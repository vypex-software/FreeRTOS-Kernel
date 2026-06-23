/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2020 Cambridge Consultants Ltd.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/*-----------------------------------------------------------
* Implementation of functions defined in portable.h for the Posix port.
*
* Each task has a pthread which eases use of standard debuggers
* (allowing backtraces of tasks etc). Threads for tasks that are not
* running are blocked in sigwait().
*
* Task switch is done by resuming the thread for the next task by
* signaling the condition variable and then waiting on a condition variable
* with the current thread.
*
* The timer interrupt uses SIGALRM and care is taken to ensure that
* the signal handler runs only on the thread for the current task.
*
* Use of part of the standard C library requires care as some
* functions can take pthread mutexes internally which can result in
* deadlocks as the FreeRTOS kernel can switch tasks while they're
* holding a pthread mutex.
*
* stdio (printf() and friends) should be called from a single task
* only or serialized with a FreeRTOS primitive such as a binary
* semaphore or mutex.
* 
* Note: When using LLDB (the default debugger on macOS) with this port, 
* suppress SIGUSR1 to prevent debugger interference. This can be
* done by adding the following line to ~/.lldbinit:
* `process handle SIGUSR1 -n true -p false -s false`
*----------------------------------------------------------*/
#ifdef __linux__
    #define _GNU_SOURCE
#endif
#include "portmacro.h"
#include <errno.h>
#include <pthread.h>
#include <limits.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <sys/times.h>
#include <time.h>
#include <unistd.h>
#include <semaphore.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "utils/wait_for_event.h"
/*-----------------------------------------------------------*/

#define SIG_RESUME    SIGUSR1

typedef struct THREAD
{
    pthread_t pthread;
    TaskFunction_t pxCode;
    void * pvParams;
    BaseType_t xDying;
    struct event * ev;
} Thread_t;

/*
 * The additional per-thread data is stored at the beginning of the
 * task's stack.
 */
static inline Thread_t * prvGetThreadFromTask( TaskHandle_t xTask )
{
    StackType_t * pxTopOfStack = *( StackType_t ** ) xTask;

    return ( Thread_t * ) ( pxTopOfStack + 1 );
}

/*-----------------------------------------------------------*/

static pthread_once_t hSigSetupThread = PTHREAD_ONCE_INIT;
static pthread_once_t hThreadKeyOnce = PTHREAD_ONCE_INIT;
static sigset_t xAllSignals;
static sigset_t xSchedulerOriginalSignalMask;
static pthread_t hMainThread = ( pthread_t ) NULL;
static volatile BaseType_t uxCriticalNesting;
static BaseType_t xSchedulerEnd = pdFALSE;
static pthread_t hTimerTickThread;
static bool xTimerTickThreadShouldRun;
static uint64_t prvStartTimeNs;
static pthread_key_t xThreadKey = 0;
static timer_t xPosixTimer;
static sem_t xTimerSemaphore;

/*
 * Vypex integration-test port modifications (this is the vypex-software fork of
 * the FreeRTOS POSIX port). Two changes live here, previously applied as a
 * configure-time string patch from integration-tests/CMakeLists.txt:
 *
 * 1. Cross-thread kernel lock (xRppKernelLock). The upstream port's critical
 *    section and interrupt-mask primitives only mask signals on the *calling*
 *    thread, which gives no mutual exclusion against other host threads. The
 *    fakes simulate ISRs by calling xTaskNotifyFromISR() from rpp new_thread
 *    workers, so those calls race the scheduler's list manipulation. The window
 *    is normally tiny, but tickless idle keeps the idle thread in
 *    xTaskResumeAll() far longer, turning the latent race into a reliable
 *    SIGSEGV. A shared recursive mutex serialises "ISR" code and the scheduler,
 *    mirroring the model the MSVC-MingW simulator port uses: one global mutex
 *    held during critical sections and fake-ISR code, released around the point
 *    a thread blocks (so the resumed thread / a pending ISR can run) and
 *    reacquired on wake. xRppLockDepth is per-thread (__thread) so the
 *    release/reacquire count is correct regardless of the global
 *    uxCriticalNesting (which is shared across host threads).
 *
 * 2. Tick speed-up (TESTS_BOOST_FACTOR). Dividing the tick interval by N makes
 *    FreeRTOS advance N ticks per real ms, so e.g. a 20 s vTaskDelay finishes in
 *    4 s wall clock at N=5. Composes with tickless idle.
 */
#ifndef TESTS_BOOST_FACTOR
    #define TESTS_BOOST_FACTOR    1
#endif

static pthread_mutex_t xRppKernelLock = PTHREAD_RECURSIVE_MUTEX_INITIALIZER_NP;
static __thread int xRppLockDepth = 0;

/* Saved signal mask + nesting depth for the fake-ISR interrupt-mask region
 * (xPortSetInterruptMask / vPortClearInterruptMask). Per-thread; depth-tracked
 * so nested FromISR masks restore the prior mask exactly once. */
static __thread sigset_t xIsrSavedSignalMask;
static __thread int xIsrMaskDepth = 0;

static void prvRppLock( void )
{
    pthread_mutex_lock( &xRppKernelLock );
    xRppLockDepth++;
}

static void prvRppUnlock( void )
{
    xRppLockDepth--;
    pthread_mutex_unlock( &xRppKernelLock );
}

/*
 * Release every level of xRppKernelLock this thread currently holds. Used both
 * on the cooperative dying path (prvSwitchThread) and as a pthread cancellation
 * cleanup handler (prvWaitForStart): a task deleted via vPortCancelThread is
 * torn down with pthread_cancel(), which does not run the cooperative drain, so
 * without this a thread cancelled while owning the lock would orphan the
 * recursive mutex and wedge every later acquirer (e.g. the tick handler).
 */
static void prvRppDrainLock( void )
{
    while( xRppLockDepth > 0 )
    {
        xRppLockDepth--;
        pthread_mutex_unlock( &xRppKernelLock );
    }
}

static void prvRppDrainLockCleanup( void * pvUnused )
{
    ( void ) pvUnused;
    prvRppDrainLock();
}

/*
 * Returns non-zero if the current SIGALRM tick must be deferred because this
 * thread is inside a guarded region - holding a non-async-signal-safe resource
 * (the glibc malloc arena lock, or any std::mutex/pthread_mutex) that the tick
 * handler's dispatch / context switch would re-enter or strand. Strongly defined
 * by the integration-test tick guard (tick_guard.cpp), which re-raises SIGALRM
 * once the last such resource is released. Weak default here so the port still
 * links (and behaves as upstream) when the guard is not present.
 */
__attribute__( ( weak ) ) int rppTickGuardDeferTick( void )
{
    return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupSignalsAndSchedulerPolicy( void );
static void prvSetupTimerInterrupt( void );
static void * prvWaitForStart( void * pvParams );
static void prvSwitchThread( Thread_t * xThreadToResume,
                             Thread_t * xThreadToSuspend );
static void prvSuspendSelf( Thread_t * thread );
static void prvResumeThread( Thread_t * xThreadId );
static void vPortSystemTickHandler( int sig );
static void vPortStartFirstTask( void );
static void prvPortYieldFromISR( void );
static void prvThreadKeyDestructor( void * pvData );
static void prvInitThreadKey( void );
static void prvMarkAsFreeRTOSThread( void );
static BaseType_t prvIsFreeRTOSThread( void );
static void prvDestroyThreadKey( void );
/*-----------------------------------------------------------*/

static void prvThreadKeyDestructor( void * pvData )
{
    free( pvData );
}
/*-----------------------------------------------------------*/

static void prvInitThreadKey( void )
{
    pthread_key_create( &xThreadKey, prvThreadKeyDestructor );
}
/*-----------------------------------------------------------*/

static void prvMarkAsFreeRTOSThread( void )
{
    uint8_t * pucThreadData = NULL;

    ( void ) pthread_once( &hThreadKeyOnce, prvInitThreadKey );

    pucThreadData = malloc( 1 );
    configASSERT( pucThreadData != NULL );

    *pucThreadData = 1;

    pthread_setspecific( xThreadKey, pucThreadData );
}
/*-----------------------------------------------------------*/

static BaseType_t prvIsFreeRTOSThread( void )
{
    uint8_t * pucThreadData = NULL;
    BaseType_t xRet = pdFALSE;

    ( void ) pthread_once( &hThreadKeyOnce, prvInitThreadKey );

    pucThreadData = ( uint8_t * ) pthread_getspecific( xThreadKey );

    if( ( pucThreadData != NULL ) && ( *pucThreadData == 1 ) )
    {
        xRet = pdTRUE;
    }

    return xRet;
}
/*-----------------------------------------------------------*/

static void prvDestroyThreadKey( void )
{
    pthread_key_delete( xThreadKey );
}
/*-----------------------------------------------------------*/

static void prvFatalError( const char * pcCall,
                           int iErrno ) __attribute__( ( __noreturn__ ) );

void prvFatalError( const char * pcCall,
                    int iErrno )
{
    fprintf( stderr, "%s: %s\n", pcCall, strerror( iErrno ) );
    abort();
}
/*-----------------------------------------------------------*/

static void prvPortSetCurrentThreadName( char * pxThreadName )
{
    #ifdef __APPLE__
        pthread_setname_np( pxThreadName );
    #else
        pthread_setname_np( pthread_self(), pxThreadName );
    #endif
}
/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     StackType_t * pxEndOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters )
{
    Thread_t * thread;
    pthread_attr_t xThreadAttributes;
    size_t ulStackSize;
    int iRet;

    ( void ) pthread_once( &hSigSetupThread, prvSetupSignalsAndSchedulerPolicy );

    /*
     * Store the additional thread data at the start of the stack.
     */
    thread = ( Thread_t * ) ( pxTopOfStack + 1 ) - 1;
    pxTopOfStack = ( StackType_t * ) thread - 1;

    /* Ensure that there is enough space to store Thread_t on the stack. */
    ulStackSize = ( size_t ) ( pxTopOfStack + 1 - pxEndOfStack ) * sizeof( *pxTopOfStack );
    configASSERT( ulStackSize > sizeof( Thread_t ) );

    thread->pxCode = pxCode;
    thread->pvParams = pvParameters;
    thread->xDying = pdFALSE;

    pthread_attr_init( &xThreadAttributes );

    thread->ev = event_create();

    vPortEnterCritical();

    iRet = pthread_create( &thread->pthread, &xThreadAttributes,
                           prvWaitForStart, thread );

    if( iRet != 0 )
    {
        prvFatalError( "pthread_create", iRet );
    }

    vPortExitCritical();

    return pxTopOfStack;
}
/*-----------------------------------------------------------*/

void vPortStartFirstTask( void )
{
    Thread_t * pxFirstThread = prvGetThreadFromTask( xTaskGetCurrentTaskHandle() );

    /* Start the first task. */
    prvResumeThread( pxFirstThread );
}
/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
BaseType_t xPortStartScheduler( void )
{
    int iSignal;
    sigset_t xSignals;

    hMainThread = pthread_self();
    prvPortSetCurrentThreadName( "Scheduler" );

    /* Start the timer that generates the tick ISR(SIGALRM).
     * Interrupts are disabled here already. */
    prvSetupTimerInterrupt();

    /*
     * Block SIG_RESUME before starting any tasks so the main thread can sigwait on it.
     * To sigwait on an unblocked signal is undefined.
     * https://pubs.opengroup.org/onlinepubs/009604499/functions/sigwait.html
     */
    sigemptyset( &xSignals );
    sigaddset( &xSignals, SIG_RESUME );
    ( void ) pthread_sigmask( SIG_BLOCK, &xSignals, NULL );

    /* Start the first task. */
    vPortStartFirstTask();

    /* Wait until signaled by vPortEndScheduler(). */
    while( xSchedulerEnd != pdTRUE )
    {
        sigwait( &xSignals, &iSignal );
    }

    /*
     * clear out the variable that is used to end the scheduler, otherwise
     * subsequent scheduler restarts will end immediately.
     */
    xSchedulerEnd = pdFALSE;

    /* Reset pthread_once_t, needed to restart the scheduler again.
     * memset the internal struct members for MacOS/Linux Compatibility */
    #if __APPLE__
        hSigSetupThread.__sig = _PTHREAD_ONCE_SIG_init;
        hThreadKeyOnce.__sig = _PTHREAD_ONCE_SIG_init;
        memset( ( void * ) &hSigSetupThread.__opaque, 0, sizeof( hSigSetupThread.__opaque ) );
        memset( ( void * ) &hThreadKeyOnce.__opaque, 0, sizeof( hThreadKeyOnce.__opaque ) );
    #else /* Linux PTHREAD library*/
        hSigSetupThread = ( pthread_once_t ) PTHREAD_ONCE_INIT;
        hThreadKeyOnce = ( pthread_once_t ) PTHREAD_ONCE_INIT;
    #endif /* __APPLE__*/

    /* Restore original signal mask. */
    ( void ) pthread_sigmask( SIG_SETMASK, &xSchedulerOriginalSignalMask, NULL );

    prvDestroyThreadKey();

    return 0;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
    Thread_t * pxCurrentThread;

    /* Stop the timer tick thread. */
    xTimerTickThreadShouldRun = false;
    
    /* Delete the POSIX timer */
    timer_delete( xPosixTimer );
    
    /* Signal the timer thread to wake up and exit */
    sem_post( &xTimerSemaphore );
    pthread_join( hTimerTickThread, NULL );
    
    /* Cleanup semaphore */
    sem_destroy( &xTimerSemaphore );

    /* Signal the scheduler to exit its loop. */
    xSchedulerEnd = pdTRUE;
    ( void ) pthread_kill( hMainThread, SIG_RESUME );

    /* Waiting to be deleted here. */
    if( prvIsFreeRTOSThread() == pdTRUE )
    {
        pxCurrentThread = prvGetThreadFromTask( xTaskGetCurrentTaskHandle() );
        event_wait( pxCurrentThread->ev );
    }

    pthread_testcancel();
}
/*-----------------------------------------------------------*/

void vPortEnterCritical( void )
{
    if( uxCriticalNesting == 0 )
    {
        vPortDisableInterrupts();
    }

    prvRppLock();
    uxCriticalNesting++;
}
/*-----------------------------------------------------------*/

void vPortExitCritical( void )
{
    uxCriticalNesting--;

    prvRppUnlock();

    /* If we have reached 0 then re-enable the interrupts. */
    if( uxCriticalNesting == 0 )
    {
        vPortEnableInterrupts();
    }
}
/*-----------------------------------------------------------*/

static void prvPortYieldFromISR( void )
{
    Thread_t * xThreadToSuspend;
    Thread_t * xThreadToResume;

    xThreadToSuspend = prvGetThreadFromTask( xTaskGetCurrentTaskHandle() );

    vTaskSwitchContext();

    xThreadToResume = prvGetThreadFromTask( xTaskGetCurrentTaskHandle() );

    prvSwitchThread( xThreadToResume, xThreadToSuspend );
}
/*-----------------------------------------------------------*/

void vPortYield( void )
{
    /* This must never be called from outside of a FreeRTOS-owned thread, or
     * the thread could get stuck in a suspended state. */
    configASSERT( prvIsFreeRTOSThread() == pdTRUE );

    vPortEnterCritical();

    prvPortYieldFromISR();

    vPortExitCritical();
}
/*-----------------------------------------------------------*/

void vPortDisableInterrupts( void )
{
    if( prvIsFreeRTOSThread() == pdTRUE )
    {
        pthread_sigmask( SIG_BLOCK, &xAllSignals, NULL );
    }
}
/*-----------------------------------------------------------*/

void vPortEnableInterrupts( void )
{
    if( prvIsFreeRTOSThread() == pdTRUE )
    {
        pthread_sigmask( SIG_UNBLOCK, &xAllSignals, NULL );
    }
}
/*-----------------------------------------------------------*/

UBaseType_t xPortSetInterruptMask( void )
{
    /* Mask the tick (SIGALRM) for this interrupt-masked region *before* taking
     * the kernel lock, then serialise fake-ISR code (xTaskNotifyFromISR from rpp
     * worker threads) against the scheduler via the shared recursive lock.
     *
     * Masking first is essential: pthread_mutex_lock is not async-signal-safe,
     * so if SIGALRM lands mid-acquisition (before ownership is recorded), the
     * tick handler's own prvRppLock re-enters pthread_mutex_lock on the
     * half-acquired recursive mutex and self-deadlocks. It also keeps the
     * fake-ISR section atomic w.r.t. the tick (no context switch mid-section).
     * Mirrors vPortEnterCritical, which disables interrupts before locking.
     * Depth-tracked save/restore so nested masks behave. */
    if( xIsrMaskDepth++ == 0 )
    {
        pthread_sigmask( SIG_BLOCK, &xAllSignals, &xIsrSavedSignalMask );
    }

    prvRppLock();
    return ( UBaseType_t ) 0;
}
/*-----------------------------------------------------------*/

void vPortClearInterruptMask( UBaseType_t uxMask )
{
    ( void ) uxMask;
    /* Release the kernel lock while the tick is still masked (so the unlock is
     * itself uninterruptible), then restore the prior signal mask at the
     * outermost nesting level. */
    prvRppUnlock();

    if( --xIsrMaskDepth == 0 )
    {
        pthread_sigmask( SIG_SETMASK, &xIsrSavedSignalMask, NULL );
    }
}
/*-----------------------------------------------------------*/

static uint64_t prvGetTimeNs( void )
{
    struct timespec t;

    clock_gettime( CLOCK_MONOTONIC, &t );

    return ( uint64_t ) t.tv_sec * ( uint64_t ) 1000000000UL + ( uint64_t ) t.tv_nsec;
}
/*-----------------------------------------------------------*/

/* commented as part of the code below in vPortSystemTickHandler,
 * to adjust timing according to full demo requirements */
/* static uint64_t prvTickCount; */

static void prvTimerCallback( union sigval sv )
{
    ( void ) sv;
    /* Signal the timer thread that a tick occurred */
    sem_post( &xTimerSemaphore );
}

static void * prvTimerTickHandler( void * arg )
{
    ( void ) arg;

    prvMarkAsFreeRTOSThread();
    prvPortSetCurrentThreadName( "Scheduler timer" );

    while( xTimerTickThreadShouldRun )
    {
        /* Wait for timer signal */
        sem_wait( &xTimerSemaphore );
        
        if( !xTimerTickThreadShouldRun )
        {
            break;
        }

        /*
         * signal to the active task to cause tick handling or
         * preemption (if enabled)
         */
        Thread_t * thread = prvGetThreadFromTask( xTaskGetCurrentTaskHandle() );
        pthread_kill( thread->pthread, SIGALRM );
    }

    return NULL;
}

/*
 * Setup the systick timer to generate the tick interrupts at the required
 * frequency.
 */
void prvSetupTimerInterrupt( void )
{
    struct sigevent sev;
    struct itimerspec its;
    int iRet;

    /* Initialize semaphore for timer synchronization */
    sem_init( &xTimerSemaphore, 0, 0 );

    /* Start the timer thread */
    xTimerTickThreadShouldRun = true;
    pthread_create( &hTimerTickThread, NULL, prvTimerTickHandler, NULL );

    /* Create the timer with thread callback (no signals) */
    sev.sigev_notify = SIGEV_THREAD;
    sev.sigev_notify_function = prvTimerCallback;
    sev.sigev_notify_attributes = NULL;
    sev.sigev_value.sival_ptr = NULL;

    iRet = timer_create( CLOCK_MONOTONIC, &sev, &xPosixTimer );
    if( iRet == -1 )
    {
        prvFatalError( "timer_create", errno );
    }

    /* Configure timer period */
    its.it_value.tv_sec = 0;
    its.it_value.tv_nsec = (portTICK_RATE_MICROSECONDS * 1000UL / TESTS_BOOST_FACTOR);
    its.it_interval.tv_sec = 0;
    its.it_interval.tv_nsec = (portTICK_RATE_MICROSECONDS * 1000UL / TESTS_BOOST_FACTOR);

    /* Start the timer */
    iRet = timer_settime( xPosixTimer, 0, &its, NULL );
    if( iRet == -1 )
    {
        prvFatalError( "timer_settime", errno );
    }

    prvStartTimeNs = prvGetTimeNs();
}
/*-----------------------------------------------------------*/

static void vPortSystemTickHandler( int sig )
{
    if( prvIsFreeRTOSThread() == pdTRUE )
    {
        Thread_t * pxThreadToSuspend;
        Thread_t * pxThreadToResume;

        ( void ) sig;

        /* If this tick interrupted a guarded region on the current thread - i.e.
         * the thread holds a non-async-signal-safe resource (the malloc arena
         * lock, or an RPP/std::mutex) - running the tick now would deadlock:
         * on_tick_hook re-enters the held lock, and the context switch would
         * suspend the holder while another task blocks on it. So defer the whole
         * tick; the guard re-raises SIGALRM the instant the last such resource is
         * released. No tick is lost (re-raised) and no time drift
         * (xTaskIncrementTick runs once, on the re-raised handler). */
        if( rppTickGuardDeferTick() != 0 )
        {
            return;
        }

        prvRppLock();
        uxCriticalNesting++; /* Signals are blocked in this signal handler. */

        pxThreadToSuspend = prvGetThreadFromTask( xTaskGetCurrentTaskHandle() );

        if( xTaskIncrementTick() != pdFALSE )
        {
            /* Select Next Task. */
            vTaskSwitchContext();

            pxThreadToResume = prvGetThreadFromTask( xTaskGetCurrentTaskHandle() );

            prvSwitchThread( pxThreadToResume, pxThreadToSuspend );
        }

        uxCriticalNesting--;
        prvRppUnlock();
    }
    else
    {
        fprintf( stderr, "vPortSystemTickHandler called from non-FreeRTOS thread\n" );
    }
}
/*-----------------------------------------------------------*/

void vPortThreadDying( void * pxTaskToDelete,
                       volatile BaseType_t * pxPendYield )
{
    Thread_t * pxThread = prvGetThreadFromTask( pxTaskToDelete );

    ( void ) pxPendYield;

    pxThread->xDying = pdTRUE;
}
/*-----------------------------------------------------------*/

void vPortCancelThread( void * pxTaskToDelete )
{
    Thread_t * pxThreadToCancel = prvGetThreadFromTask( pxTaskToDelete );
    sigset_t xPrevMask;

    /*
     * Block the tick (all signals) on the calling thread for the cancel + join.
     * vPortCancelThread runs outside a critical section, so a SIGALRM landing
     * here would run vPortSystemTickHandler -> prvRppLock(); if the thread being
     * torn down still owns xRppKernelLock at the instant it is cancelled, that
     * acquisition blocks forever and the whole process wedges at shutdown
     * (observed as intermittent 300 s integration-test timeouts). The cancelled
     * thread itself releases any lock it holds via the prvRppDrainLockCleanup
     * cancellation handler installed in prvWaitForStart.
     */
    ( void ) pthread_sigmask( SIG_BLOCK, &xAllSignals, &xPrevMask );

    pthread_cancel( pxThreadToCancel->pthread );
    event_signal( pxThreadToCancel->ev );
    pthread_join( pxThreadToCancel->pthread, NULL );
    event_delete( pxThreadToCancel->ev );

    ( void ) pthread_sigmask( SIG_SETMASK, &xPrevMask, NULL );
}
/*-----------------------------------------------------------*/

static void * prvWaitForStart( void * pvParams )
{
    Thread_t * pxThread = pvParams;

    prvMarkAsFreeRTOSThread();

    /* Release any xRppKernelLock levels this thread holds if it is torn down via
     * pthread_cancel (vPortCancelThread). pthread_cancel does not run the
     * cooperative dying drain in prvSwitchThread, so without this handler a task
     * cancelled while owning the lock would orphan the recursive mutex. Runs on
     * both pthread_cancel and pthread_exit unwinding. */
    pthread_cleanup_push( prvRppDrainLockCleanup, NULL );

    prvSuspendSelf( pxThread );

    /* Resumed for the first time, unblocks all signals. */
    uxCriticalNesting = 0;
    vPortEnableInterrupts();

    /* Set thread name */
    prvPortSetCurrentThreadName( pcTaskGetName( xTaskGetCurrentTaskHandle() ) );

    /* Call the task's entry point. */
    pxThread->pxCode( pxThread->pvParams );

    /* A function that implements a task must not exit or attempt to return to
     * its caller as there is nothing to return to. If a task wants to exit it
     * should instead call vTaskDelete( NULL ). Artificially force an assert()
     * to be triggered if configASSERT() is defined, so application writers can
     * catch the error. */
    configASSERT( pdFALSE );

    pthread_cleanup_pop( 0 );

    return NULL;
}
/*-----------------------------------------------------------*/

static void prvSwitchThread( Thread_t * pxThreadToResume,
                             Thread_t * pxThreadToSuspend )
{
    BaseType_t uxSavedCriticalNesting;

    if( pxThreadToSuspend != pxThreadToResume )
    {
        /*
         * Switch tasks.
         *
         * The critical section nesting is per-task, so save it on the
         * stack of the current (suspending thread), restoring it when
         * we switch back to this task.
         */
        uxSavedCriticalNesting = uxCriticalNesting;

        prvResumeThread( pxThreadToResume );

        if( pxThreadToSuspend->xDying == pdTRUE )
        {
            prvRppDrainLock();
            pthread_exit( NULL );
        }

        prvSuspendSelf( pxThreadToSuspend );

        uxCriticalNesting = uxSavedCriticalNesting;
    }
}
/*-----------------------------------------------------------*/

static void prvSuspendSelf( Thread_t * thread )
{
    /*
     * Suspend this thread by waiting for a pthread_cond_signal event.
     *
     * A suspended thread must not handle signals (interrupts) so
     * all signals must be blocked by calling this from:
     *
     * - Inside a critical section (vPortEnterCritical() /
     *   vPortExitCritical()).
     *
     * - From a signal handler that has all signals masked.
     *
     * - A thread with all signals blocked with pthread_sigmask().
     */
    {
        int xResumeDepth = xRppLockDepth;
        int xLevel;

        /* Drop the kernel lock while blocked so the resumed thread / a pending
         * fake-ISR can run, then reacquire to the same depth on wake. */
        for( xLevel = 0; xLevel < xResumeDepth; xLevel++ )
        {
            pthread_mutex_unlock( &xRppKernelLock );
        }
        xRppLockDepth = 0;

        event_wait( thread->ev );

        for( xLevel = 0; xLevel < xResumeDepth; xLevel++ )
        {
            pthread_mutex_lock( &xRppKernelLock );
        }
        xRppLockDepth = xResumeDepth;
    }
    pthread_testcancel();
}

/*-----------------------------------------------------------*/

static void prvResumeThread( Thread_t * xThreadId )
{
    if( pthread_self() != xThreadId->pthread )
    {
        event_signal( xThreadId->ev );
    }
}
/*-----------------------------------------------------------*/

static void prvSetupSignalsAndSchedulerPolicy( void )
{
    struct sigaction sigtick;
    int iRet;

    hMainThread = pthread_self();

    /* Initialise common signal masks. */
    sigfillset( &xAllSignals );

    /* Don't block SIGINT so this can be used to break into GDB while
     * in a critical section. */
    sigdelset( &xAllSignals, SIGINT );

    /*
     * Block all signals in this thread so all new threads
     * inherits this mask.
     *
     * When a thread is resumed for the first time, all signals
     * will be unblocked.
     */
    ( void ) pthread_sigmask( SIG_SETMASK,
                              &xAllSignals,
                              &xSchedulerOriginalSignalMask );

    sigtick.sa_flags = 0;
    sigtick.sa_handler = vPortSystemTickHandler;
    sigfillset( &sigtick.sa_mask );

    iRet = sigaction( SIGALRM, &sigtick, NULL );

    if( iRet == -1 )
    {
        prvFatalError( "sigaction", errno );
    }
}
/*-----------------------------------------------------------*/

uint32_t ulPortGetRunTime( void )
{
    struct tms xTimes;

    times( &xTimes );

    return ( uint32_t ) xTimes.tms_utime;
}
/*-----------------------------------------------------------*/
