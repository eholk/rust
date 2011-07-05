
#include <stdarg.h>
#include "rust_internal.h"
#include "globals.h"

rust_scheduler::rust_scheduler(rust_kernel *kernel, rust_srv *srv,
                               const char *name) :
    interrupt_flag(0),
    _log(srv, this),
    log_lvl(log_note),
    srv(srv),
    name(name),
    newborn_tasks(this, "newborn"),
    running_tasks(this, "running"),
    blocked_tasks(this, "blocked"),
    dead_tasks(this, "dead"),
    cache(this),
    root_task(NULL),
    rval(0),
    kernel(kernel)
{
    LOGPTR(this, "new dom", (uintptr_t)this);
    isaac_init(this, &rctx);
#ifndef __WIN32__
    pthread_attr_init(&attr);
    pthread_attr_setstacksize(&attr, 1024 * 1024);
    pthread_attr_setdetachstate(&attr, true);
#endif
}

rust_scheduler::~rust_scheduler() {
    DLOG(this, dom, "~rust_scheduler %s @0x%" PRIxPTR, name, (uintptr_t)this);

    I(this, ref_count == 0);

    newborn_tasks.delete_all();
    running_tasks.delete_all();
    blocked_tasks.delete_all();
    dead_tasks.delete_all();

#ifndef __WIN32__
    pthread_attr_destroy(&attr);
#endif
}

void
rust_scheduler::activate(rust_task *task) {
    context ctx;

    task->ctx.next = &ctx;
    DLOG(this, task, "descheduling...");
    task->ctx.swap(ctx);
    DLOG(this, task, "task has returned");
}

void
rust_scheduler::log(const rust_task* task, 
                    uint32_t level, char const *fmt, ...) {
    char buf[BUF_BYTES];
    va_list args;
    va_start(args, fmt);
    vsnprintf(buf, sizeof(buf), fmt, args);
    _log.trace_ln(task, level, buf);
    va_end(args);
}

void
rust_scheduler::fail() {
    log(NULL, log_err, "domain %s @0x%" PRIxPTR " root task failed",
        name, this);
    I(this, rval == 0);
    rval = 1;
}

size_t
rust_scheduler::number_of_live_tasks() {
    return running_tasks.length() + blocked_tasks.length();
}

/**
 * Delete any dead tasks.
 */
void
rust_scheduler::reap_dead_tasks(int id) {
    I(this, kernel->scheduler_lock.lock_held_by_current_thread());
    for (size_t i = 0; i < dead_tasks.length(); ) {
        rust_task *task = dead_tasks[i];
        if(task->has_messages() && task->can_schedule(id)) {
            task->running_on = id;
            kernel->scheduler_lock.unlock();
            task->drain_incoming_message_queue(true);
            kernel->scheduler_lock.lock();
            task->running_on = -1;
        }

        // Make sure this task isn't still running somewhere else...
        if (task->can_schedule(id)) {
            I(this, task->tasks_waiting_to_join.is_empty());
            dead_tasks.remove(task);
            DLOG(this, task,
                 "scheduler dropping reference to dead task %s @0x%" PRIxPTR,
                 task->name, task);
            //task->sched = NULL;
            task->deref();
            continue;
        }
        ++i;
    }
}

/**
 * Schedules a running task for execution. Only running tasks can be
 * activated.  Blocked tasks have to be unblocked before they can be
 * activated.
 *
 * Returns NULL if no tasks can be scheduled.
 */
rust_task *
rust_scheduler::schedule_task(int id) {
    I(this, this);
    // FIXME: in the face of failing tasks, this is not always right.
    // I(this, n_live_tasks() > 0);
    if (running_tasks.length() > 0) {
        size_t k = rand(&rctx);
        // Look around for a runnable task, starting at k.
        for(size_t j = 0; j < running_tasks.length(); ++j) {
            size_t  i = (j + k) % running_tasks.length();
            if (running_tasks[i]->can_schedule(id)) {
                return (rust_task *)running_tasks[i];
            }
        }
    }
    return NULL;
}

void
rust_scheduler::log_state() {
    if (log_rt_task < log_note) return;

    if (!running_tasks.is_empty()) {
        log(NULL, log_note, "running tasks:");
        for (size_t i = 0; i < running_tasks.length(); i++) {
            log(NULL, log_note, "\t task: %s @0x%" PRIxPTR " timeout: %d %s",
                running_tasks[i]->name,
                running_tasks[i],
                running_tasks[i]->yield_timer.get_timeout(),
                running_tasks[i]->has_messages() ? "(*)" : "( )");
        }
    }

    if (!blocked_tasks.is_empty()) {
        log(NULL, log_note, "blocked tasks:");
        for (size_t i = 0; i < blocked_tasks.length(); i++) {
            log(NULL, log_note, 
                "\t task: %s @0x%" PRIxPTR ", blocked on: 0x%"
                PRIxPTR " '%s' %s",
                blocked_tasks[i]->name, blocked_tasks[i],
                blocked_tasks[i]->cond, blocked_tasks[i]->cond_name,
                blocked_tasks[i]->has_messages() ? "(*)" : "( )");
        }
    }

    if (!dead_tasks.is_empty()) {
        log(NULL, log_note, "dead tasks:");
        for (size_t i = 0; i < dead_tasks.length(); i++) {
            log(NULL, log_note, "\t task: %s 0x%"PRIxPTR", ref_count: %d %s",
                dead_tasks[i]->name, dead_tasks[i],
                dead_tasks[i]->ref_count,
                dead_tasks[i]->has_messages() ? "(*)" : "( )");
        }
    }
}
/**
 * Starts the main scheduler loop which performs task scheduling for this
 * domain.
 *
 * Returns once no more tasks can be scheduled and all task ref_counts
 * drop to zero.
 */
int
rust_scheduler::start_main_loop(int id) {
    kernel->scheduler_lock.lock();

    // Make sure someone is watching, to pull us out of infinite loops.
    //
    // FIXME: time-based interruption is not presently working; worked
    // in rustboot and has been completely broken in rustc.
    //
    // rust_timer timer(this);

    DLOG(this, dom, "started domain loop %d", id);

    while (number_of_live_tasks() > 0) {
        A(this, kernel->is_deadlocked() == false, "deadlock");

        DLOG(this, dom, "worker %d, number_of_live_tasks = %d",
             id, number_of_live_tasks());

        // Check if any blocked tasks have messages
        for(size_t i = 0; i < blocked_tasks.length(); ++i) {
            if(blocked_tasks[i]->has_messages()) {
                printf("draining messages on %p\n", blocked_tasks[i]);
                rust_task *task = blocked_tasks[i];
                task->running_on = id;
                kernel->scheduler_lock.unlock();
                task->drain_incoming_message_queue(true);
                kernel->scheduler_lock.lock();
                task->running_on = -1;
            }
        }

        rust_task *scheduled_task = schedule_task(id);

        // The scheduler busy waits until a task is available for scheduling.
        // Eventually we'll want a smarter way to do this, perhaps sleep
        // for a minimum amount of time.

        if (scheduled_task == NULL) {
            log_state();
            DLOG(this, task,
                 "all tasks are blocked, scheduler id %d yielding ...",
                 id);
            kernel->scheduler_lock.unlock();
            // FIXME: properly sleep until more tasks are ready to run.
            abort();
            sync::sleep(100);
            kernel->scheduler_lock.lock();
            DLOG(this, task,
                "scheduler resuming ...");
            continue;
        }

        I(this, scheduled_task->running());

        DLOG(this, task,
            "activating task %s 0x%" PRIxPTR
            ", sp=0x%" PRIxPTR
            ", ref_count=%d"
            ", state: %s",
            scheduled_task->name,
            (uintptr_t)scheduled_task,
            scheduled_task->rust_sp,
            scheduled_task->ref_count,
            scheduled_task->state->name);

        interrupt_flag = 0;

        DLOG(this, task,
             "Running task %p on worker %d",
             scheduled_task, id);
        scheduled_task->running_on = id;
        kernel->scheduler_lock.unlock();
        scheduled_task->drain_incoming_message_queue(true);
        activate(scheduled_task);
        kernel->scheduler_lock.lock();
        scheduled_task->running_on = -1;

        DLOG(this, task,
             "returned from task %s @0x%" PRIxPTR
             " in state '%s', sp=0x%x, worker id=%d",
             scheduled_task->name,
             (uintptr_t)scheduled_task,
             scheduled_task->state->name,
             scheduled_task->rust_sp,
             id);

        reap_dead_tasks(id);
    }

    DLOG(this, dom,
         "terminated scheduler loop, reaping dead tasks ...");

    while (dead_tasks.length() > 0) {
        DLOG(this, dom,
             "waiting for %d dead tasks to become dereferenced, "
             "scheduler yielding ...",
             dead_tasks.length());
        log_state();
        kernel->scheduler_lock.unlock();
        sync::yield();
        kernel->scheduler_lock.lock();

#if 0
        if (message_queue->is_empty()) {
            DLOG(this, dom,
                "waiting for %d dead tasks to become dereferenced, "
                "scheduler yielding ...",
                dead_tasks.length());
            log_state();
            kernel->scheduler_lock.unlock();
            sync::yield();
            kernel->scheduler_lock.lock();
        } else {
            kernel->scheduler_lock.unlock();
            drain_incoming_message_queue(true);
            kernel->scheduler_lock.lock();
        }
#endif

        reap_dead_tasks(id);
    }

    DLOG(this, dom, "finished main-loop %d (dom.rval = %d)", id, rval);

    kernel->scheduler_lock.unlock();
    return rval;
}

rust_crate_cache *
rust_scheduler::get_cache() {
    return &cache;
}

//
// Local Variables:
// mode: C++
// fill-column: 70;
// indent-tabs-mode: nil
// c-basic-offset: 4
// buffer-file-coding-system: utf-8-unix
// compile-command: "make -k -C .. 2>&1 | sed -e 's/\\/x\\//x:\\//g'";
// End:
//
