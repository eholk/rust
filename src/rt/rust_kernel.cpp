#include "rust_internal.h"

#define KLOG(...)                                          \
  do {                                                     \
      if (log_rt_kern >= log_note) {                       \
          log(log_note, __VA_ARGS__);                      \
      }                                                    \
  } while (0)

rust_kernel::rust_kernel(rust_srv *srv) :
    _region(&srv->local_region),
    _log(srv, NULL),
    _srv(srv),
    _interrupt_kernel_loop(FALSE) 
{
    create_scheduler("main");
}

void
rust_kernel::create_scheduler(const char *name) {
    rust_srv *srv = _srv->clone();
    sched = new (this) rust_scheduler(this, srv, name);
    sched->root_task = create_task(NULL, name);
    KLOG("created scheduler: " PTR ", name: %s, index: %d",
         sched, name, sched->list_index);
}

void
rust_kernel::destroy_scheduler() {
    _kernel_lock.lock();
    KLOG("deleting scheduler: " PTR ", name: %s, index: %d",
        sched, sched->name, sched->list_index);
    rust_srv *srv = sched->srv;
    delete sched;
    delete srv;
    _kernel_lock.signal_all();
    _kernel_lock.unlock();
}

rust_handle<rust_task> *
rust_kernel::internal_get_task_handle(rust_task *task) {
    rust_handle<rust_task> *handle = NULL;
    if (_task_handles.get(task, &handle) == false) {
        handle =
            new (this) rust_handle<rust_task>(this,
                                              task->message_queue,
                                              task);
        _task_handles.put(task, handle);
    }
    return handle;
}

rust_handle<rust_task> *
rust_kernel::get_task_handle(rust_task *task) {
    scoped_lock with(_kernel_lock);
    return internal_get_task_handle(task);
}

rust_handle<rust_port> *
rust_kernel::get_port_handle(rust_port *port) {
    _kernel_lock.lock();
    rust_handle<rust_port> *handle = NULL;
    if (_port_handles.get(port, &handle) == false) {
        handle = new (this)
            rust_handle<rust_port>(this,
                                   port->task->message_queue,
                                   port);
        _port_handles.put(port, handle);
    }
    _kernel_lock.unlock();
    return handle;
}

void
rust_kernel::log_all_scheduler_state() {
    sched->log_state();
}

/**
 * Checks for simple deadlocks.
 */
bool
rust_kernel::is_deadlocked() {
    return false;
}

void
rust_kernel::log(uint32_t level, char const *fmt, ...) {
    char buf[BUF_BYTES];
    va_list args;
    va_start(args, fmt);
    vsnprintf(buf, sizeof(buf), fmt, args);
    _log.trace_ln(NULL, level, buf);
    va_end(args);
}

void
rust_kernel::pump_message_queues() {
    for (size_t i = 0; i < message_queues.length(); i++) {
        rust_message_queue *queue = message_queues[i];
        if (queue->is_associated() == false) {
            rust_message *message = NULL;
            while (queue->dequeue(&message)) {
                message->kernel_process();
                delete message;
            }
        }
    }
}

void
rust_kernel::start_kernel_loop() {
    _kernel_lock.lock();
    while (_interrupt_kernel_loop == false) {
        _kernel_lock.wait();
        pump_message_queues();
    }
    _kernel_lock.unlock();
}

void
rust_kernel::run() {
    KLOG("started kernel loop");
    start_kernel_loop();
    KLOG("finished kernel loop");
}

void
rust_kernel::terminate_kernel_loop() {
    KLOG("terminating kernel loop");
    _interrupt_kernel_loop = true;
    signal_kernel_lock();
    join();
}

rust_kernel::~rust_kernel() {
    destroy_scheduler();

    terminate_kernel_loop();

    // It's possible that the message pump misses some messages because
    // of races, so pump any remaining messages here. By now all domain
    // threads should have been joined, so we shouldn't miss any more
    // messages.
    pump_message_queues();

    KLOG("freeing handles");

    free_handles(_task_handles);
    KLOG("..task handles freed");
    free_handles(_port_handles);
    KLOG("..port handles freed");
    free_handles(_sched_handles);
    KLOG("..sched handles freed");

    KLOG("freeing queues");

    rust_message_queue *queue = NULL;
    while (message_queues.pop(&queue)) {
        K(_srv, queue->is_empty(), "Kernel message queue should be empty "
          "before killing the kernel.");
        delete queue;
    }
}

void *
rust_kernel::malloc(size_t size) {
    return _region->malloc(size);
}

void rust_kernel::free(void *mem) {
    _region->free(mem);
}

template<class T> void
rust_kernel::free_handles(hash_map<T*, rust_handle<T>* > &map) {
    T* key;
    rust_handle<T> *value;
    while (map.pop(&key, &value)) {
        KLOG("...freeing " PTR, value);
        delete value;
    }
}

void
rust_kernel::notify_message_enqueued(rust_message_queue *queue,
                                     rust_message *message) {
    // The message pump needs to handle this message if the queue is not
    // associated with a domain, therefore signal the message pump.
    if (queue->is_associated() == false) {
        signal_kernel_lock();
    }
}

void
rust_kernel::signal_kernel_lock() {
    _kernel_lock.lock();
    _kernel_lock.signal_all();
    _kernel_lock.unlock();
}

int rust_kernel::start_task_threads(int num_threads)
{
    rust_task_thread *thread = NULL;
    
    // -1, because this thread will also be a thread.
    for(int i = 0; i < num_threads - 1; ++i) {
        thread = new rust_task_thread(i + 1, this);
        thread->start();
        threads.push(thread);
    }
    
    sched->start_main_loop(0);

    while(threads.pop(&thread)) {
        thread->join();
        delete thread;
    }

    return sched->rval;
}

rust_task *
rust_kernel::create_task(rust_task *spawner, const char *name) {
    rust_message_queue *message_queue =
        new (this) rust_message_queue(_srv, this);

    rust_task *task =
        new (this) rust_task (this->sched, &sched->newborn_tasks, spawner, 
                              name, message_queue);

    rust_handle<rust_task> *handle = get_task_handle(task);
    message_queue->associate(handle);
    message_queues.append(message_queue);
    
    DLOG(this->sched, task, "created task: " PTR ", spawner: %s, name: %s",
         task, spawner ? spawner->name : "null", name);
    if(spawner)
        task->pin(spawner->pinned_on);
    sched->newborn_tasks.append(task);
    return task;
}

#ifdef __WIN32__
void
rust_kernel::win32_require(LPCTSTR fn, BOOL ok) {
    if (!ok) {
        LPTSTR buf;
        DWORD err = GetLastError();
        FormatMessage(FORMAT_MESSAGE_ALLOCATE_BUFFER |
                      FORMAT_MESSAGE_FROM_SYSTEM |
                      FORMAT_MESSAGE_IGNORE_INSERTS,
                      NULL, err,
                      MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT),
                      (LPTSTR) &buf, 0, NULL );
        DLOG_ERR(sched, dom, "%s failed with error %ld: %s", fn, err, buf);
        LocalFree((HLOCAL)buf);
        I(sched, ok);
    }
}
#endif

rust_task_thread::rust_task_thread(int id, rust_kernel *owner)
    : id(id), owner(owner)
{
}

void rust_task_thread::run()
{
    owner->sched->start_main_loop(id);
}

//
// Local Variables:
// mode: C++
// fill-column: 78;
// indent-tabs-mode: nil
// c-basic-offset: 4
// buffer-file-coding-system: utf-8-unix
// compile-command: "make -k -C .. 2>&1 | sed -e 's/\\/x\\//x:\\//g'";
// End:
//
