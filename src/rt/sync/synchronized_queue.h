// -*- c++ -*-
#ifndef SYNCHRONIZED_QUEUE_H
#define SYNCHRONIZED_QUEUE_H

#include <assert.h>

template <class T>
class synchronized_queue {
    lock_and_signal lock;
    
    struct node_t {
        T value;
        node_t *next;
        node_t *prev;

        node_t()
            : next(this), prev(this)
        {}

        node_t(T value) 
            : value(value), next(this), prev(this)
        {}
    };

    node_t head;
    
public:
    synchronized_queue() 
    {}

    virtual ~synchronized_queue() {
        assert(is_empty());
    }

    bool is_empty() {
        return head.next == &head;
    }

    virtual void enqueue(T value) {
        scoped_lock with(lock);

        node_t *n = new node_t(value);

        n->next = head.next;
        head.next = n;

        n->prev = &head;
        n->next->prev = n;
    }

    bool dequeue(T *value) {
        scoped_lock with(lock);

        if(is_empty()) {
            return false;
        }
        else {
            node_t *n = head.prev;
            assert(n != &head);

            *value = n->value;

            head.prev = n->prev;
            n->prev->next = &head;
            
            return true;
        }
    }
};

#endif /* SYNCHRONIZED_QUEUE_H */
