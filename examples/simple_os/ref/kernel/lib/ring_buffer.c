/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/lib/ring_buffer.c -- Fixed-size circular FIFO queue
 *
 * Mirrors: spl/kernel/lib/ring_buffer.spl
 */

#include "kernel/lib/ring_buffer.h"

/* ------------------------------------------------------------------------ */

void ring_buffer_init(ring_buffer_t *rb, uint32_t capacity)
{
    uint32_t cap = capacity;
    if (cap > RING_MAX_CAPACITY) {
        cap = RING_MAX_CAPACITY;
    } else if (cap < 2) {
        cap = 2; /* Minimum 2 to hold at least 1 element */
    }

    rb->head     = 0;
    rb->tail     = 0;
    rb->capacity = cap;

    for (uint32_t i = 0; i < RING_MAX_CAPACITY; i++) {
        rb->data[i] = 0;
    }
}

/* ------------------------------------------------------------------------ */

bool ring_buffer_is_empty(const ring_buffer_t *rb)
{
    return rb->head == rb->tail;
}

/* ------------------------------------------------------------------------ */

bool ring_buffer_is_full(const ring_buffer_t *rb)
{
    return ((rb->tail + 1) % rb->capacity) == rb->head;
}

/* ------------------------------------------------------------------------ */

uint32_t ring_buffer_count(const ring_buffer_t *rb)
{
    if (rb->tail >= rb->head) {
        return rb->tail - rb->head;
    }
    return rb->capacity - rb->head + rb->tail;
}

/* ------------------------------------------------------------------------ */

uint32_t ring_buffer_free_count(const ring_buffer_t *rb)
{
    /* Usable capacity is (capacity - 1) since one slot is always unused. */
    return (rb->capacity - 1) - ring_buffer_count(rb);
}

/* ------------------------------------------------------------------------ */

bool ring_buffer_push(ring_buffer_t *rb, uint32_t value)
{
    if (ring_buffer_is_full(rb)) {
        return false;
    }
    rb->data[rb->tail] = value;
    rb->tail = (rb->tail + 1) % rb->capacity;
    return true;
}

/* ------------------------------------------------------------------------ */

bool ring_buffer_pop(ring_buffer_t *rb, uint32_t *out)
{
    if (ring_buffer_is_empty(rb)) {
        return false;
    }
    *out = rb->data[rb->head];
    rb->head = (rb->head + 1) % rb->capacity;
    return true;
}

/* ------------------------------------------------------------------------ */

bool ring_buffer_peek(const ring_buffer_t *rb, uint32_t *out)
{
    if (ring_buffer_is_empty(rb)) {
        return false;
    }
    *out = rb->data[rb->head];
    return true;
}

/* ------------------------------------------------------------------------ */

bool ring_buffer_peek_at(const ring_buffer_t *rb, uint32_t offset, uint32_t *out)
{
    if (offset >= ring_buffer_count(rb)) {
        return false;
    }
    uint32_t idx = (rb->head + offset) % rb->capacity;
    *out = rb->data[idx];
    return true;
}

/* ------------------------------------------------------------------------ */

void ring_buffer_clear(ring_buffer_t *rb)
{
    rb->head = 0;
    rb->tail = 0;
}

/* ------------------------------------------------------------------------ */

uint32_t ring_buffer_push_batch(ring_buffer_t *rb, const uint32_t *values,
                                uint32_t count)
{
    uint32_t pushed = 0;
    for (uint32_t i = 0; i < count; i++) {
        if (!ring_buffer_push(rb, values[i])) {
            break;
        }
        pushed++;
    }
    return pushed;
}

/* ------------------------------------------------------------------------ */

uint32_t ring_buffer_pop_batch(ring_buffer_t *rb, uint32_t *out,
                               uint32_t max_count)
{
    uint32_t popped = 0;
    for (uint32_t i = 0; i < max_count; i++) {
        if (!ring_buffer_pop(rb, &out[i])) {
            break;
        }
        popped++;
    }
    return popped;
}
