/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/lib/ring_buffer.h -- Fixed-size circular FIFO queue of u32 values
 *
 * Mirrors: spl/kernel/lib/ring_buffer.spl
 *
 * The buffer holds up to (capacity - 1) elements to distinguish full
 * from empty.
 */

#ifndef SIMPLE_OS_RING_BUFFER_H
#define SIMPLE_OS_RING_BUFFER_H

#include "common/types.h"
#include "common/config.h"

/* ---- Data structure ---------------------------------------------------- */

typedef struct {
    uint32_t data[RING_MAX_CAPACITY];
    uint32_t head;       /* Index of next slot to read  */
    uint32_t tail;       /* Index of next slot to write */
    uint32_t capacity;   /* Total number of slots (usable = capacity - 1) */
} ring_buffer_t;

/* ---- API --------------------------------------------------------------- */

/* Initialise an empty ring buffer with the given capacity (clamped [2, 256]). */
void ring_buffer_init(ring_buffer_t *rb, uint32_t capacity);

/* Returns true if the buffer contains no elements. */
bool ring_buffer_is_empty(const ring_buffer_t *rb);

/* Returns true if the buffer is full (no room to push). */
bool ring_buffer_is_full(const ring_buffer_t *rb);

/* Returns the number of elements currently stored. */
uint32_t ring_buffer_count(const ring_buffer_t *rb);

/* Returns the number of free slots remaining. */
uint32_t ring_buffer_free_count(const ring_buffer_t *rb);

/* Push a value onto the tail. Returns true on success, false if full. */
bool ring_buffer_push(ring_buffer_t *rb, uint32_t value);

/*
 * Pop a value from the head.
 * Returns true on success and writes the value to *out.
 * Returns false if the buffer is empty (*out is unchanged).
 */
bool ring_buffer_pop(ring_buffer_t *rb, uint32_t *out);

/*
 * Peek at the head value without removing it.
 * Returns true on success and writes the value to *out.
 */
bool ring_buffer_peek(const ring_buffer_t *rb, uint32_t *out);

/*
 * Peek at a specific offset from head (0 = head).
 * Returns true on success and writes the value to *out.
 */
bool ring_buffer_peek_at(const ring_buffer_t *rb, uint32_t offset, uint32_t *out);

/* Discard all elements, resetting the buffer to empty. */
void ring_buffer_clear(ring_buffer_t *rb);

/*
 * Try to push multiple values. Returns the number actually pushed.
 * Stops at the first failure (buffer full).
 */
uint32_t ring_buffer_push_batch(ring_buffer_t *rb, const uint32_t *values,
                                uint32_t count);

/*
 * Try to pop multiple values into a caller-supplied array.
 * Returns the number actually popped.
 */
uint32_t ring_buffer_pop_batch(ring_buffer_t *rb, uint32_t *out,
                               uint32_t max_count);

#endif /* SIMPLE_OS_RING_BUFFER_H */
