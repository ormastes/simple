/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/lib/bitmap.h -- Fixed-size bitmap for tracking allocated/free resources
 *
 * Mirrors: spl/kernel/lib/bitmap.spl
 */

#ifndef SIMPLE_OS_BITMAP_H
#define SIMPLE_OS_BITMAP_H

#include "common/types.h"
#include "common/config.h"

/* ---- Data structure ---------------------------------------------------- */

typedef struct {
    uint32_t words[BITMAP_MAX_WORDS];
    uint32_t num_bits;
    uint32_t num_words;
} bitmap_t;

/* ---- API --------------------------------------------------------------- */

/* Initialise a bitmap that can track `num_bits` items, all initially clear. */
void bitmap_init(bitmap_t *bm, uint32_t num_bits);

/* Set a single bit (mark as used / allocated). */
void bitmap_set(bitmap_t *bm, uint32_t bit);

/* Clear a single bit (mark as free). */
void bitmap_clear(bitmap_t *bm, uint32_t bit);

/* Test whether a specific bit is set. */
bool bitmap_test(const bitmap_t *bm, uint32_t bit);

/* Find the index of the first clear (0) bit. Returns -1 if none. */
int32_t bitmap_find_first_clear(const bitmap_t *bm);

/* Find the index of the first set (1) bit. Returns -1 if none. */
int32_t bitmap_find_first_set(const bitmap_t *bm);

/* Count the number of set bits across the entire bitmap. */
uint32_t bitmap_count_set(const bitmap_t *bm);

/* Count the number of clear bits (num_bits - count_set). */
uint32_t bitmap_count_clear(const bitmap_t *bm);

/* Set a contiguous range of bits [start, start+count). */
void bitmap_set_range(bitmap_t *bm, uint32_t start, uint32_t count);

/* Clear a contiguous range of bits [start, start+count). */
void bitmap_clear_range(bitmap_t *bm, uint32_t start, uint32_t count);

/* Find `count` contiguous clear bits. Returns starting index or -1. */
int32_t bitmap_find_contiguous_clear(const bitmap_t *bm, uint32_t count);

#endif /* SIMPLE_OS_BITMAP_H */
