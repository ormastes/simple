/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/lib/bitmap.c -- Fixed-size bitmap implementation
 *
 * Mirrors: spl/kernel/lib/bitmap.spl
 */

#include "kernel/lib/bitmap.h"

/* ------------------------------------------------------------------------ */

void bitmap_init(bitmap_t *bm, uint32_t num_bits)
{
    uint32_t capped = num_bits;
    if (capped > BITMAP_MAX_BITS) {
        capped = BITMAP_MAX_BITS;
    }

    bm->num_bits  = capped;
    bm->num_words = (capped + 31) / 32;

    for (uint32_t i = 0; i < BITMAP_MAX_WORDS; i++) {
        bm->words[i] = 0;
    }
}

/* ------------------------------------------------------------------------ */

void bitmap_set(bitmap_t *bm, uint32_t bit)
{
    if (bit >= bm->num_bits) {
        return;
    }
    uint32_t word_idx = bit / BITMAP_BITS_PER_WORD;
    uint32_t bit_idx  = bit % BITMAP_BITS_PER_WORD;
    bm->words[word_idx] |= ((uint32_t)1 << bit_idx);
}

/* ------------------------------------------------------------------------ */

void bitmap_clear(bitmap_t *bm, uint32_t bit)
{
    if (bit >= bm->num_bits) {
        return;
    }
    uint32_t word_idx = bit / BITMAP_BITS_PER_WORD;
    uint32_t bit_idx  = bit % BITMAP_BITS_PER_WORD;
    bm->words[word_idx] &= ~((uint32_t)1 << bit_idx);
}

/* ------------------------------------------------------------------------ */

bool bitmap_test(const bitmap_t *bm, uint32_t bit)
{
    if (bit >= bm->num_bits) {
        return false;
    }
    uint32_t word_idx = bit / BITMAP_BITS_PER_WORD;
    uint32_t bit_idx  = bit % BITMAP_BITS_PER_WORD;
    return (bm->words[word_idx] & ((uint32_t)1 << bit_idx)) != 0;
}

/* ------------------------------------------------------------------------ */

int32_t bitmap_find_first_clear(const bitmap_t *bm)
{
    for (uint32_t i = 0; i < bm->num_words; i++) {
        /* A word of all-ones has no clear bits -- skip it. */
        if (bm->words[i] == 0xFFFFFFFF) {
            continue;
        }

        for (uint32_t b = 0; b < BITMAP_BITS_PER_WORD; b++) {
            uint32_t bit_index = i * BITMAP_BITS_PER_WORD + b;
            if (bit_index >= bm->num_bits) {
                return -1;
            }
            if ((bm->words[i] & ((uint32_t)1 << b)) == 0) {
                return (int32_t)bit_index;
            }
        }
    }
    return -1;
}

/* ------------------------------------------------------------------------ */

int32_t bitmap_find_first_set(const bitmap_t *bm)
{
    for (uint32_t i = 0; i < bm->num_words; i++) {
        /* A zero word has no set bits -- skip it. */
        if (bm->words[i] == 0) {
            continue;
        }

        for (uint32_t b = 0; b < BITMAP_BITS_PER_WORD; b++) {
            uint32_t bit_index = i * BITMAP_BITS_PER_WORD + b;
            if (bit_index >= bm->num_bits) {
                return -1;
            }
            if ((bm->words[i] & ((uint32_t)1 << b)) != 0) {
                return (int32_t)bit_index;
            }
        }
    }
    return -1;
}

/* ------------------------------------------------------------------------ */

uint32_t bitmap_count_set(const bitmap_t *bm)
{
    uint32_t count = 0;
    for (uint32_t i = 0; i < bm->num_words; i++) {
        uint32_t word = bm->words[i];
        /* Kernighan's bit-counting trick: each iteration clears the
         * lowest set bit, so the loop runs once per set bit. */
        while (word != 0) {
            word = word & (word - 1);
            count++;
        }
    }
    return count;
}

/* ------------------------------------------------------------------------ */

uint32_t bitmap_count_clear(const bitmap_t *bm)
{
    return bm->num_bits - bitmap_count_set(bm);
}

/* ------------------------------------------------------------------------ */

void bitmap_set_range(bitmap_t *bm, uint32_t start, uint32_t count)
{
    for (uint32_t i = 0; i < count; i++) {
        bitmap_set(bm, start + i);
    }
}

/* ------------------------------------------------------------------------ */

void bitmap_clear_range(bitmap_t *bm, uint32_t start, uint32_t count)
{
    for (uint32_t i = 0; i < count; i++) {
        bitmap_clear(bm, start + i);
    }
}

/* ------------------------------------------------------------------------ */

int32_t bitmap_find_contiguous_clear(const bitmap_t *bm, uint32_t count)
{
    if (count == 0) {
        return -1;
    }

    uint32_t run_start = 0;
    uint32_t run_len   = 0;

    for (uint32_t bit = 0; bit < bm->num_bits; bit++) {
        if (bitmap_test(bm, bit)) {
            /* Bit is set -- reset the run. */
            run_start = bit + 1;
            run_len   = 0;
        } else {
            run_len++;
            if (run_len >= count) {
                return (int32_t)run_start;
            }
        }
    }
    return -1;
}
