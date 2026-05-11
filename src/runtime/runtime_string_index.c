/*
 * Segmented Width Index + Rank-Select Index for UTF-8 strings
 *
 * Provides O(1) char↔byte offset conversion for random access into
 * UTF-8 strings with mixed-width codepoints.
 *
 * Wave 1: scalar stubs.
 * Wave 2: SIMD-accelerated index building.
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. runtime_string_index.c
 */

#include "runtime_simd_dispatch.h"
#include <stdlib.h>

/* ================================================================
 * SegmentedWidthIndex
 *
 * Divides the string into fixed-size segments (e.g. 64 bytes).
 * Each segment stores the byte offset and cumulative codepoint count
 * at its start.  Lookup: binary search to find segment, then scan
 * within segment.
 * ================================================================ */

#define SWI_SEGMENT_SIZE 64

typedef struct {
    uint64_t byte_offset;
    uint64_t char_offset;
} SwiEntry;

typedef struct SegmentedWidthIndex {
    SwiEntry* entries;
    uint64_t  count;       /* number of segment entries */
    uint64_t  total_bytes; /* total byte length of string */
    uint64_t  total_chars; /* total codepoint count */
} SegmentedWidthIndex;

/*
 * rt_swi_build(tagged_string) -> SegmentedWidthIndex*
 *   Builds an index for the given string.  Caller must rt_swi_free().
 */
SegmentedWidthIndex* rt_swi_build(int64_t value) {
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s) return NULL;

    const uint8_t* data = (const uint8_t*)s->data;
    uint64_t len = s->len;

    /* Estimate segment count */
    uint64_t seg_count = (len / SWI_SEGMENT_SIZE) + 2; /* +1 for tail, +1 for safety */

    SegmentedWidthIndex* idx = (SegmentedWidthIndex*)malloc(sizeof(SegmentedWidthIndex));
    if (!idx) return NULL;

    idx->entries = (SwiEntry*)malloc(seg_count * sizeof(SwiEntry));
    if (!idx->entries) { free(idx); return NULL; }

    idx->total_bytes = len;
    uint64_t char_count = 0;
    uint64_t entry_idx = 0;

    /* Record entry at byte 0 */
    idx->entries[0].byte_offset = 0;
    idx->entries[0].char_offset = 0;
    entry_idx = 1;

    uint64_t next_boundary = SWI_SEGMENT_SIZE;
    uint64_t i = 0;
    while (i < len) {
        if (i >= next_boundary && entry_idx < seg_count) {
            idx->entries[entry_idx].byte_offset = i;
            idx->entries[entry_idx].char_offset = char_count;
            entry_idx++;
            next_boundary += SWI_SEGMENT_SIZE;
        }

        uint8_t b = data[i];
        if (b < 0x80)        i += 1;
        else if ((b & 0xE0) == 0xC0) i += 2;
        else if ((b & 0xF0) == 0xE0) i += 3;
        else if ((b & 0xF8) == 0xF0) i += 4;
        else                  i += 1; /* invalid byte, skip */
        char_count++;
    }

    idx->count = entry_idx;
    idx->total_chars = char_count;
    return idx;
}

/*
 * rt_swi_char_to_byte(idx, char_offset) -> int64_t
 *   Converts a codepoint index to a byte offset.
 *   Returns -1 if out of range.
 */
int64_t rt_swi_char_to_byte(SegmentedWidthIndex* idx, int64_t char_offset) {
    if (!idx || char_offset < 0 || (uint64_t)char_offset > idx->total_chars)
        return -1;
    if ((uint64_t)char_offset == idx->total_chars)
        return (int64_t)idx->total_bytes;

    /* Binary search for the segment containing this char offset */
    uint64_t lo = 0, hi = idx->count - 1;
    while (lo < hi) {
        uint64_t mid = lo + (hi - lo + 1) / 2;
        if (idx->entries[mid].char_offset <= (uint64_t)char_offset)
            lo = mid;
        else
            hi = mid - 1;
    }

    /* lo is the segment — now scan forward from entries[lo] */
    /* (This is a stub — Wave 2 will use the dispatch table for scanning) */
    (void)lo;

    /* Simple linear scan from segment start */
    /* TODO: optimize with SIMD in Wave 2 */
    return (int64_t)idx->entries[lo].byte_offset;
    /* NOTE: this returns the segment start, not the exact byte.
     * Full implementation would scan from segment start to char_offset. */
}

/*
 * rt_swi_byte_to_char(idx, byte_offset) -> int64_t
 *   Converts a byte offset to a codepoint index.
 *   Returns -1 if out of range.
 */
int64_t rt_swi_byte_to_char(SegmentedWidthIndex* idx, int64_t byte_offset) {
    if (!idx || byte_offset < 0 || (uint64_t)byte_offset > idx->total_bytes)
        return -1;
    if ((uint64_t)byte_offset == idx->total_bytes)
        return (int64_t)idx->total_chars;

    /* Binary search for the segment containing this byte offset */
    uint64_t lo = 0, hi = idx->count - 1;
    while (lo < hi) {
        uint64_t mid = lo + (hi - lo + 1) / 2;
        if (idx->entries[mid].byte_offset <= (uint64_t)byte_offset)
            lo = mid;
        else
            hi = mid - 1;
    }

    /* Return segment's char offset as approximation.
     * Full implementation would scan from segment start. */
    return (int64_t)idx->entries[lo].char_offset;
}

/*
 * rt_swi_free(idx) — release all memory.
 */
void rt_swi_free(SegmentedWidthIndex* idx) {
    if (!idx) return;
    free(idx->entries);
    free(idx);
}

/* ================================================================
 * RankSelectIndex
 *
 * Bitvector-based rank/select for marking ASCII vs multi-byte
 * codepoint positions.  Enables O(1) rank (count of 1-bits up to
 * position) and O(log n) select (position of the k-th 1-bit).
 *
 * Wave 1: simple array-based stub.
 * Wave 2: cache-line-aligned blocks with popcount intrinsics.
 * ================================================================ */

typedef struct RankSelectIndex {
    uint64_t* bitvec;      /* packed 64-bit words */
    uint64_t  bit_count;   /* total number of bits */
    uint64_t  word_count;  /* number of 64-bit words */
    uint64_t  ones_count;  /* total number of set bits */
} RankSelectIndex;

/*
 * rt_rank_select_build(data, len) -> RankSelectIndex*
 *   Builds a bitvector marking non-ASCII lead bytes (bit=1 for multi-byte
 *   codepoint start, bit=0 for ASCII or continuation byte).
 */
RankSelectIndex* rt_rank_select_build(const uint8_t* data, uint64_t len) {
    if (!data || len == 0) return NULL;

    RankSelectIndex* rs = (RankSelectIndex*)malloc(sizeof(RankSelectIndex));
    if (!rs) return NULL;

    rs->bit_count = len;
    rs->word_count = (len + 63) / 64;
    rs->bitvec = (uint64_t*)calloc(rs->word_count, sizeof(uint64_t));
    if (!rs->bitvec) { free(rs); return NULL; }

    uint64_t ones = 0;
    for (uint64_t i = 0; i < len; i++) {
        if (data[i] >= 0x80 && (data[i] & 0xC0) != 0x80) {
            /* Multi-byte lead byte — set bit */
            rs->bitvec[i / 64] |= (1ULL << (i % 64));
            ones++;
        }
    }
    rs->ones_count = ones;
    return rs;
}

/*
 * rt_rank_query(rs, pos) -> int64_t
 *   Count of set bits in [0, pos).
 *   Returns -1 on error.
 */
int64_t rt_rank_query(RankSelectIndex* rs, int64_t pos) {
    if (!rs || pos < 0) return -1;
    uint64_t p = (uint64_t)pos;
    if (p > rs->bit_count) p = rs->bit_count;

    uint64_t count = 0;
    uint64_t full_words = p / 64;
    uint64_t remainder = p % 64;

    for (uint64_t w = 0; w < full_words; w++) {
        /* popcount — Wave 2 will use __builtin_popcountll */
        uint64_t v = rs->bitvec[w];
        /* Kernighan's bit-count */
        while (v) { v &= v - 1; count++; }
    }

    if (remainder > 0 && full_words < rs->word_count) {
        uint64_t mask = (1ULL << remainder) - 1;
        uint64_t v = rs->bitvec[full_words] & mask;
        while (v) { v &= v - 1; count++; }
    }

    return (int64_t)count;
}

/*
 * rt_select_query(rs, k) -> int64_t
 *   Position of the k-th set bit (0-indexed).
 *   Returns -1 if k >= ones_count.
 */
int64_t rt_select_query(RankSelectIndex* rs, int64_t k) {
    if (!rs || k < 0 || (uint64_t)k >= rs->ones_count) return -1;

    uint64_t remaining = (uint64_t)k;
    for (uint64_t w = 0; w < rs->word_count; w++) {
        uint64_t v = rs->bitvec[w];
        /* Count bits in this word */
        uint64_t wc = 0;
        uint64_t tmp = v;
        while (tmp) { tmp &= tmp - 1; wc++; }

        if (remaining < wc) {
            /* The k-th bit is in this word */
            for (int bit = 0; bit < 64; bit++) {
                if (v & (1ULL << bit)) {
                    if (remaining == 0)
                        return (int64_t)(w * 64 + (uint64_t)bit);
                    remaining--;
                }
            }
        }
        remaining -= wc;
    }
    return -1;
}

/*
 * rt_rank_select_free(rs) — release all memory.
 */
void rt_rank_select_free(RankSelectIndex* rs) {
    if (!rs) return;
    free(rs->bitvec);
    free(rs);
}
