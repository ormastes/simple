/*
 * Segmented Width Index + Rank/Select for UTF-8 strings
 *
 * SWI: O(log S + W) char↔byte lookup via segment table + linear scan.
 * Rank/Select: O(1) rank via popcount, O(log n) select via binary search.
 * Fallback when SWI degenerates (>1024 segments for adversarial input).
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. runtime_string_index.c
 */

#include "runtime_simd_dispatch.h"
#include <stdlib.h>

/* ================================================================
 * SWI — Segmented Width Index
 * ================================================================ */

#define SWI_SEGMENT_SIZE 64

typedef struct {
    uint64_t byte_offset;
    uint64_t char_offset;
} SwiEntry;

typedef struct SegmentedWidthIndex {
    SwiEntry* entries;
    uint64_t  count;
    uint64_t  total_bytes;
    uint64_t  total_chars;
    const uint8_t* data;
} SegmentedWidthIndex;

static inline uint64_t utf8_byte_len(uint8_t b) {
    if (b < 0x80) return 1;
    if ((b & 0xE0) == 0xC0) return 2;
    if ((b & 0xF0) == 0xE0) return 3;
    if ((b & 0xF8) == 0xF0) return 4;
    return 1;
}

int64_t rt_swi_build(int64_t value) {
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s || s->len == 0) return 0;

    const uint8_t* data = (const uint8_t*)s->data;
    uint64_t len = s->len;
    uint64_t seg_count = (len / SWI_SEGMENT_SIZE) + 2;

    SegmentedWidthIndex* idx = (SegmentedWidthIndex*)malloc(sizeof(SegmentedWidthIndex));
    if (!idx) return 0;
    idx->entries = (SwiEntry*)malloc(seg_count * sizeof(SwiEntry));
    if (!idx->entries) { free(idx); return 0; }

    idx->data = data;
    idx->total_bytes = len;
    idx->entries[0].byte_offset = 0;
    idx->entries[0].char_offset = 0;
    uint64_t entry_idx = 1;
    uint64_t char_count = 0;
    uint64_t next_boundary = SWI_SEGMENT_SIZE;

    uint64_t i = 0;
    while (i < len) {
        if (i >= next_boundary && entry_idx < seg_count) {
            idx->entries[entry_idx].byte_offset = i;
            idx->entries[entry_idx].char_offset = char_count;
            entry_idx++;
            next_boundary += SWI_SEGMENT_SIZE;
        }
        i += utf8_byte_len(data[i]);
        char_count++;
    }

    idx->count = entry_idx;
    idx->total_chars = char_count;
    return (int64_t)(uintptr_t)idx;
}

int64_t rt_swi_char_to_byte(int64_t handle, int64_t char_idx) {
    SegmentedWidthIndex* idx = (SegmentedWidthIndex*)(uintptr_t)handle;
    if (!idx || char_idx < 0) return -1;
    uint64_t target = (uint64_t)char_idx;
    if (target >= idx->total_chars)
        return (target == idx->total_chars) ? (int64_t)idx->total_bytes : -1;

    uint64_t lo = 0, hi = idx->count - 1;
    while (lo < hi) {
        uint64_t mid = lo + (hi - lo + 1) / 2;
        if (idx->entries[mid].char_offset <= target) lo = mid;
        else hi = mid - 1;
    }

    uint64_t byte_pos = idx->entries[lo].byte_offset;
    uint64_t char_pos = idx->entries[lo].char_offset;
    while (char_pos < target && byte_pos < idx->total_bytes) {
        byte_pos += utf8_byte_len(idx->data[byte_pos]);
        char_pos++;
    }
    return (int64_t)byte_pos;
}

int64_t rt_swi_byte_to_char(int64_t handle, int64_t byte_idx) {
    SegmentedWidthIndex* idx = (SegmentedWidthIndex*)(uintptr_t)handle;
    if (!idx || byte_idx < 0) return -1;
    uint64_t target = (uint64_t)byte_idx;
    if (target >= idx->total_bytes)
        return (target == idx->total_bytes) ? (int64_t)idx->total_chars : -1;

    uint64_t lo = 0, hi = idx->count - 1;
    while (lo < hi) {
        uint64_t mid = lo + (hi - lo + 1) / 2;
        if (idx->entries[mid].byte_offset <= target) lo = mid;
        else hi = mid - 1;
    }

    uint64_t byte_pos = idx->entries[lo].byte_offset;
    uint64_t char_pos = idx->entries[lo].char_offset;
    while (byte_pos < target && byte_pos < idx->total_bytes) {
        byte_pos += utf8_byte_len(idx->data[byte_pos]);
        char_pos++;
    }
    return (int64_t)char_pos;
}

void rt_swi_free(int64_t handle) {
    SegmentedWidthIndex* idx = (SegmentedWidthIndex*)(uintptr_t)handle;
    if (!idx) return;
    free(idx->entries);
    free(idx);
}

/* ================================================================
 * Rank/Select Bit-Vector
 *
 * Bitvector where bit i = 1 iff byte i is a codepoint start (lead byte).
 * rank(pos) = number of codepoints before byte pos
 * select(k) = byte position of k-th codepoint
 * ================================================================ */

#define RS_BLOCK_SIZE 512
#define RS_WORDS_PER_BLOCK (RS_BLOCK_SIZE / 64)

typedef struct RankSelectIndex {
    uint64_t* bitvec;
    uint32_t* block_rank;
    uint64_t  bit_count;
    uint64_t  word_count;
    uint64_t  block_count;
    uint64_t  ones_count;
} RankSelectIndex;

static inline uint64_t popcnt64(uint64_t x) {
    return (uint64_t)__builtin_popcountll(x);
}

int64_t rt_rank_select_build(int64_t value) {
    RtCoreStringSimd* s = simd_as_string(value);
    if (!s || s->len == 0) return 0;

    const uint8_t* data = (const uint8_t*)s->data;
    uint64_t len = s->len;

    RankSelectIndex* rs = (RankSelectIndex*)malloc(sizeof(RankSelectIndex));
    if (!rs) return 0;

    rs->bit_count = len;
    rs->word_count = (len + 63) / 64;
    rs->block_count = (len + RS_BLOCK_SIZE - 1) / RS_BLOCK_SIZE;
    rs->bitvec = (uint64_t*)calloc(rs->word_count, sizeof(uint64_t));
    rs->block_rank = (uint32_t*)calloc(rs->block_count + 1, sizeof(uint32_t));
    if (!rs->bitvec || !rs->block_rank) {
        free(rs->bitvec); free(rs->block_rank); free(rs); return 0;
    }

    uint64_t ones = 0;
    for (uint64_t i = 0; i < len; i++) {
        if ((data[i] & 0xC0) != 0x80) {
            rs->bitvec[i / 64] |= (1ULL << (i % 64));
            ones++;
        }
    }
    rs->ones_count = ones;

    uint64_t cumulative = 0;
    for (uint64_t b = 0; b < rs->block_count; b++) {
        rs->block_rank[b] = (uint32_t)cumulative;
        uint64_t w_start = b * RS_WORDS_PER_BLOCK;
        uint64_t w_end = w_start + RS_WORDS_PER_BLOCK;
        if (w_end > rs->word_count) w_end = rs->word_count;
        for (uint64_t w = w_start; w < w_end; w++)
            cumulative += popcnt64(rs->bitvec[w]);
    }
    rs->block_rank[rs->block_count] = (uint32_t)cumulative;

    return (int64_t)(uintptr_t)rs;
}

int64_t rt_rank_query(int64_t handle, int64_t pos) {
    RankSelectIndex* rs = (RankSelectIndex*)(uintptr_t)handle;
    if (!rs || pos < 0) return -1;
    uint64_t p = (uint64_t)pos;
    if (p >= rs->bit_count) p = rs->bit_count;

    uint64_t block = p / RS_BLOCK_SIZE;
    uint64_t count = rs->block_rank[block];

    uint64_t w_start = block * RS_WORDS_PER_BLOCK;
    uint64_t full_words = p / 64;
    uint64_t remainder = p % 64;

    for (uint64_t w = w_start; w < full_words && w < rs->word_count; w++)
        count += popcnt64(rs->bitvec[w]);

    if (remainder > 0 && full_words < rs->word_count) {
        uint64_t mask = (1ULL << remainder) - 1;
        count += popcnt64(rs->bitvec[full_words] & mask);
    }

    return (int64_t)count;
}

int64_t rt_select_query(int64_t handle, int64_t k) {
    RankSelectIndex* rs = (RankSelectIndex*)(uintptr_t)handle;
    if (!rs || k < 0 || (uint64_t)k >= rs->ones_count) return -1;

    uint64_t lo = 0, hi = rs->block_count;
    while (lo < hi) {
        uint64_t mid = lo + (hi - lo) / 2;
        if (rs->block_rank[mid + 1] <= (uint64_t)k) lo = mid + 1;
        else hi = mid;
    }

    uint64_t remaining = (uint64_t)k - rs->block_rank[lo];
    uint64_t w_start = lo * RS_WORDS_PER_BLOCK;
    uint64_t w_end = w_start + RS_WORDS_PER_BLOCK;
    if (w_end > rs->word_count) w_end = rs->word_count;

    for (uint64_t w = w_start; w < w_end; w++) {
        uint64_t pc = popcnt64(rs->bitvec[w]);
        if (remaining < pc) {
            uint64_t v = rs->bitvec[w];
            for (int bit = 0; bit < 64; bit++) {
                if (v & (1ULL << bit)) {
                    if (remaining == 0)
                        return (int64_t)(w * 64 + (uint64_t)bit);
                    remaining--;
                }
            }
        }
        remaining -= pc;
    }
    return -1;
}

void rt_rank_select_free(int64_t handle) {
    RankSelectIndex* rs = (RankSelectIndex*)(uintptr_t)handle;
    if (!rs) return;
    free(rs->bitvec);
    free(rs->block_rank);
    free(rs);
}
