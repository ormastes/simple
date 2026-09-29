#include <stdio.h>

#include "cosmos_nvme_media_policy.h"
#include "cosmos_nvme_media_policy_oracle.h"

#define EXPECTED_PARITY_ROWS 196U
#define P(name) cosmos_nvme_media_policy_##name
#define O(name) cosmos_nvme_media_oracle_##name
#define STRINGIFY_INNER(value) #value
#define STRINGIFY(value) STRINGIFY_INNER(value)

typedef unsigned int (*sig_u_void)(void);
typedef int (*sig_i_1u)(unsigned int);
typedef unsigned int (*sig_u_1u)(unsigned int);
typedef unsigned int (*sig_u_2u)(unsigned int, unsigned int);
typedef int (*sig_i_2u)(unsigned int, unsigned int);
typedef int (*sig_i_3u)(unsigned int, unsigned int, unsigned int);
typedef int (*sig_i_5u)(unsigned int, unsigned int, unsigned int,
                        unsigned int, unsigned int);
typedef int (*sig_i_6u)(unsigned int, unsigned int, unsigned int,
                        unsigned int, unsigned int, unsigned int);
typedef int (*sig_i_7u)(unsigned int, unsigned int, unsigned int,
                        unsigned int, unsigned int, unsigned int,
                        unsigned int);
typedef int (*sig_i_9u)(unsigned int, unsigned int, unsigned int,
                        unsigned int, unsigned int, unsigned int,
                        unsigned int, unsigned int, unsigned int);
typedef int (*sig_i_10u)(unsigned int, unsigned int, unsigned int,
                         unsigned int, unsigned int, unsigned int,
                         unsigned int, unsigned int, unsigned int,
                         unsigned int);
typedef unsigned int (*sig_u_10u)(unsigned int, unsigned int, unsigned int,
                                  unsigned int, unsigned int, unsigned int,
                                  unsigned int, unsigned int, unsigned int,
                                  unsigned int);
typedef unsigned int (*sig_u_14u)(unsigned int, unsigned int, unsigned int,
                                  unsigned int, unsigned int, unsigned int,
                                  unsigned int, unsigned int, unsigned int,
                                  unsigned int, unsigned int, unsigned int,
                                  unsigned int, unsigned int);
typedef unsigned int (*sig_u_16u)(unsigned int, unsigned int, unsigned int,
                                  unsigned int, unsigned int, unsigned int,
                                  unsigned int, unsigned int, unsigned int,
                                  unsigned int, unsigned int, unsigned int,
                                  unsigned int, unsigned int, unsigned int,
                                  unsigned int);
typedef unsigned int (*sig_u_i_1u)(int, unsigned int);
typedef unsigned int (*sig_u_i_3u)(int, unsigned int, unsigned int,
                                   unsigned int);
typedef int (*sig_i_i_2u)(int, unsigned int, unsigned int);
typedef int (*sig_i_2u_ull_2u)(unsigned int, unsigned int,
                               unsigned long long, unsigned int,
                               unsigned int);
typedef unsigned long long (*sig_ull_2u)(unsigned int, unsigned int);

#define ABI_ASSERT(function, signature)                                     \
    _Static_assert(_Generic(&(function), signature: 1, default: 0),          \
                   "ABI type mismatch: " #function)
#define ABI_ASSERT_PAIR(name, signature)                                    \
    ABI_ASSERT(P(name), signature);                                          \
    ABI_ASSERT(O(name), signature)

ABI_ASSERT_PAIR(status_success, sig_u_void);
ABI_ASSERT_PAIR(status_invalid_opcode, sig_u_void);
ABI_ASSERT_PAIR(status_invalid_field, sig_u_void);
ABI_ASSERT_PAIR(status_invalid_namespace, sig_u_void);
ABI_ASSERT_PAIR(status_lba_range, sig_u_void);
ABI_ASSERT_PAIR(status_data_transfer, sig_u_void);
ABI_ASSERT_PAIR(status_is_success, sig_i_1u);
ABI_ASSERT_PAIR(media_status, sig_u_i_1u);
ABI_ASSERT_PAIR(end_within_namespace, sig_i_5u);
ABI_ASSERT_PAIR(data_span_valid, sig_i_6u);
ABI_ASSERT_PAIR(rw_status, sig_u_14u);
ABI_ASSERT_PAIR(flush_status, sig_u_10u);
ABI_ASSERT_PAIR(zeroes_status, sig_u_16u);
ABI_ASSERT_PAIR(dsm_status, sig_u_14u);
ABI_ASSERT_PAIR(post_state, sig_u_1u);
ABI_ASSERT_PAIR(post_status, sig_i_1u);
ABI_ASSERT_PAIR(service_init_valid, sig_i_7u);
ABI_ASSERT_PAIR(dispatch_init_valid, sig_i_6u);
ABI_ASSERT_PAIR(dispatch_queue_status, sig_i_5u);
ABI_ASSERT_PAIR(u64, sig_ull_2u);
ABI_ASSERT_PAIR(address_set_valid, sig_i_5u);
ABI_ASSERT_PAIR(command_span_status, sig_i_9u);
ABI_ASSERT_PAIR(zeroes_span_status, sig_i_10u);
ABI_ASSERT_PAIR(retry_limit, sig_u_1u);
ABI_ASSERT_PAIR(command_retry_limit, sig_u_2u);
ABI_ASSERT_PAIR(begin_status, sig_i_3u);
ABI_ASSERT_PAIR(retry_terminal, sig_i_i_2u);
ABI_ASSERT_PAIR(mapped_read_status, sig_i_i_2u);
ABI_ASSERT_PAIR(dma_offsets_valid, sig_i_2u);
ABI_ASSERT_PAIR(page_action, sig_u_i_3u);
ABI_ASSERT_PAIR(page_count, sig_u_2u);
ABI_ASSERT_PAIR(dsm_range_valid, sig_i_2u_ull_2u);
ABI_ASSERT_PAIR(init_valid, sig_i_7u);
ABI_ASSERT_PAIR(deallocate_valid, sig_i_7u);
ABI_ASSERT_PAIR(chunk_bytes, sig_u_1u);
ABI_ASSERT_PAIR(full_page, sig_i_2u);

/*
 * Keep the frozen ledger sensitive to the values passed into every oracle
 * call.  Stringifying the production expression alone is insufficient for
 * rows generated from loop variables: it binds the variable names, not their
 * runtime values.
 */
#undef O
#define ORACLE_FN_INNER(name) cosmos_nvme_media_oracle_##name
#define ORACLE_FN(name) ORACLE_FN_INNER(name)
#define TRACKED_ORACLE0(name)                                               \
    (record_call(#name, NULL, 0U), ORACLE_FN(name)())
#define TRACKED_ORACLE(name, ...)                                           \
    (record_call(#name,                                                     \
                 (const unsigned long long[]){__VA_ARGS__},                 \
                 sizeof((const unsigned long long[]){__VA_ARGS__}) /        \
                     sizeof(unsigned long long)),                           \
     ORACLE_FN(name)(__VA_ARGS__))
#define O(name) TRACKED_ORACLE_##name
#define TRACKED_ORACLE_status_success() TRACKED_ORACLE0(status_success)
#define TRACKED_ORACLE_status_invalid_opcode()                              \
    TRACKED_ORACLE0(status_invalid_opcode)
#define TRACKED_ORACLE_status_invalid_field()                               \
    TRACKED_ORACLE0(status_invalid_field)
#define TRACKED_ORACLE_status_invalid_namespace()                           \
    TRACKED_ORACLE0(status_invalid_namespace)
#define TRACKED_ORACLE_status_lba_range() TRACKED_ORACLE0(status_lba_range)
#define TRACKED_ORACLE_status_data_transfer()                               \
    TRACKED_ORACLE0(status_data_transfer)
#define TRACKED_ORACLE_status_is_success(...)                               \
    TRACKED_ORACLE(status_is_success, __VA_ARGS__)
#define TRACKED_ORACLE_media_status(...) TRACKED_ORACLE(media_status, __VA_ARGS__)
#define TRACKED_ORACLE_end_within_namespace(...)                            \
    TRACKED_ORACLE(end_within_namespace, __VA_ARGS__)
#define TRACKED_ORACLE_data_span_valid(...)                                 \
    TRACKED_ORACLE(data_span_valid, __VA_ARGS__)
#define TRACKED_ORACLE_rw_status(...) TRACKED_ORACLE(rw_status, __VA_ARGS__)
#define TRACKED_ORACLE_flush_status(...) TRACKED_ORACLE(flush_status, __VA_ARGS__)
#define TRACKED_ORACLE_zeroes_status(...)                                   \
    TRACKED_ORACLE(zeroes_status, __VA_ARGS__)
#define TRACKED_ORACLE_dsm_status(...) TRACKED_ORACLE(dsm_status, __VA_ARGS__)
#define TRACKED_ORACLE_post_state(...) TRACKED_ORACLE(post_state, __VA_ARGS__)
#define TRACKED_ORACLE_post_status(...) TRACKED_ORACLE(post_status, __VA_ARGS__)
#define TRACKED_ORACLE_service_init_valid(...)                              \
    TRACKED_ORACLE(service_init_valid, __VA_ARGS__)
#define TRACKED_ORACLE_dispatch_init_valid(...)                             \
    TRACKED_ORACLE(dispatch_init_valid, __VA_ARGS__)
#define TRACKED_ORACLE_dispatch_queue_status(...)                           \
    TRACKED_ORACLE(dispatch_queue_status, __VA_ARGS__)
#define TRACKED_ORACLE_u64(...) TRACKED_ORACLE(u64, __VA_ARGS__)
#define TRACKED_ORACLE_address_set_valid(...)                               \
    TRACKED_ORACLE(address_set_valid, __VA_ARGS__)
#define TRACKED_ORACLE_command_span_status(...)                             \
    TRACKED_ORACLE(command_span_status, __VA_ARGS__)
#define TRACKED_ORACLE_zeroes_span_status(...)                              \
    TRACKED_ORACLE(zeroes_span_status, __VA_ARGS__)
#define TRACKED_ORACLE_retry_limit(...) TRACKED_ORACLE(retry_limit, __VA_ARGS__)
#define TRACKED_ORACLE_command_retry_limit(...)                             \
    TRACKED_ORACLE(command_retry_limit, __VA_ARGS__)
#define TRACKED_ORACLE_begin_status(...) TRACKED_ORACLE(begin_status, __VA_ARGS__)
#define TRACKED_ORACLE_retry_terminal(...)                                  \
    TRACKED_ORACLE(retry_terminal, __VA_ARGS__)
#define TRACKED_ORACLE_mapped_read_status(...)                              \
    TRACKED_ORACLE(mapped_read_status, __VA_ARGS__)
#define TRACKED_ORACLE_dma_offsets_valid(...)                               \
    TRACKED_ORACLE(dma_offsets_valid, __VA_ARGS__)
#define TRACKED_ORACLE_page_action(...) TRACKED_ORACLE(page_action, __VA_ARGS__)
#define TRACKED_ORACLE_page_count(...) TRACKED_ORACLE(page_count, __VA_ARGS__)
#define TRACKED_ORACLE_dsm_range_valid(...)                                 \
    TRACKED_ORACLE(dsm_range_valid, __VA_ARGS__)
#define TRACKED_ORACLE_init_valid(...) TRACKED_ORACLE(init_valid, __VA_ARGS__)
#define TRACKED_ORACLE_deallocate_valid(...)                                \
    TRACKED_ORACLE(deallocate_valid, __VA_ARGS__)
#define TRACKED_ORACLE_chunk_bytes(...) TRACKED_ORACLE(chunk_bytes, __VA_ARGS__)
#define TRACKED_ORACLE_full_page(...) TRACKED_ORACLE(full_page, __VA_ARGS__)

static unsigned int parity_rows;
static unsigned long long parity_digest = 0xcbf29ce484222325ULL;

static void record_call(const char *name, const unsigned long long *inputs,
                        size_t input_count);

static void record_vector(const char *vector) {
    const unsigned char *cursor = (const unsigned char *)vector;

    while (*cursor != 0U) {
        parity_digest ^= *cursor;
        parity_digest *= 0x100000001b3ULL;
        cursor++;
    }
    parity_digest ^= 0xffU;
    parity_digest *= 0x100000001b3ULL;
}

static void record_call(const char *name, const unsigned long long *inputs,
                        size_t input_count) {
    size_t index;
    size_t byte_index;

    record_vector(name);
    parity_digest ^= (unsigned long long)input_count;
    parity_digest *= 0x100000001b3ULL;
    for (index = 0U; index < input_count; index++) {
        for (byte_index = 0U; byte_index < 8U; byte_index++) {
            parity_digest ^= (inputs[index] >> (byte_index * 8U)) & 0xffU;
            parity_digest *= 0x100000001b3ULL;
        }
    }
}

static void record_value(unsigned long long value) {
    parity_digest ^= value + parity_rows;
    parity_digest *= 0x100000001b3ULL;
    parity_rows++;
}

#if defined(COSMOS_NVME_MEDIA_ORACLE_COVERAGE_ONLY)
#define CHECK32(production, oracle) do {                                    \
    record_vector(STRINGIFY(production));                                    \
    record_value((unsigned int)(oracle));                                    \
} while (0)
#define CHECK64(production, oracle) do {                                    \
    record_vector(STRINGIFY(production));                                    \
    record_value((unsigned long long)(oracle));                              \
} while (0)
#else
#define CHECK32(production, oracle) do {                                    \
    unsigned int production_value_ = (unsigned int)(production);             \
    unsigned int oracle_value_ = (unsigned int)(oracle);                     \
    record_vector(STRINGIFY(production));                                    \
    if (production_value_ != oracle_value_) {                                \
        fprintf(stderr, "row %u mismatch: Simple=%08x oracle=%08x\n",      \
                parity_rows + 1U, production_value_, oracle_value_);         \
        return 1;                                                            \
    }                                                                        \
    record_value(oracle_value_);                                             \
} while (0)
#define CHECK64(production, oracle) do {                                    \
    unsigned long long production_value_ =                                  \
        (unsigned long long)(production);                                    \
    unsigned long long oracle_value_ = (unsigned long long)(oracle);         \
    record_vector(STRINGIFY(production));                                    \
    if (production_value_ != oracle_value_) {                                \
        fprintf(stderr, "row %u mismatch: Simple=%016llx oracle=%016llx\n",\
                parity_rows + 1U, production_value_, oracle_value_);         \
        return 1;                                                            \
    }                                                                        \
    record_value(oracle_value_);                                             \
} while (0)
#endif

int main(void) {
    CHECK32(P(status_success)(), O(status_success)());
    CHECK32(P(status_invalid_opcode)(), O(status_invalid_opcode)());
    CHECK32(P(status_invalid_field)(), O(status_invalid_field)());
    CHECK32(P(status_invalid_namespace)(), O(status_invalid_namespace)());
    CHECK32(P(status_lba_range)(), O(status_lba_range)());
    CHECK32(P(status_data_transfer)(), O(status_data_transfer)());
    CHECK32(P(status_is_success)(0U), O(status_is_success)(0U));
    CHECK32(P(status_is_success)(1U), O(status_is_success)(1U));

    CHECK32(P(media_status)(0, 0x80U), O(media_status)(0, 0x80U));
    CHECK32(P(media_status)(1, 0x80U), O(media_status)(1, 0x80U));
    CHECK32(P(media_status)(3, 0x80U), O(media_status)(3, 0x80U));
    CHECK32(P(media_status)(4, 0x81U), O(media_status)(4, 0x81U));
    CHECK32(P(media_status)(2, 0x80U), O(media_status)(2, 0x80U));

    CHECK64(P(u64)(0U, 0U), O(u64)(0U, 0U));
    CHECK64(P(u64)(0xffffffffU, 0U), O(u64)(0xffffffffU, 0U));
    CHECK64(P(u64)(0x89abcdefU, 0x01234567U),
            O(u64)(0x89abcdefU, 0x01234567U));

    CHECK32(P(end_within_namespace)(16U, 0U, 0U, 0U, 1U),
            O(end_within_namespace)(16U, 0U, 0U, 0U, 1U));
    CHECK32(P(end_within_namespace)(16U, 0U, 16U, 0U, 1U),
            O(end_within_namespace)(16U, 0U, 16U, 0U, 1U));
    CHECK32(P(end_within_namespace)(0U, 1U, 0xffffffffU, 0U, 1U),
            O(end_within_namespace)(0U, 1U, 0xffffffffU, 0U, 1U));
    CHECK32(P(end_within_namespace)(0U, 0xffffffffU,
                                    0xffffffffU, 0xffffffffU, 1U),
            O(end_within_namespace)(0U, 0xffffffffU,
                                    0xffffffffU, 0xffffffffU, 1U));
    CHECK32(P(end_within_namespace)(0U, 2U, 0U, 1U, 1U),
            O(end_within_namespace)(0U, 2U, 0U, 1U, 1U));
    CHECK32(P(end_within_namespace)(0U, 0U, 0U, 1U, 1U),
            O(end_within_namespace)(0U, 0U, 0U, 1U, 1U));
    CHECK32(P(end_within_namespace)(8U, 1U, 7U, 1U, 1U),
            O(end_within_namespace)(8U, 1U, 7U, 1U, 1U));
    CHECK32(P(end_within_namespace)(8U, 1U, 8U, 1U, 1U),
            O(end_within_namespace)(8U, 1U, 8U, 1U, 1U));

    CHECK32(P(data_span_valid)(0U, 0U, 0U, 0U, 4U, 4U),
            O(data_span_valid)(0U, 0U, 0U, 0U, 4U, 4U));
    CHECK32(P(data_span_valid)(1U, 0U, 0U, 0U, 4U, 4U),
            O(data_span_valid)(1U, 0U, 0U, 0U, 4U, 4U));
    CHECK32(P(data_span_valid)(0U, 1U, 0U, 0U, 4U, 4U),
            O(data_span_valid)(0U, 1U, 0U, 0U, 4U, 4U));
    CHECK32(P(data_span_valid)(0x1000U, 0U, 1U, 0U, 4U, 4U),
            O(data_span_valid)(0x1000U, 0U, 1U, 0U, 4U, 4U));
    CHECK32(P(data_span_valid)(0x1000U, 0U, 0U, 1U, 4U, 4U),
            O(data_span_valid)(0x1000U, 0U, 0U, 1U, 4U, 4U));
    CHECK32(P(data_span_valid)(0x1000U, 0U, 0U, 0U, 8U, 4U),
            O(data_span_valid)(0x1000U, 0U, 0U, 0U, 8U, 4U));
    CHECK32(P(data_span_valid)(0x1000U, 0U, 0U, 0U, 4U, 4U),
            O(data_span_valid)(0x1000U, 0U, 0U, 0U, 4U, 4U));

#define RW(cid, nsid, nlb, control, address, bytes, nsblocks, block)          \
    CHECK32(P(rw_status)(cid, nsid, 0U, 0U, nlb, control, address, 0U,       \
                         0U, 0U, bytes, nsblocks, 0U, block),                \
            O(rw_status)(cid, nsid, 0U, 0U, nlb, control, address, 0U,       \
                         0U, 0U, bytes, nsblocks, 0U, block))
    RW(0x10000U, 1U, 0U, 0U, 0x1000U, 4096U, 16U, 4096U);
    RW(1U, 1U, 0x10000U, 0U, 0x1000U, 4096U, 16U, 4096U);
    RW(1U, 1U, 0U, 1U, 0x1000U, 4096U, 16U, 4096U);
    RW(1U, 2U, 0U, 0U, 0x1000U, 4096U, 16U, 4096U);
    RW(1U, 1U, 0U, 0U, 0x1000U, 4096U, 0U, 4096U);
    RW(1U, 1U, 0U, 0U, 0x1000U, 4096U, 16U, 0U);
    RW(1U, 1U, 0xffffU, 0U, 0x1000U, 0U, 0x20000U, 65536U);
    RW(1U, 1U, 0U, 0U, 1U, 4096U, 16U, 4096U);
    RW(1U, 1U, 0U, 0U, 0x1000U, 8192U, 16U, 4096U);
    RW(1U, 1U, 0U, 0U, 0x1000U, 4096U, 16U, 4096U);
#undef RW

#define FLUSH(cid, nsid, llo, lhi, nlb, alo, ahi, a2lo, a2hi, bytes)         \
    CHECK32(P(flush_status)(cid, nsid, llo, lhi, nlb, alo, ahi, a2lo,       \
                            a2hi, bytes),                                    \
            O(flush_status)(cid, nsid, llo, lhi, nlb, alo, ahi, a2lo,       \
                            a2hi, bytes))
    FLUSH(0U, 2U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U);
    FLUSH(0x10000U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U);
    FLUSH(0U, 1U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, 0U);
    FLUSH(0U, 1U, 0U, 1U, 0U, 0U, 0U, 0U, 0U, 0U);
    FLUSH(0U, 1U, 0U, 0U, 1U, 0U, 0U, 0U, 0U, 0U);
    FLUSH(0U, 1U, 0U, 0U, 0U, 1U, 0U, 0U, 0U, 0U);
    FLUSH(0U, 1U, 0U, 0U, 0U, 0U, 1U, 0U, 0U, 0U);
    FLUSH(0U, 1U, 0U, 0U, 0U, 0U, 0U, 1U, 0U, 0U);
    FLUSH(0U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, 1U, 0U);
    FLUSH(0U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 1U);
    FLUSH(0U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U);
#undef FLUSH

#define ZERO(cid, nsid, nlb, ctl, attr, ranges, alo, ahi, a2lo, a2hi,       \
             bytes, nsblocks, callback)                                     \
    CHECK32(P(zeroes_status)(cid, nsid, 0U, 0U, nlb, ctl, attr, ranges,     \
                              alo, ahi, a2lo, a2hi, bytes, nsblocks, 0U,     \
                              callback),                                     \
            O(zeroes_status)(cid, nsid, 0U, 0U, nlb, ctl, attr, ranges,     \
                              alo, ahi, a2lo, a2hi, bytes, nsblocks, 0U,     \
                              callback))
    ZERO(0U, 2U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 16U, 1U);
    ZERO(0x10000U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 16U, 1U);
    ZERO(0U, 1U, 0x10000U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 16U, 1U);
    ZERO(0U, 1U, 0U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 16U, 1U);
    ZERO(0U, 1U, 0U, 0U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, 16U, 1U);
    ZERO(0U, 1U, 0U, 0U, 0U, 1U, 0U, 0U, 0U, 0U, 0U, 16U, 1U);
    ZERO(0U, 1U, 0U, 0U, 0U, 0U, 1U, 0U, 0U, 0U, 0U, 16U, 1U);
    ZERO(0U, 1U, 0U, 0U, 0U, 0U, 0U, 1U, 0U, 0U, 0U, 16U, 1U);
    ZERO(0U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, 1U, 0U, 0U, 16U, 1U);
    ZERO(0U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 1U, 0U, 16U, 1U);
    ZERO(0U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 1U, 16U, 1U);
    ZERO(0U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 1U);
    ZERO(0U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 16U, 0U);
    ZERO(0U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 0U, 16U, 1U);
#undef ZERO

#define DSM(cid, nsid, ctl, attr, ranges, llo, lhi, nlb, address, bytes, cb) \
    CHECK32(P(dsm_status)(cid, nsid, llo, lhi, nlb, ctl, attr, ranges,       \
                          address, 0U, 0U, 0U, bytes, cb),                   \
            O(dsm_status)(cid, nsid, llo, lhi, nlb, ctl, attr, ranges,       \
                          address, 0U, 0U, 0U, bytes, cb))
    DSM(0U, 2U, 0U, 0U, 1U, 0U, 0U, 0U, 0x1000U, 16U, 1U);
    DSM(0x10000U, 1U, 0U, 0U, 1U, 0U, 0U, 0U, 0x1000U, 16U, 1U);
    DSM(0U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, 0x1000U, 0U, 1U);
    DSM(0U, 1U, 0U, 0U, 257U, 0U, 0U, 0U, 0x1000U, 4112U, 1U);
    DSM(0U, 1U, 0U, 8U, 1U, 0U, 0U, 0U, 0x1000U, 16U, 1U);
    DSM(0U, 1U, 0U, 0U, 1U, 1U, 0U, 0U, 0x1000U, 16U, 1U);
    DSM(0U, 1U, 0U, 0U, 1U, 0U, 1U, 0U, 0x1000U, 16U, 1U);
    DSM(0U, 1U, 0U, 0U, 1U, 0U, 0U, 1U, 0x1000U, 16U, 1U);
    DSM(0U, 1U, 1U, 0U, 1U, 0U, 0U, 0U, 0x1000U, 16U, 1U);
    DSM(0U, 1U, 0U, 0U, 1U, 0U, 0U, 0U, 1U, 16U, 1U);
    DSM(0U, 1U, 0U, 0U, 1U, 0U, 0U, 0U, 0x1000U, 8U, 1U);
    DSM(0U, 1U, 0U, 0U, 1U, 0U, 0U, 0U, 0x1000U, 16U, 1U);
    DSM(0U, 1U, 0U, 4U, 1U, 0U, 0U, 0U, 0x1000U, 16U, 0U);
    DSM(0U, 1U, 0U, 4U, 1U, 0U, 0U, 0U, 0x1000U, 16U, 1U);
#undef DSM

    CHECK32(P(post_state)(0U), O(post_state)(0U));
    CHECK32(P(post_state)(1U), O(post_state)(1U));
    CHECK32(P(post_state)(2U), O(post_state)(2U));
    CHECK32(P(post_state)(3U), O(post_state)(3U));
    CHECK32(P(post_status)(0U), O(post_status)(0U));
    CHECK32(P(post_status)(1U), O(post_status)(1U));
    CHECK32(P(post_status)(2U), O(post_status)(2U));
    CHECK32(P(post_status)(3U), O(post_status)(3U));

#define SERVICE(p, r, w, f, low, high, block)                               \
    CHECK32(P(service_init_valid)(p, r, w, f, low, high, block),            \
            O(service_init_valid)(p, r, w, f, low, high, block))
    SERVICE(0U, 1U, 1U, 1U, 16U, 0U, 4096U);
    SERVICE(1U, 0U, 1U, 1U, 16U, 0U, 4096U);
    SERVICE(1U, 1U, 0U, 1U, 16U, 0U, 4096U);
    SERVICE(1U, 1U, 1U, 0U, 16U, 0U, 4096U);
    SERVICE(1U, 1U, 1U, 1U, 0U, 0U, 4096U);
    SERVICE(1U, 1U, 1U, 1U, 0U, 1U, 4096U);
    SERVICE(1U, 1U, 1U, 1U, 16U, 0U, 0U);
    SERVICE(1U, 1U, 1U, 1U, 16U, 0U, 4097U);
    SERVICE(1U, 1U, 1U, 1U, 16U, 0U, 4096U);
#undef SERVICE

#define DISPATCH(d, b, io, admin, iof, af)                                 \
    CHECK32(P(dispatch_init_valid)(d, b, io, admin, iof, af),               \
            O(dispatch_init_valid)(d, b, io, admin, iof, af))
    DISPATCH(0U, 1U, 1U, 1U, 0U, 0U);
    DISPATCH(1U, 0U, 1U, 1U, 0U, 0U);
    DISPATCH(1U, 1U, 0U, 1U, 0U, 0U);
    DISPATCH(1U, 1U, 1U, 0U, 0U, 0U);
    DISPATCH(1U, 1U, 1U, 1U, 1U, 0U);
    DISPATCH(1U, 1U, 1U, 1U, 0U, 1U);
    DISPATCH(1U, 1U, 1U, 1U, 0U, 0U);
#undef DISPATCH

#define QUEUE(q, n, sv, cq, cv)                                             \
    CHECK32(P(dispatch_queue_status)(q, n, sv, cq, cv),                     \
            O(dispatch_queue_status)(q, n, sv, cq, cv))
    QUEUE(0U, 1U, 1U, 1U, 1U);
    QUEUE(2U, 1U, 1U, 1U, 1U);
    QUEUE(5U, 5U, 1U, 1U, 1U);
    QUEUE(1U, 1U, 0U, 1U, 1U);
    QUEUE(1U, 1U, 1U, 0U, 1U);
    QUEUE(1U, 1U, 1U, 5U, 1U);
    QUEUE(1U, 1U, 1U, 1U, 0U);
    QUEUE(1U, 1U, 1U, 1U, 1U);
#undef QUEUE

#define ADDRS(data, spare, completion, report, error)                       \
    CHECK32(P(address_set_valid)(data, spare, completion, report, error),    \
            O(address_set_valid)(data, spare, completion, report, error))
    ADDRS(0U, 0x100U, 4U, 8U, 12U);
    ADDRS(0x4004U, 0x100U, 4U, 8U, 12U);
    ADDRS(0x4000U, 0U, 4U, 8U, 12U);
    ADDRS(0x4000U, 0x101U, 4U, 8U, 12U);
    ADDRS(0x4000U, 0x100U, 0U, 8U, 12U);
    ADDRS(0x4000U, 0x100U, 5U, 8U, 12U);
    ADDRS(0x4000U, 0x100U, 4U, 0U, 12U);
    ADDRS(0x4000U, 0x100U, 4U, 9U, 12U);
    ADDRS(0x4000U, 0x100U, 4U, 8U, 0U);
    ADDRS(0x4000U, 0x100U, 4U, 8U, 13U);
    ADDRS(0x4000U, 0x100U, 4U, 8U, 12U);
#undef ADDRS

#define SPAN(mp, cp, ns, bytes, tag, low, high, caplow, caphigh)             \
    CHECK32(P(command_span_status)(mp, cp, ns, bytes, tag, low, high,        \
                                    caplow, caphigh),                         \
            O(command_span_status)(mp, cp, ns, bytes, tag, low, high,        \
                                    caplow, caphigh))
    SPAN(0U, 1U, 1U, 4096U, 0U, 0U, 0U, 16U, 0U);
    SPAN(1U, 0U, 1U, 4096U, 0U, 0U, 0U, 16U, 0U);
    SPAN(1U, 1U, 2U, 4096U, 0U, 0U, 0U, 16U, 0U);
    SPAN(1U, 1U, 1U, 0U, 0U, 0U, 0U, 16U, 0U);
    SPAN(1U, 1U, 1U, 1U, 0U, 0U, 0U, 16U, 0U);
    SPAN(1U, 1U, 1U, 257U * 4096U, 0U, 0U, 0U, 1024U, 0U);
    SPAN(1U, 1U, 1U, 4096U, 128U, 0U, 0U, 16U, 0U);
    SPAN(1U, 1U, 1U, 4096U, 0U, 0xffffffffU, 0xffffffffU,
         0xffffffffU, 0xffffffffU);
    SPAN(1U, 1U, 1U, 4096U, 0U, 16U, 0U, 16U, 0U);
    SPAN(1U, 1U, 1U, 4096U, 0U, 15U, 0U, 16U, 0U);
#undef SPAN

#define ZSPAN(mp, cp, ns, bytes, tag, low, high, nlb, caplow, caphigh)       \
    CHECK32(P(zeroes_span_status)(mp, cp, ns, bytes, tag, low, high, nlb,   \
                                   caplow, caphigh),                          \
            O(zeroes_span_status)(mp, cp, ns, bytes, tag, low, high, nlb,   \
                                   caplow, caphigh))
    ZSPAN(0U, 1U, 1U, 0U, 0U, 0U, 0U, 0U, 16U, 0U);
    ZSPAN(1U, 0U, 1U, 0U, 0U, 0U, 0U, 0U, 16U, 0U);
    ZSPAN(1U, 1U, 2U, 0U, 0U, 0U, 0U, 0U, 16U, 0U);
    ZSPAN(1U, 1U, 1U, 1U, 0U, 0U, 0U, 0U, 16U, 0U);
    ZSPAN(1U, 1U, 1U, 0U, 0U, 0U, 0U, 0xffffffffU, 16U, 0U);
    ZSPAN(1U, 1U, 1U, 0U, 0U, 0U, 0U, 256U, 512U, 0U);
    ZSPAN(1U, 1U, 1U, 0U, 128U, 0U, 0U, 0U, 16U, 0U);
    ZSPAN(1U, 1U, 1U, 0U, 0U, 0xffffffffU, 0xffffffffU, 0U,
          0xffffffffU, 0xffffffffU);
    ZSPAN(1U, 1U, 1U, 0U, 0U, 16U, 0U, 0U, 16U, 0U);
    ZSPAN(1U, 1U, 1U, 0U, 0U, 15U, 0U, 0U, 16U, 0U);
#undef ZSPAN

    CHECK32(P(retry_limit)(0U), O(retry_limit)(0U));
    CHECK32(P(retry_limit)(9U), O(retry_limit)(9U));
    CHECK32(P(command_retry_limit)(4U, 4U),
            O(command_retry_limit)(4U, 4U));
    CHECK32(P(command_retry_limit)(0U, 4U),
            O(command_retry_limit)(0U, 4U));
    CHECK32(P(begin_status)(0U, 1U, 0U), O(begin_status)(0U, 1U, 0U));
    CHECK32(P(begin_status)(1U, 0U, 0U), O(begin_status)(1U, 0U, 0U));
    CHECK32(P(begin_status)(1U, 1U, 1U), O(begin_status)(1U, 1U, 1U));
    CHECK32(P(begin_status)(1U, 1U, 0U), O(begin_status)(1U, 1U, 0U));
    CHECK32(P(retry_terminal)(0, 0U, 3U), O(retry_terminal)(0, 0U, 3U));
    CHECK32(P(retry_terminal)(5, 0U, 3U), O(retry_terminal)(5, 0U, 3U));
    CHECK32(P(retry_terminal)(5, 2U, 3U), O(retry_terminal)(5, 2U, 3U));
    CHECK32(P(retry_terminal)(5, 0xffffffffU, 0U),
            O(retry_terminal)(5, 0xffffffffU, 0U));
    CHECK32(P(mapped_read_status)(0, 1U, 2U),
            O(mapped_read_status)(0, 1U, 2U));
    CHECK32(P(mapped_read_status)(0, 2U, 2U),
            O(mapped_read_status)(0, 2U, 2U));
    CHECK32(P(mapped_read_status)(5, 1U, 2U),
            O(mapped_read_status)(5, 1U, 2U));
    CHECK32(P(dma_offsets_valid)(0U, 0U), O(dma_offsets_valid)(0U, 0U));
    CHECK32(P(dma_offsets_valid)(256U, 0U), O(dma_offsets_valid)(256U, 0U));
    CHECK32(P(dma_offsets_valid)(0U, 4U), O(dma_offsets_valid)(0U, 4U));
    CHECK32(P(dma_offsets_valid)(255U, 3U), O(dma_offsets_valid)(255U, 3U));

#define ACTION(status, write, offset, count)                                \
    CHECK32(P(page_action)(status, write, offset, count),                   \
            O(page_action)(status, write, offset, count))
    ACTION(-1, 0U, 0U, 1U);
    ACTION(4U, 0U, 0U, 1U);
    ACTION(1U, 0U, 0U, 1U);
    ACTION(0U, 1U, 0U, 4U);
    ACTION(0U, 0U, 1U, 1U);
    ACTION(1U, 1U, 1U, 1U);
#undef ACTION

    CHECK32(P(page_count)(0U, 1U), O(page_count)(0U, 1U));
    CHECK32(P(page_count)(3U, 4U), O(page_count)(3U, 4U));
    CHECK32(P(page_count)(0U, 4U), O(page_count)(0U, 4U));
    CHECK32(P(dsm_range_valid)(1U, 1U, 0U, 16U, 0U),
            O(dsm_range_valid)(1U, 1U, 0U, 16U, 0U));
    CHECK32(P(dsm_range_valid)(0U, 0U, 0U, 16U, 0U),
            O(dsm_range_valid)(0U, 0U, 0U, 16U, 0U));
    CHECK32(P(dsm_range_valid)(0U, 1U, 0xffffffffffffffffULL,
                               0xffffffffU, 0xffffffffU),
            O(dsm_range_valid)(0U, 1U, 0xffffffffffffffffULL,
                               0xffffffffU, 0xffffffffU));
    CHECK32(P(dsm_range_valid)(0U, 2U, 15U, 16U, 0U),
            O(dsm_range_valid)(0U, 2U, 15U, 16U, 0U));
    CHECK32(P(dsm_range_valid)(0U, 1U, 15U, 16U, 0U),
            O(dsm_range_valid)(0U, 1U, 15U, 16U, 0U));

#define INIT(mp, fp, data, spare, completion, report, error)                \
    CHECK32(P(init_valid)(mp, fp, data, spare, completion, report, error),   \
            O(init_valid)(mp, fp, data, spare, completion, report, error))
    INIT(0U, 1U, 0x4000U, 0x100U, 4U, 8U, 12U);
    INIT(1U, 0U, 0x4000U, 0x100U, 4U, 8U, 12U);
    INIT(1U, 1U, 0U, 0x100U, 4U, 8U, 12U);
    INIT(1U, 1U, 0x4000U, 0x100U, 4U, 8U, 12U);
#undef INIT

#define DEALLOC(mp, cp, ns, attr, count, bytes, tag)                        \
    CHECK32(P(deallocate_valid)(mp, cp, ns, attr, count, bytes, tag),        \
            O(deallocate_valid)(mp, cp, ns, attr, count, bytes, tag))
    DEALLOC(0U, 1U, 1U, 4U, 1U, 16U, 0U);
    DEALLOC(1U, 0U, 1U, 4U, 1U, 16U, 0U);
    DEALLOC(1U, 1U, 2U, 4U, 1U, 16U, 0U);
    DEALLOC(1U, 1U, 1U, 0U, 1U, 16U, 0U);
    DEALLOC(1U, 1U, 1U, 12U, 1U, 16U, 0U);
    DEALLOC(1U, 1U, 1U, 4U, 0U, 0U, 0U);
    DEALLOC(1U, 1U, 1U, 4U, 257U, 4112U, 0U);
    DEALLOC(1U, 1U, 1U, 4U, 1U, 15U, 0U);
    DEALLOC(1U, 1U, 1U, 4U, 1U, 16U, 128U);
    DEALLOC(1U, 1U, 1U, 4U, 1U, 16U, 0U);
#undef DEALLOC

    CHECK32(P(chunk_bytes)(0U), O(chunk_bytes)(0U));
    CHECK32(P(chunk_bytes)(16384U), O(chunk_bytes)(16384U));
    CHECK32(P(chunk_bytes)(16385U), O(chunk_bytes)(16385U));
    CHECK32(P(full_page)(0U, 4U), O(full_page)(0U, 4U));
    CHECK32(P(full_page)(1U, 4U), O(full_page)(1U, 4U));
    CHECK32(P(full_page)(0U, 3U), O(full_page)(0U, 3U));

    if (parity_rows != EXPECTED_PARITY_ROWS) {
        fprintf(stderr, "frozen row count changed: %u != %u\n",
                parity_rows, EXPECTED_PARITY_ROWS);
        return 1;
    }
    printf("COSMOS_NVME_MEDIA_POLICY_PARITY_ROWS %u digest=%016llx\n",
           parity_rows, parity_digest);
    printf("COSMOS_NVME_MEDIA_POLICY_PARITY_INPUT_BINDING "
           "function-id+arity+runtime-values+result+row\n");
    return 0;
#undef P
#undef O
}
