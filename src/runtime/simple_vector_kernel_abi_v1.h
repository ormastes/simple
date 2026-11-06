#ifndef SIMPLE_VECTOR_KERNEL_ABI_V1_H
#define SIMPLE_VECTOR_KERNEL_ABI_V1_H
#include <stdint.h>
#include <stddef.h>

/* Byte-wire ABI, never native struct packing. No pointers may outlive apply.
 * SHA256 of SIMPLE_VECTOR_ABI_DESCRIPTION, UTF-8, no terminating NUL/newline. */
#define SIMPLE_VECTOR_ABI_DESCRIPTION "SimpleVectorKernelsV1|SIMDKER1|LE|request:64:u32@0,u32@4,u64@8,u64@16,u64@24,u64@32,u64@40,u64@48,u64@56|response:24:u32@0,u32@4,u64@8,i64@16|ops:1=and-u32,2=or-u32,3=find-byte,4=find-crlf|status:0..6|call:i64(i64,i64,i64)|maxspan:1073741824|maxaddr:9223372036854775807|bitmap:align4,no-output-overlap,zero-null"
#define SIMPLE_VECTOR_ABI_SHA256 "f16901349e16de8bb16f0769f492488fff27d0d0bd3b5f15c20b20b25f060600"
#define SIMPLE_VECTOR_ABI_DIGEST_BYTES {0xf1,0x69,0x01,0x34,0x9e,0x16,0xde,0x8b,0xb1,0x6f,0x07,0x69,0xf4,0x92,0x48,0x8f,0xff,0x27,0xd0,0xd0,0xbd,0x3b,0x5f,0x15,0xc2,0x0b,0x20,0xb2,0x5f,0x06,0x06,0x00}
#define SIMPLE_VECTOR_KERNELS_V1_INTERFACE UINT64_C(6001412934163845681)
#define SIMPLE_VECTOR_REQUEST_V1_SIZE 64u
#define SIMPLE_VECTOR_RESPONSE_V1_SIZE 24u
#define SIMPLE_VECTOR_MAX_SPAN_BYTES UINT64_C(1073741824)
#define SIMPLE_VECTOR_MAX_ADDRESS UINT64_C(9223372036854775807)
enum simple_vector_opcode_v1 { SIMPLE_VECTOR_BITMAP_AND_U32=1, SIMPLE_VECTOR_BITMAP_OR_U32=2,
    SIMPLE_VECTOR_HTTP_FIND_BYTE=3, SIMPLE_VECTOR_HTTP_FIND_CRLF=4 };
/* Additive text extension. The v1 description/digest above are unchanged; a
 * host discovers text support by requesting SIMPLE_VECTOR_TEXT_CAPS at query
 * (a provider without it answers status 5) and keeps its scalar path then.
 * Request: input u64@8 + len u64@16; FIND/FIND_LAST needle @24/@32 (else 0);
 * UPPER/LOWER out @40, cap @48 == len, out == input or disjoint (else 0);
 * argument @56 == 0. Response i64@16 = result: VALIDATE/ASCII_CHECK 1|0,
 * FIND_INVALID/FIND/FIND_LAST byte offset|-1 (empty needle: 0 / len),
 * COUNT = non-continuation bytes; u64@8 = len for UPPER/LOWER. Empty spans
 * use address 0 like every v1 span. Opcode n is capability bit n-1. */
enum simple_vector_text_opcode_v1 { SIMPLE_VECTOR_TEXT_UTF8_VALIDATE=5,
    SIMPLE_VECTOR_TEXT_UTF8_FIND_INVALID=6, SIMPLE_VECTOR_TEXT_UTF8_COUNT=7,
    SIMPLE_VECTOR_TEXT_ASCII_CHECK=8, SIMPLE_VECTOR_TEXT_ASCII_UPPER=9,
    SIMPLE_VECTOR_TEXT_ASCII_LOWER=10, SIMPLE_VECTOR_TEXT_FIND=11,
    SIMPLE_VECTOR_TEXT_FIND_LAST=12 };
#define SIMPLE_VECTOR_TEXT_FIRST_OPCODE 5u
#define SIMPLE_VECTOR_TEXT_LAST_OPCODE 12u
#define SIMPLE_VECTOR_TEXT_CAPS UINT64_C(0xFF0)
enum simple_vector_status_v1 { SIMPLE_VECTOR_OK=0, SIMPLE_VECTOR_INVALID_REQUEST=1,
    SIMPLE_VECTOR_UNSUPPORTED_OPERATION=2, SIMPLE_VECTOR_CAPABILITY_DENIED=3,
    SIMPLE_VECTOR_RANGE_INVALID=4, SIMPLE_VECTOR_FEATURE_UNAVAILABLE=5,
    SIMPLE_VECTOR_EXECUTION_FAILED=6 };
typedef int32_t (*simple_vector_query_fn_v1)(uint64_t, uint64_t);
typedef int64_t (*simple_vector_apply_fn_v1)(int64_t, int64_t, int64_t);
static inline uint32_t simple_vector_rd32(const uint8_t *p) {
    return (uint32_t)p[0]|((uint32_t)p[1]<<8)|((uint32_t)p[2]<<16)|((uint32_t)p[3]<<24);
}
static inline uint64_t simple_vector_rd64(const uint8_t *p) {
    uint64_t v=0; for(unsigned i=0;i<8;i++) v|=(uint64_t)p[i]<<(8*i); return v;
}
static inline void simple_vector_wr32(uint8_t *p,uint32_t v) {
    for(unsigned i=0;i<4;i++) p[i]=(uint8_t)(v>>(8*i));
}
static inline void simple_vector_wr64(uint8_t *p,uint64_t v) {
    for(unsigned i=0;i<8;i++) p[i]=(uint8_t)(v>>(8*i));
}
#endif
