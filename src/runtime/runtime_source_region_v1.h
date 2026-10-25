#ifndef SIMPLE_RUNTIME_SOURCE_REGION_V1_H
#define SIMPLE_RUNTIME_SOURCE_REGION_V1_H
#include <stdint.h>
/* Compiler-private scalar ABI. These declarations do not confer SOURCE
 * admission. Account reservations and descriptor provenance remain obligations
 * of the admitted compiler facade, never caller-authored certificates. */
int64_t rt_source_region_abi_v1(void);
int64_t rt_source_region_capabilities_v1(void);
int64_t rt_source_region_bound_v1(int64_t operation, int64_t descriptor,
    int64_t capacity, int64_t metric);
int64_t rt_source_region_create_v1(int64_t prepaid_work);
/* Birth-only, prepaid with create: operand must be the immediately returned
 * successful create token. Never expose this accessor to raw SOURCE calls. */
int64_t rt_source_region_created_generation_v1(int64_t born_control);
int64_t rt_source_region_allocation_prepare_v1(int64_t descriptor,
    int64_t capacity, int64_t prepaid_work);
int64_t rt_source_region_alloc_v1(int64_t control, int64_t generation,
    int64_t epoch, int64_t descriptor, int64_t capacity,
    int64_t prepared_revision, int64_t prepaid_work);
int64_t rt_source_region_generation_v1(int64_t control, int64_t prepaid_work);
int64_t rt_source_region_stamp_v1(int64_t control, int64_t generation,
    int64_t prepaid_work);
int64_t rt_source_region_read_begin_v1(int64_t control, int64_t generation,
    int64_t epoch, int64_t prepaid_work);
int64_t rt_source_region_read_end_v1(int64_t control, int64_t generation,
    int64_t lease, int64_t prepaid_work);
int64_t rt_source_region_write_begin_v1(int64_t control, int64_t generation,
    int64_t epoch, int64_t destination, int64_t slot, int64_t prepaid_work);
int64_t rt_source_region_write_commit_v1(int64_t control, int64_t generation,
    int64_t ticket, int64_t value_bits, int64_t prepaid_work);
int64_t rt_source_region_alias_write_v1(int64_t control, int64_t generation,
    int64_t destination, int64_t slot, int64_t value_bits, int64_t prepaid_work);
int64_t rt_source_region_close_v1(int64_t control, int64_t generation,
    int64_t prepaid_work);
int64_t rt_source_region_release_v1(int64_t control, int64_t generation,
    int64_t prepaid_work);

/* UNSAFE/compiler-private LIVE cleanup ABI. A positive integer, generation,
 * SourceRegionContextV1 object or live boolean is NOT a lifetime proof.
 * The compiler must prove birth -> owner-pinned borrows -> lease end -> one
 * release, with no escape/stored alias/copy-after-release. Each native attempt
 * consumes a separately prepaid credit, including an unsuccessful trylock.
 * Arbitrary/saved/freed tokens are invalid operands: these operations directly
 * dereference a genuinely retained control. Safe facade access stays gated on
 * the actual affine pin-verifier receipt. Native availability enables no such
 * authority, and this ABI must never be admitted as an ordinary raw SOURCE call.
 * Bound ops: 1 revoke=16, 2 read-end=24, 3 release=64 logical work units;
 * metrics 1 state fields / 2 bytes are zero. Metric 0 is work. */
int64_t rt_source_region_live_cleanup_bound_v1(int64_t operation, int64_t metric);
int64_t rt_source_region_revoke_live_v1(int64_t pinned_control,
    int64_t generation, int64_t prepaid_work);
int64_t rt_source_region_read_end_live_v1(int64_t pinned_control,
    int64_t generation, int64_t lease, int64_t prepaid_work);
int64_t rt_source_region_release_live_v1(int64_t pinned_control,
    int64_t generation, int64_t prepaid_work);
#endif
