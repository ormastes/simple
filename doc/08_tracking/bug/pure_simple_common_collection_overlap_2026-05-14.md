# Pure Simple common collection overlap audit

Date: 2026-05-14

## Purpose

Track the common collection surfaces that exist in both native/runtime support
and Simple libraries so parity work is aimed at real shared APIs, not only the
standalone collection benchmark.

## Runtime/native collection surface

The runtime symbol and FFI registries expose these collection families:

- Array: `rt_array_new`, `rt_array_new_with_cap_u64`, `rt_array_push`,
  `rt_array_get`, `rt_array_set`, `rt_array_pop`, `rt_array_clear`,
  `rt_array_len`, `rt_array_first`, `rt_array_last`, `rt_array_reverse`,
  `rt_array_sort`, `rt_array_data_ptr`, `rt_array_header_ptr`,
  `rt_array_set_len_known`.
- Generic indexing and membership: `rt_index_get`, `rt_index_set`,
  `rt_contains`, `rt_len`.
- Typed arrays: `rt_typed_bytes_*`, `rt_typed_words_u32_*`,
  `rt_typed_words_u64_*`, including unchecked/data-pointer/known-at push and
  store helpers.
- Native map/set families remain in runtime symbol space:
  `rt_hashmap_*`, `rt_hashset_*`, `rt_btreemap_*`, `rt_btreeset_*`.
- Numeric helper space includes `rt_numeric_*`; `rt_numeric_xor_sum_u64` was
  already tested as a traversal shortcut and rejected for this benchmark.

## Simple library overlap

Representative Simple collection files exist under these families:

- `src/lib/gc_async_mut/`: `array.spl`, `array_advanced.spl`,
  `package/list.spl`, `cache/set.spl`, `src/hash.spl`, `src/map.spl`,
  `src/set.spl`, `src/array_builder.spl`, and
  `src/collections/{btree,hashmap,hashset,mod,__init__}.spl`.
- `src/lib/nogc_async_mut/`: same array/list/map/set/hash/collections shape,
  plus `concurrent/collections.spl` and `examples/benchmarks/set_operations.spl`.
- `src/lib/nogc_sync_mut/`: same array/list/map/set/hash/collections shape,
  plus `examples/benchmarks/set_operations.spl`.
- `src/lib/nogc_async_immut/`: persistent collection implementations:
  `persistent_list`, `persistent_vec`, `persistent_map`, `persistent_set`,
  `persistent_sorted_map`, and `persistent_trie`.
- `src/lib/nogc_async_mut_noalloc/`: fixed-size/no-allocation collection
  implementations: `fixed_array`, `fixed_map`, `fixed_set`, `fixed_stack`,
  `linked_list`, and `ring_buffer`.
- `src/lib/common/hash/adler32.spl` overlaps with runtime/native checksum and
  hashing helpers.

## Current parity status

- Pure Simple native codegen now inlines typed array hot helpers and removes
  supported small local tail calls, including the benchmark's hot
  `set_contains` call.
- Native integer comparison lowering now honors unsigned ordering for unsigned
  operands, which is required for `u64` collection counters and keys.
- The collection benchmark still remains below C/Rust parity because
  `list_traverse` and `set_contains` are still scalar, non-unrolled scans.

## Next optimization targets

1. Add a real typed contiguous array scan loop transform for `u64` loops over
   `rt_array_data_ptr` plus `rt_typed_words_u64_raw_data_at`.
2. Reuse that transform for Simple library array/list traversal paths before
   adding runtime helper shortcuts.
3. After typed scans improve, benchmark `src/lib/*/examples/benchmarks/set_operations.spl`
   and representative `hashset`/`hashmap` Simple APIs against runtime/native
   equivalents.
4. Keep rejected shortcuts documented: source-level unroll rewrites and
   `rt_numeric_xor_sum_u64` substitution both preserved checksums but regressed
   speed in local probes.
