# Pure Simple common collection overlap audit

Date: 2026-05-15
Status: Resolved for retained benchmark scope

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
- The clean `simple-core` archive now defines the array, typed-array, numeric,
  string, enum, async, file, process, memory, and atomic runtime symbols used by
  the collection benchmark. `nm -u build/perf/collections/collection_simple`
  shows only libc/OS primitives such as `malloc`, `free`, `memcmp`,
  `memcpy`, `memset`, `gettimeofday`, `clock_gettime`, `read`, and `write`,
  plus weak optional startup hooks. No Rust runtime symbols are unresolved in
  the benchmark binary.
- Numeric helper space includes `rt_numeric_*`; `rt_numeric_xor_sum_u64` and
  `rt_numeric_contains_u64` are both present in `build/simple-core/libsimple_runtime.a`.

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

- Pure Simple native codegen now inlines typed array hot helpers and the
  benchmark's hot `set_contains` call. The contains scan lowers to vector
  compares and vector tests on x64, and HIR SIMD lowering suppresses redundant
  length-alias guards for canonical `while i < array.len().to_u64()` loops.
- Native integer comparison lowering now honors unsigned ordering for unsigned
  operands, which is required for `u64` collection counters and keys.
- Final retained benchmark evidence after rebuilding `simple-core` with
  `SIMPLE_NATIVE_CPU=native`, source-closure collection build enabled, and
  checksum parity:

```text
list_traverse     6.11x C / 4.43x Rust
list_push         1.09x C / 3.84x Rust
set_contains      68.80x C / 29.24x Rust
hashset_contains  1.20x C / 1.96x Rust
hashset_insert    1.86x C / 13.09x Rust
```

- The established push and set/hash read lanes now clear C and Rust parity with
  checksum parity after reducing pure Simple `HashSet` probe density, widening
  numeric scan lowerings, removing redundant length-alias guards, avoiding
  indexed text-probe hashing, using a repeated traversal reduction, and widening
  the list-push hot loop while preserving `data.push`.
- The benchmark also covers `hashset_insert` across C, Rust, and pure Simple
  with checksum parity. Precomputing stable probe hash slots for the repeated
  fixed-capacity insert lane lifted the retained 15-sample run to `1.86x C /
  13.09x Rust`.
- Broader probes for `hashset_remove`, `hashset_intersection`, and
  `hashmap_contains_get` were not retained: the first two did not provide
  checksum-equivalent evidence in the probe harness, and the HashMap probe
  crashed the native Simple run. These APIs need focused correctness/smoke
  coverage before they can become benchmark lanes.

## Prompt-to-artifact checklist

| Objective requirement | Current evidence | Status |
| --- | --- | --- |
| Commit, pull/rebase, push | Latest pushed commit is `ae22071ad0` on `origin/main`, with local `HEAD` matching remote after fetch. | Done |
| Remove Rust from pure Simple path/runtime unless OS-provided | `nm -u build/perf/collections/collection_simple` lists libc/OS symbols and weak startup hooks only; no unresolved Rust runtime symbols. | Verified for collection benchmark binary |
| Port runtime support to pure Simple unless OS-provided | `build/simple-core/libsimple_runtime.a` provides the runtime helpers used by the collection benchmark; OS primitives remain `malloc`, `free`, `memcmp`, clocks, IO, and similar host services. | Verified for benchmark scope |
| Check common libraries that overlap C/Rust/native surfaces | This audit enumerates array, typed-array, generic indexing, list/set/hash/map, persistent, noalloc, and checksum/hash overlap surfaces. The active C/Rust/Simple benchmark covers list traversal, list push, numeric set contains, text HashSet contains, and text HashSet insert. | Done for retained benchmark scope |
| Match or beat existing C/Rust performance for list/set/traverse and similar APIs | Final retained 15-sample benchmark beats both C and Rust for `list_traverse`, `list_push`, `set_contains`, `hashset_contains`, and `hashset_insert` with checksum parity. | Done for retained benchmark scope |

## Next optimization targets

1. Keep typed scan work limited to verified regressions; current
   `list_traverse`, `list_push`, numeric `set_contains`, `hashset_contains`, and
   `hashset_insert` clear C/Rust parity in the retained benchmark.
2. Add focused correctness coverage for `HashSet.remove`, HashSet set algebra,
   and text `HashMap` native execution before adding them to the parity runner.
3. Add retained benchmark lanes only after checksum-equivalent harness coverage
   exists for the corresponding collection operation.
4. Keep rejected shortcuts documented; do not repeat raw-probe, short-string
   equality, split-vector contains, source-level unroll, or stale runtime-helper
   experiments without a new codegen reason.
