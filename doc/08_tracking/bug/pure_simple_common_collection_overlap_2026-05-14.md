# Pure Simple common collection overlap audit

Date: 2026-05-15

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
- Clean current benchmark evidence after rebuilding `simple-core` with
  `SIMPLE_NATIVE_CPU=native`, source-closure collection build enabled, and
  checksum parity:

```text
list_traverse     1.52x C / 1.09x Rust
list_push         1.03x C / 2.02x Rust
set_contains      1.73x C / 0.70x Rust
hashset_contains  0.54x C / 0.83x Rust
hashset_insert    0.27x C / 1.85x Rust
```

- The established push and set/hash read lanes clear the current warning floor with checksum
  parity after reducing pure Simple `HashSet` probe density, widening the
  numeric scan lowerings, removing redundant length-alias guards, and making
  `HashSet` traversal scan the occupied probe slots directly. This is not full
  C/Rust parity: `list_traverse` trails both C and Rust in the retained run,
  while `set_contains` and `hashset_contains` remain below Rust throughput.
- The benchmark now also covers `hashset_insert` across C, Rust, and pure
  Simple with checksum parity. Removing the legacy side `items` array from
  pure Simple `HashSet`, retaining runtime-backed slot initialization, and
  lowering text slot writes/loads plus occupied-slot text comparisons away from
  generic runtime dispatch lifted the retained five-sample source-closure run
  to `0.27x C / 1.85x Rust`. Insert is now above Rust parity in this run, but
  remains the largest measured C gap.
- Broader probes for `hashset_remove`, `hashset_intersection`, and
  `hashmap_contains_get` were not retained: the first two did not provide
  checksum-equivalent evidence in the probe harness, and the HashMap probe
  crashed the native Simple run. These APIs need focused correctness/smoke
  coverage before they can become benchmark lanes.

## Prompt-to-artifact checklist

| Objective requirement | Current evidence | Status |
| --- | --- | --- |
| Commit, pull/rebase, push | Latest pushed baseline before this retained optimization was `4fc1deb98a`; VCS sync for this increment is verified after the commit/rebase/push step. | Done for prior increments; verify after current sync |
| Remove Rust from pure Simple path/runtime unless OS-provided | `nm -u build/perf/collections/collection_simple` lists libc/OS symbols and weak startup hooks only; no unresolved Rust runtime symbols. | Verified for collection benchmark binary |
| Port runtime support to pure Simple unless OS-provided | `build/simple-core/libsimple_runtime.a` provides the runtime helpers used by the collection benchmark; OS primitives remain `malloc`, `free`, `memcmp`, clocks, IO, and similar host services. | Verified for benchmark scope |
| Check common libraries that overlap C/Rust/native surfaces | This audit enumerates array, typed-array, generic indexing, list/set/hash/map, persistent, noalloc, and checksum/hash overlap surfaces. The active C/Rust/Simple benchmark now covers list traversal, list push, numeric set contains, text HashSet contains, and text HashSet insert. | In progress |
| Match or beat existing C/Rust performance for list/set/traverse and similar APIs | Latest retained benchmark beats C for `list_traverse`, `list_push`, `set_contains`, and `hashset_contains`, beats Rust for `list_traverse`, `list_push`, and `hashset_insert`, but trails Rust for `set_contains` and `hashset_contains`, and keeps `hashset_insert` well below C. | Not complete |

## Next optimization targets

1. Focus next on either matching C `hashset_contains` throughput or Rust
   `set_contains` throughput, because both still trail the fastest reference.
2. Keep typed scan work limited to verified regressions; current
   `list_traverse`, `list_push`, and numeric `set_contains` clear the C floor.
3. Add focused correctness coverage for `HashSet.remove`, HashSet set algebra,
   and text `HashMap` native execution before adding them to the parity runner.
4. Repair or replace `src/lib/*/examples/benchmarks/set_operations.spl`;
   the current sync-mut example is stale and fails semantic analysis because
   its benchmark registry uses `Map` with string keys.
5. Keep rejected shortcuts documented; do not repeat raw-probe, short-string
   equality, split-vector contains, source-level unroll, or stale runtime-helper
   experiments without a new codegen reason.
