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
  compares and vector tests on x64.
- Native integer comparison lowering now honors unsigned ordering for unsigned
  operands, which is required for `u64` collection counters and keys.
- Clean pushed-state benchmark evidence after rebuilding `simple-core` with
  `SIMPLE_NATIVE_CPU=native`, source-closure collection build enabled, and
  checksum parity:

```text
list_traverse     1.04x C / 0.84x Rust
list_push         1.31x C / 2.56x Rust
set_contains      1.86x C / 0.74x Rust
hashset_contains  0.65x C / 1.08x Rust
```

- The benchmark now clears the current warning floor with checksum parity after
  reducing pure Simple `HashSet` probe density and widening the numeric scan
  lowerings. This is not full C/Rust parity: `hashset_contains` remains below C
  throughput, and `list_traverse` plus `set_contains` remain below Rust
  throughput in the retained five-sample run.

## Prompt-to-artifact checklist

| Objective requirement | Current evidence | Status |
| --- | --- | --- |
| Commit, pull/rebase, push | Latest pushed commits through `f57dc5bf81`; `HEAD` and `origin/main` match in `/tmp/simple-parity-next` after fetch/rebase/push. | Done for current increments |
| Remove Rust from pure Simple path/runtime unless OS-provided | `nm -u build/perf/collections/collection_simple` lists libc/OS symbols and weak startup hooks only; no unresolved Rust runtime symbols. | Verified for collection benchmark binary |
| Port runtime support to pure Simple unless OS-provided | `build/simple-core/libsimple_runtime.a` provides the runtime helpers used by the collection benchmark; OS primitives remain `malloc`, `free`, `memcmp`, clocks, IO, and similar host services. | Verified for benchmark scope |
| Check common libraries that overlap C/Rust/native surfaces | This audit enumerates array, typed-array, generic indexing, list/set/hash/map, persistent, noalloc, and checksum/hash overlap surfaces. | In progress |
| Match or beat existing C/Rust performance for list/set/traverse and similar APIs | Latest retained benchmark beats C for `list_traverse`, `list_push`, and `set_contains`, beats Rust for `list_push` and `hashset_contains`, but trails Rust for `list_traverse`/`set_contains` and trails C for `hashset_contains`. | Not complete |

## Next optimization targets

1. Focus next on either matching C `hashset_contains` throughput or Rust
   `set_contains` throughput, because both still trail the fastest reference.
2. Keep typed scan work limited to verified regressions; current
   `list_traverse`, `list_push`, and numeric `set_contains` clear the C floor.
3. Benchmark `src/lib/*/examples/benchmarks/set_operations.spl`
   and representative `hashset`/`hashmap` Simple APIs against runtime/native
   equivalents after `hashset_contains` clears the C floor.
4. Keep rejected shortcuts documented; do not repeat raw-probe, short-string
   equality, split-vector contains, source-level unroll, or stale runtime-helper
   experiments without a new codegen reason.
