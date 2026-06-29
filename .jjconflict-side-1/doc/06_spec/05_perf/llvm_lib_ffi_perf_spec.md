# Llvm Lib Ffi Perf Specification

> <details>

<!-- sdn-diagram:id=llvm_lib_ffi_perf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_lib_ffi_perf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_lib_ffi_perf_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_lib_ffi_perf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Lib Ffi Perf Specification

## Scenarios

### LLVM-lib FFI Performance

<details>
<summary>Advanced: benchmarks scratch buffer vs alloc/free (P1)</summary>

#### benchmarks scratch buffer vs alloc/free (P1) _(slow)_

1. run bench
2. run bench
3. run bench
4. run bench
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
print ""
print "=== P1: Scratch Buffer vs Alloc/Free ==="
run_bench("P1/scratch_write_4", bench_scratch_write_4)
run_bench("P1/alloc_free_4", bench_alloc_free_4)
run_bench("P1/scratch_write_8", bench_scratch_write_8)
run_bench("P1/alloc_free_8", bench_alloc_free_8)
expect(true).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: benchmarks cached vs uncached FFI calls (P0)</summary>

#### benchmarks cached vs uncached FFI calls (P0) _(slow)_

1. run bench
2. run bench
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _llvm_ok = load_llvm()
if not _llvm_ok:
    print "[skip] libLLVM not available"
    expect(true).to_equal(true)
else:
    print ""
    print "=== P0: Cached vs Uncached FFI Calls ==="
    run_bench("P0/cached_ctx_create_dispose", bench_cached_ctx)
    run_bench("P0/uncached_ctx_create_dispose", bench_uncached_ctx)
    expect(true).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: benchmarks full IR gen cached vs uncached</summary>

#### benchmarks full IR gen cached vs uncached _(slow)_

1.  llvm ok2 = load llvm
   - Expected: true is true
2. run bench
3. run bench
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var _llvm_ok2 = _llvm_handle != 0
if not _llvm_ok2:
    _llvm_ok2 = load_llvm()
if not _llvm_ok2:
    print "[skip] libLLVM not available"
    expect(true).to_equal(true)
else:
    print ""
    print "=== Full IR Generation: Cached vs Uncached ==="
    run_bench("full/cached_build_add_fn", bench_cached_build_fn)
    run_bench("full/uncached_build_add_fn", bench_uncached_build_fn)
    expect(true).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/llvm_lib_ffi_perf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLVM-lib FFI Performance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
