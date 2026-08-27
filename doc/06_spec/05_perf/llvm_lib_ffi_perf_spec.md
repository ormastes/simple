# llvm_lib_ffi_perf_spec

> Purpose: measure the P0 (dlsym pointer caching) and P1 (scratch buffer vs

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# llvm_lib_ffi_perf_spec

Purpose: measure the P0 (dlsym pointer caching) and P1 (scratch buffer vs

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/llvm_lib_ffi_perf_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: measure the P0 (dlsym pointer caching) and P1 (scratch buffer vs
alloc/free) FFI optimization lanes against libLLVM's C API, with executed
read-back oracles proving the FFI surface used by the benchmarks is correct.
Audience: runtime/SFFI maintainers and the compiler performance owners.

## Scenarios

### LLVM-lib FFI Performance

<details>
<summary>Advanced: benchmarks scratch buffer vs alloc/free (P1)</summary>

#### benchmarks scratch buffer vs alloc/free (P1) _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- benchmarks scratch buffer vs alloc/free (P1)
   - Expected: scratch_readback_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("benchmarks scratch buffer vs alloc/free (P1)")
print ""
print "=== P1: Scratch Buffer vs Alloc/Free ==="
run_bench("P1/scratch_write_4", bench_scratch_write_4)
run_bench("P1/alloc_free_4", bench_alloc_free_4)
run_bench("P1/scratch_write_8", bench_scratch_write_8)
run_bench("P1/alloc_free_8", bench_alloc_free_8)
expect(scratch_readback_ok()).to_equal(true)  # oracle: pointer writes read back exactly through the same FFI surface the benches use
```

</details>


</details>

<details>
<summary>Advanced: benchmarks cached vs uncached FFI calls (P0)</summary>

#### benchmarks cached vs uncached FFI calls (P0) _(slow)_

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- benchmarks cached vs uncached FFI calls (P0)
   - Expected: _fp_ctx_create equals `0`
   - Expected: _fp_ctx_create != 0 and _fp_ctx_dispose != 0 is true
   - Expected: ffi_ctx_roundtrip_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("benchmarks cached vs uncached FFI calls (P0)")
val _llvm_ok = load_llvm()
if not _llvm_ok:
    print "[skip] libLLVM not available"
    expect(_fp_ctx_create).to_equal(0)  # oracle: an unavailable libLLVM leaves the cached pointers null (honest skip)
else:
    print ""
    print "=== P0: Cached vs Uncached FFI Calls ==="
    expect(_fp_ctx_create != 0 and _fp_ctx_dispose != 0).to_equal(true)  # oracle: dlsym resolved the LLVM C API entry points
    expect(ffi_ctx_roundtrip_ok()).to_equal(true)  # oracle: a context can really be created and disposed through the wffi call path
    run_bench("P0/cached_ctx_create_dispose", bench_cached_ctx)
    run_bench("P0/uncached_ctx_create_dispose", bench_uncached_ctx)
```

</details>


</details>

<details>
<summary>Advanced: benchmarks full IR gen cached vs uncached</summary>

#### benchmarks full IR gen cached vs uncached _(slow)_

**Manual warnings:**
- invalid capture metadata value: statistics (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- benchmarks full IR gen cached vs uncached
   - Expected: _llvm_handle equals `0`
   - Expected: _fp_build_add != 0 and _fp_build_ret != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("benchmarks full IR gen cached vs uncached")
var _llvm_ok2 = _llvm_handle != 0
if not _llvm_ok2:
    _llvm_ok2 = load_llvm()
if not _llvm_ok2:
    print "[skip] libLLVM not available"
    expect(_llvm_handle).to_equal(0)  # oracle: an unavailable libLLVM leaves no stale handle behind
else:
    print ""
    print "=== Full IR Generation: Cached vs Uncached ==="
    expect(_fp_build_add != 0 and _fp_build_ret != 0).to_equal(true)  # oracle: the IR-builder entry points resolved
    run_bench("full/cached_build_add_fn", bench_cached_build_fn)
    run_bench("full/uncached_build_add_fn", bench_uncached_build_fn)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cb21e116fe3dd9079f8fcc922181d26d0a386111661c5c224f54e602262ebe2e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cb21e116fe3dd9079f8fcc922181d26d0a386111661c5c224f54e602262ebe2e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cb21e116fe3dd9079f8fcc922181d26d0a386111661c5c224f54e602262ebe2e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/05_perf/llvm_lib_ffi_perf_spec.spl
mirror: doc/06_spec/05_perf/llvm_lib_ffi_perf_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/llvm_lib_ffi_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/llvm_lib_ffi_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
