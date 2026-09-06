# Llvm Lib Ffi Perf Specification

> Tests covering LLVM-lib FFI Performance.

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual FFI performance evidence (expected show, folded, detail, or skip)


- warm up and time scratch-buffer vs alloc/free FFI patterns
   - Expected: rt_ptr_read_i64(probe, 0) equals `400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-FFI-BENCH
step("warm up and time scratch-buffer vs alloc/free FFI patterns")
print ""
print "=== P1: Scratch Buffer vs Alloc/Free ==="
run_bench("P1/scratch_write_4", bench_scratch_write_4)
run_bench("P1/alloc_free_4", bench_alloc_free_4)
run_bench("P1/scratch_write_8", bench_scratch_write_8)
run_bench("P1/alloc_free_8", bench_alloc_free_8)
# Real oracle: FFI pointer round-trip preserves a written value.
# oracle: 400 was just written at offset 0 of a freshly allocated block.
val probe = rt_alloc(8)
rt_ptr_write_i64(probe, 0, 400)
expect(rt_ptr_read_i64(probe, 0)).to_equal(400)
rt_free(probe)
```

</details>


</details>

<details>
<summary>Advanced: benchmarks cached vs uncached FFI calls (P0)</summary>

#### benchmarks cached vs uncached FFI calls (P0) _(slow)_

- load libLLVM and time cached vs uncached FFI calls
   - Expected: _llvm_handle > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-FFI-BENCH
step("load libLLVM and time cached vs uncached FFI calls")
val _llvm_ok = load_llvm()
if not _llvm_ok:
    print "[skip] libLLVM not available"
    expect(_llvm_ok).to_be_falsy()
else:
    print ""
    print "=== P0: Cached vs Uncached FFI Calls ==="
    run_bench("P0/cached_ctx_create_dispose", bench_cached_ctx)
    run_bench("P0/uncached_ctx_create_dispose", bench_uncached_ctx)
    # Real oracle: the benchmark executed against a live LLVM handle.
    expect(_llvm_handle > 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: benchmarks full IR gen cached vs uncached</summary>

#### benchmarks full IR gen cached vs uncached _(slow)_

- time full IR function generation, cached vs uncached
   - Expected: _llvm_handle > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-FFI-BENCH
step("time full IR function generation, cached vs uncached")
var _llvm_ok2 = _llvm_handle != 0
if not _llvm_ok2:
    _llvm_ok2 = load_llvm()
if not _llvm_ok2:
    print "[skip] libLLVM not available"
    expect(_llvm_ok2).to_be_falsy()
else:
    print ""
    print "=== Full IR Generation: Cached vs Uncached ==="
    run_bench("full/cached_build_add_fn", bench_cached_build_fn)
    run_bench("full/uncached_build_add_fn", bench_uncached_build_fn)
    # Real oracle: IR generation ran against a live LLVM handle.
    expect(_llvm_handle > 0).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
| Status | Active |
| Source | `test/perf/llvm_lib_ffi_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLVM-lib FFI Performance.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-PERF-FFI-BENCH`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `541ff05758876c8fa9d3eb7b241f9ae3a377af108a588ff67b6385d0d294a6de`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `541ff05758876c8fa9d3eb7b241f9ae3a377af108a588ff67b6385d0d294a6de`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `541ff05758876c8fa9d3eb7b241f9ae3a377af108a588ff67b6385d0d294a6de`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/perf/llvm_lib_ffi_perf_spec.spl
mirror: doc/06_spec/perf/llvm_lib_ffi_perf_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/llvm_lib_ffi_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/llvm_lib_ffi_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/llvm_lib_ffi_perf_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/llvm_lib_ffi_perf_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/perf/llvm_lib_ffi_perf_spec.spl:249:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'benchmarks scratch buffer vs alloc/free (P1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/llvm_lib_ffi_perf_spec.spl:265:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'benchmarks cached vs uncached FFI calls (P0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/llvm_lib_ffi_perf_spec.spl:280:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'benchmarks full IR gen cached vs uncached' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
