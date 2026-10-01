# Sampled Guard-Page Allocator Gate (SIMPLE_MEM_GUARD_RATE)

> `SIMPLE_MEM_GUARD_RATE=N` (plan M2 §1-2, `src/compiler_rust/compiler/src/interpreter_extern/mem_guard.rs`) is a GWP-ASan-style sampled guard-page allocator layered onto the hosted `rt_alloc`/`rt_free` path: 1-in-N allocations land on their own `mmap`'d slot with unmapped guard pages, so a small overflow (or a use-after-free) traps instead of corrupting a neighbor. Unset/0 is the zero-overhead-when-off default — `mem_guard_should_sample` degenerates to a single cached `OnceLock<u64>` read.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sampled Guard-Page Allocator Gate (SIMPLE_MEM_GUARD_RATE)

`SIMPLE_MEM_GUARD_RATE=N` (plan M2 §1-2, `src/compiler_rust/compiler/src/interpreter_extern/mem_guard.rs`) is a GWP-ASan-style sampled guard-page allocator layered onto the hosted `rt_alloc`/`rt_free` path: 1-in-N allocations land on their own `mmap`'d slot with unmapped guard pages, so a small overflow (or a use-after-free) traps instead of corrupting a neighbor. Unset/0 is the zero-overhead-when-off default — `mem_guard_should_sample` degenerates to a single cached `OnceLock<u64>` read.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interp/mem_guard_rate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`SIMPLE_MEM_GUARD_RATE=N` (plan M2 §1-2,
`src/compiler_rust/compiler/src/interpreter_extern/mem_guard.rs`) is a
GWP-ASan-style sampled guard-page allocator layered onto the hosted
`rt_alloc`/`rt_free` path: 1-in-N allocations land on their own
`mmap`'d slot with unmapped guard pages, so a small overflow (or a
use-after-free) traps instead of corrupting a neighbor. Unset/0 is the
zero-overhead-when-off default — `mem_guard_should_sample` degenerates to a
single cached `OnceLock<u64>` read.

This spec locks in the three-part contract `mem_extern_parity_spec.spl`
leaves untested: the sampled count is exactly 0 with the gate unset (not
merely "non-negative"), it is non-zero once the gate is set, and at rate=1
every single allocation is sampled (an exact count, not just ">0").

## Key Concepts

| Concept | Description |
|---------|-------------|
| SIMPLE_MEM_GUARD_RATE | Env var gate; unset/`0` = disabled, `N` = 1-in-N sampling |
| rt_mem_guard_stats | Total hosted `rt_alloc` calls ever routed onto a guard slot |
| Deterministic sampling | `counter % rate == 0`, never `rand()` — rate=1 samples every call |

## Related Specifications

- test/01_unit/runtime/mem_extern_parity_spec.spl — sibling callable/sanity spec (no gate proof)
- doc/05_design/runtime/memory_analysis/m2_guard_and_harden_design.md

## Scenarios

### SIMPLE_MEM_GUARD_RATE sampled guard-page allocator

#### is disabled by default: the sampled count is exactly 0 in this process

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is disabled by default: the sampled count is exactly 0 in this process
- Query rt_mem_guard_stats() without SIMPLE_MEM_GUARD_RATE set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is disabled by default: the sampled count is exactly 0 in this process")
step("Query rt_mem_guard_stats() without SIMPLE_MEM_GUARD_RATE set")
val before = rt_mem_guard_stats()
assert_equal(before, 0)
```

</details>

#### stays at 0 across allocations while the gate is unset (zero-overhead-off)

- stays at 0 across allocations while the gate is unset (zero-overhead-off)
- Run 50 rt_alloc/rt_free cycles with no SIMPLE_MEM_GUARD_RATE set
- Confirm rt_mem_guard_stats() is still exactly 0 - nothing was sampled


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stays at 0 across allocations while the gate is unset (zero-overhead-off)")
step("Run 50 rt_alloc/rt_free cycles with no SIMPLE_MEM_GUARD_RATE set")
var i = 0
while i < ALLOC_COUNT:
    val p = rt_alloc(64)
    rt_free(p)
    i = i + 1

step("Confirm rt_mem_guard_stats() is still exactly 0 - nothing was sampled")
assert_equal(rt_mem_guard_stats(), 0)
```

</details>

#### samples every single allocation at rate=1 in a child process with SIMPLE_MEM_GUARD_RATE=1

- samples every single allocation at rate=1 in a child process with SIMPLE_MEM_GUARD_RATE=1
- Run the guard-rate workload fixture with SIMPLE_MEM_GUARD_RATE=1
- Confirm the child process exited cleanly
- Confirm the pre-sampling count was 0 and the post count equals the exact allocation count


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("samples every single allocation at rate=1 in a child process with SIMPLE_MEM_GUARD_RATE=1")
step("Run the guard-rate workload fixture with SIMPLE_MEM_GUARD_RATE=1")
val (out, err, code) = run_guard_workload_child()

step("Confirm the child process exited cleanly")
assert_equal(code, 0)
assert_equal(err.contains("unknown extern function"), false)

step("Confirm the pre-sampling count was 0 and the post count equals the exact allocation count")
val before = extract_field(out, "guard_rate_workload: before=")
val after = extract_field(out, "guard_rate_workload: after=")
assert_equal(before, 0)
assert_equal(after, ALLOC_COUNT)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-MEM-GUARD-RATE-001`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4cd48bf881c94757a1bd552c4ab2b539fe0274f4f5a2275e23e77d8a906a79a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4cd48bf881c94757a1bd552c4ab2b539fe0274f4f5a2275e23e77d8a906a79a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4cd48bf881c94757a1bd552c4ab2b539fe0274f4f5a2275e23e77d8a906a79a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/interp/mem_guard_rate_spec.spl
mirror: doc/06_spec/01_unit/compiler/interp/mem_guard_rate_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/interp/mem_guard_rate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interp/mem_guard_rate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interp/mem_guard_rate_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/interp/mem_guard_rate_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is disabled by default: the sampled count is exactly 0 in this process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interp/mem_guard_rate_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stays at 0 across allocations while the gate is unset (zero-overhead-off)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interp/mem_guard_rate_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'samples every single allocation at rate=1 in a child process with SIMPLE_MEM_GUARD_RATE=1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
