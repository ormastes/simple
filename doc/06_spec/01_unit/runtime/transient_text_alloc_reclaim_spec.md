# Transient text allocation is never reclaimed (parse-phase memory blowup reproducer)

> This is the in-the-small reproducer for `doc/08_tracking/bug/bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md` ("stage-4 self-host parse-phase memory blowup, ~160 MB per parsed file").

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transient text allocation is never reclaimed (parse-phase memory blowup reproducer)

This is the in-the-small reproducer for `doc/08_tracking/bug/bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md` ("stage-4 self-host parse-phase memory blowup, ~160 MB per parsed file").

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/transient_text_alloc_reclaim_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This is the in-the-small reproducer for
`doc/08_tracking/bug/bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`
("stage-4 self-host parse-phase memory blowup, ~160 MB per parsed file").

That bug has been chased for many sessions as *AST retention*. It is not:
`ast_reset()` (`src/compiler/10.frontend/core/_Ast/module_state.spl:453`) already
clears every arena pool **in place**, so the flat-array AST arenas are reused
across files and are bounded by the largest file, not by the corpus.

What is actually unbounded is one layer below: on the native/JIT lane there is
no GC and no refcounting, so **every transient heap value a loop allocates is
stranded for the life of the process**, even when nothing references it after
the iteration that made it. A parse allocates hundreds of thousands of
short-lived strings per file (token texts, interpolated diagnostics, flat
encodings), so the per-file RSS step falls straight out of this rate.

Measured 2026-08-17 with the deployed `bin/simple` (Rust bootstrap seed,
Cranelift `run` lane) over `test/fixture/mem_infra/transient_alloc_churn_workload.spl`:

| CHURN_N | VmRSS |
|---------|-------|
| 20,000  | 32,768 kB |
| 40,000  | 35,840 kB |
| 80,000  | 44,968 kB |
| 160,000 | 61,576 kB |
| 320,000 | 94,324 kB |

Dead linear: 205 B/iteration between 80k->160k and 205 B/iteration between
160k->320k. This is a **cost/retention defect, not a hang** — every run
terminates promptly (0.3-1.4 s wall).

## What this spec locks in

The slope, not the absolute RSS. The true target for a reclaiming runtime is
**0 bytes per iteration**; until the bug above is fixed the spec holds the
measured rate under a ceiling so it cannot silently get worse, and it fails
loudly rather than vacuously if the child never ran.

## Related Specifications

- test/01_unit/runtime/transient_alloc_reclaim_family_class_spec.spl — same
  method generalized to the array and dict allocation families
- test/01_unit/runtime/mem_attr_gate_spec.spl — per-owner attribution gate

## Scenarios

### Transient text allocation reclamation (stage-4 parse blowup reproducer)

#### does not strand more than the budgeted bytes per discarded string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not strand more than the budgeted bytes per discarded string
- Run the text-churn workload at N={SMALL_N} in a child process
- Run the same workload at N={LARGE_N} in a second child process
- Both children must have completed - a crashed or OOM-killed child proves nothing
- Both children must have reported a readable VmRSS - non-vacuity gate
- Bytes stranded per discarded string must stay under the ceiling


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("does not strand more than the budgeted bytes per discarded string")
step("Run the text-churn workload at N={SMALL_N} in a child process")
val (small_out, small_code) = run_churn(0, SMALL_N)

step("Run the same workload at N={LARGE_N} in a second child process")
val (large_out, large_code) = run_churn(0, LARGE_N)

step("Both children must have completed - a crashed or OOM-killed child proves nothing")
assert_equal(small_code, 0)
assert_equal(large_code, 0)
assert_equal(small_out.contains("CHURN_DONE"), true)
assert_equal(large_out.contains("CHURN_DONE"), true)

step("Both children must have reported a readable VmRSS - non-vacuity gate")
val small_kb = rss_kb_from(small_out)
val large_kb = rss_kb_from(large_out)
assert_equal(small_kb > 0, true)
assert_equal(large_kb > 0, true)

step("Bytes stranded per discarded string must stay under the ceiling")
val delta_bytes = (large_kb - small_kb) * 1024
val per_iter = delta_bytes / (LARGE_N - SMALL_N)
print "[reclaim] text: {small_kb} kB @ {SMALL_N} -> {large_kb} kB @ {LARGE_N} = {per_iter} B/iter (ceiling {TEXT_BYTES_PER_ITER_CEILING}, target 0)"
assert_equal(per_iter <= TEXT_BYTES_PER_ITER_CEILING, true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-RUNTIME-TRANSIENT-ALLOC-RECLAIM-001`
- `REQ-SSPEC-RUNTIME`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e0f5d5c9f4a2084cce65f7868c0c4d5e36289f49e144e28b1e818262758b6db4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e0f5d5c9f4a2084cce65f7868c0c4d5e36289f49e144e28b1e818262758b6db4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e0f5d5c9f4a2084cce65f7868c0c4d5e36289f49e144e28b1e818262758b6db4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/runtime/transient_text_alloc_reclaim_spec.spl
mirror: doc/06_spec/01_unit/runtime/transient_text_alloc_reclaim_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=89; blocker cap makes effective=49
doc/06_spec/01_unit/runtime/transient_text_alloc_reclaim_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/runtime/transient_text_alloc_reclaim_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/runtime/transient_text_alloc_reclaim_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/runtime/transient_text_alloc_reclaim_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not strand more than the budgeted bytes per discarded string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
