# Transient heap reclamation — allocation-family class detector

> Class generalization of `test/01_unit/runtime/transient_text_alloc_reclaim_spec.spl`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transient heap reclamation — allocation-family class detector

Class generalization of `test/01_unit/runtime/transient_text_alloc_reclaim_spec.spl`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/transient_alloc_reclaim_family_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Class generalization of
`test/01_unit/runtime/transient_text_alloc_reclaim_spec.spl`.

The defect class is: **a heap allocation family whose short-lived values are
never reclaimed on the native/JIT lane**, so any bounded loop over that family
grows RSS linearly and forever. The text family is the one that shows up in
`doc/08_tracking/bug/bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`
because a parse is string-heavy, but nothing about the mechanism is specific to
strings — it is the absence of GC/refcounting for `rt_core_*` heap objects, and
it therefore applies to every family equally.

Measured 2026-08-17, deployed `bin/simple` (Rust bootstrap seed), `run` lane
with `SIMPLE_EXECUTION_MODE=jit`, over
`test/fixture/mem_infra/transient_alloc_churn_workload.spl`, N = 50,000 vs
200,000:

| family | VmRSS @50k | VmRSS @200k | bytes / iteration |
|--------|-----------|-------------|-------------------|
| text   | 37,836 kB | 63,584 kB   | ~176 |
| array  | 33,356 kB | 44,284 kB   | ~75  |
| dict   | 38,272 kB | 63,296 kB   | ~171 |

All three leak. None of the three is bounded. The target for every row is
**0 bytes per iteration**.

## Why a class spec and not three copies of the reproducer

A fix for one family (for instance an interning table for strings, which is
what `rt_string_new_literal` did in 2026-07-24) moves that one row and leaves
the others exactly where they were. This spec fails when **any** family
regresses past its ceiling, so a family-local fix cannot be mistaken for a
class-level one, and a newly added family that leaks worse than the existing
ones is caught rather than being discovered by a 64 GB bootstrap.

## Engine-divergence note (this is the seed-vs-self-host contrast, in miniature)

The same workload under `SIMPLE_EXECUTION_MODE=interpreter` measures ~31
B/iteration for the text family versus ~222 under `=jit` — the tree-walk
interpreter's values are Rust-owned and dropped, the JIT's are not. That is
the same shape as the bug doc's headline contrast (seed-compiled stage-4 flat
at ~90 MB, self-host-compiled stage-4 at ~160 MB/file). Every child here
therefore **pins** the execution mode; an inherited mode would make this spec
report which lane ran rather than whether the runtime reclaims.

## Related Specifications

- test/01_unit/runtime/transient_text_alloc_reclaim_spec.spl — the reproducer
- test/01_unit/runtime/mem_attr_gate_spec.spl — per-owner attribution gate

## Scenarios

### Transient heap reclamation across allocation families

#### keeps the text family's stranded bytes per iteration under its ceiling

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the text family's stranded bytes per iteration under its ceiling
- Measure the text-churn slope across two child processes
- The measurement must be real - a failed child is not a pass
- Slope must stay under the text ceiling


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("keeps the text family's stranded bytes per iteration under its ceiling")
step("Measure the text-churn slope across two child processes")
val rate = bytes_per_iter(0)
print "[reclaim-class] text: {rate} B/iter (ceiling {TEXT_CEILING}, target 0)"

step("The measurement must be real - a failed child is not a pass")
assert_equal(rate >= 0, true)

step("Slope must stay under the text ceiling")
assert_equal(rate <= TEXT_CEILING, true)
```

</details>

#### keeps the array family's stranded bytes per iteration under its ceiling

- keeps the array family's stranded bytes per iteration under its ceiling
- Measure the array-churn slope across two child processes
- The measurement must be real - a failed child is not a pass
- Slope must stay under the array ceiling


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("keeps the array family's stranded bytes per iteration under its ceiling")
step("Measure the array-churn slope across two child processes")
val rate = bytes_per_iter(1)
print "[reclaim-class] array: {rate} B/iter (ceiling {ARRAY_CEILING}, target 0)"

step("The measurement must be real - a failed child is not a pass")
assert_equal(rate >= 0, true)

step("Slope must stay under the array ceiling")
assert_equal(rate <= ARRAY_CEILING, true)
```

</details>

#### keeps the dict family's stranded bytes per iteration under its ceiling

- keeps the dict family's stranded bytes per iteration under its ceiling
- Measure the dict-churn slope across two child processes
- The measurement must be real - a failed child is not a pass
- Slope must stay under the dict ceiling


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("keeps the dict family's stranded bytes per iteration under its ceiling")
step("Measure the dict-churn slope across two child processes")
val rate = bytes_per_iter(2)
print "[reclaim-class] dict: {rate} B/iter (ceiling {DICT_CEILING}, target 0)"

step("The measurement must be real - a failed child is not a pass")
assert_equal(rate >= 0, true)

step("Slope must stay under the dict ceiling")
assert_equal(rate <= DICT_CEILING, true)
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
- `REQ-RUNTIME-TRANSIENT-ALLOC-RECLAIM-002`
- `REQ-SSPEC-RUNTIME`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a0629d37c409fdf4dd327f9893d2274b76fcf62e8aa1a1d7d90a77e014d781fc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a0629d37c409fdf4dd327f9893d2274b76fcf62e8aa1a1d7d90a77e014d781fc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a0629d37c409fdf4dd327f9893d2274b76fcf62e8aa1a1d7d90a77e014d781fc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/runtime/transient_alloc_reclaim_family_class_spec.spl
mirror: doc/06_spec/01_unit/runtime/transient_alloc_reclaim_family_class_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/runtime/transient_alloc_reclaim_family_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/runtime/transient_alloc_reclaim_family_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/runtime/transient_alloc_reclaim_family_class_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/runtime/transient_alloc_reclaim_family_class_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the text family's stranded bytes per iteration under its ceiling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/transient_alloc_reclaim_family_class_spec.spl:150:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the array family's stranded bytes per iteration under its ceiling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/transient_alloc_reclaim_family_class_spec.spl:163:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the dict family's stranded bytes per iteration under its ceiling' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
