# Multi Buffer Specification

> Tests covering MultiBufferManager.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multi Buffer Specification

## Scenarios

### MultiBufferManager

#### creates empty manager with zero buffers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates empty manager with zero buffers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty manager with zero buffers")
val mgr = multi_buffer_create()
val count = mgr.buffers.len()
expect count to_equal(0)
```

</details>

#### opens empty buffer and increments count

- opens empty buffer and increments count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opens empty buffer and increments count")
val mgr = multi_buffer_create()
multi_buffer_open_empty(mgr)
val count = mgr.buffers.len()
expect count to_equal(1)
```

</details>

#### finds buffer by id after opening

- finds buffer by id after opening


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds buffer by id after opening")
val mgr = multi_buffer_create()
val bid = multi_buffer_open_empty(mgr)
val doc = multi_buffer_get(mgr, bid)
val found = doc != nil
expect found to_equal(true)
```

</details>

#### reports dirty count correctly

- reports dirty count correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports dirty count correctly")
val mgr = multi_buffer_create()
multi_buffer_open_empty(mgr)
multi_buffer_open_empty(mgr)
val dirty = multi_buffer_dirty_count(mgr)
expect dirty to_equal(0)
```

</details>

#### opens multiple buffers

- opens multiple buffers


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opens multiple buffers")
val mgr = multi_buffer_create()
multi_buffer_open_empty(mgr)
multi_buffer_open_empty(mgr)
multi_buffer_open_empty(mgr)
val count = mgr.buffers.len()
expect count to_equal(3)
```

</details>

#### closes buffer reduces count

- closes buffer reduces count


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closes buffer reduces count")
val mgr = multi_buffer_create()
val bid = multi_buffer_open_empty(mgr)
multi_buffer_open_empty(mgr)
multi_buffer_close(mgr, bid)
val count = mgr.buffers.len()
expect count to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/editor/multi_buffer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MultiBufferManager.
- MultiBufferManager

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `30fcfdcc10f255237e1840c9b841af17429c1659622a539f97adbec464919f39`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `30fcfdcc10f255237e1840c9b841af17429c1659622a539f97adbec464919f39`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `30fcfdcc10f255237e1840c9b841af17429c1659622a539f97adbec464919f39`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/editor/multi_buffer_spec.spl
mirror: doc/06_spec/unit/lib/editor/multi_buffer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/editor/multi_buffer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/editor/multi_buffer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/editor/multi_buffer_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates empty manager with zero buffers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/editor/multi_buffer_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens empty buffer and increments count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/editor/multi_buffer_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds buffer by id after opening' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
