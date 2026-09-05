# Global Write Visible To Callee Specification

> Tests covering module global write is visible to a callee, module global write is visible across a module boundary, module global write-back on return still works.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Global Write Visible To Callee Specification

## Scenarios

### module global write is visible to a callee

#### scalar assignment is visible to a same-module callee

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- scalar assignment is visible to a same-module callee


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scalar assignment is visible to a same-module callee")
gwv_reset()
expect gwv_w_scalar() == 42
```

</details>

#### whole-array assignment is visible to a same-module callee

- whole-array assignment is visible to a same-module callee


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("whole-array assignment is visible to a same-module callee")
gwv_reset()
expect gwv_w_array() == 7
```

</details>

#### indexed assignment is visible to a same-module callee

- indexed assignment is visible to a same-module callee


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("indexed assignment is visible to a same-module callee")
gwv_reset()
expect gwv_w_indexed() == 55
```

</details>

<details>
<summary>Advanced: push loop growth is visible to a same-module callee</summary>

#### push loop growth is visible to a same-module callee

- push loop growth is visible to a same-module callee


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push loop growth is visible to a same-module callee")
gwv_reset()
expect gwv_w_push_loop() == 7
```

</details>


</details>

#### assignment nested in if/while is visible to a same-module callee

- assignment nested in if/while is visible to a same-module callee


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assignment nested in if/while is visible to a same-module callee")
gwv_reset()
expect gwv_w_nested_if() == 777
```

</details>

#### callee sees the write that precedes it, not the one that follows

- callee sees the write that precedes it, not the one that follows


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("callee sees the write that precedes it, not the one that follows")
gwv_reset()
expect gwv_w_midwrite() == 11
```

</details>

### module global write is visible across a module boundary

#### scalar assignment is visible to a callee in another module

- scalar assignment is visible to a callee in another module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scalar assignment is visible to a callee in another module")
gwv_reset()
expect gwv_w_scalar_xmod() == 43
```

</details>

#### whole-array assignment is visible to a callee in another module

- whole-array assignment is visible to a callee in another module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("whole-array assignment is visible to a callee in another module")
gwv_reset()
expect gwv_w_array_xmod() == 8
```

</details>

#### indexed assignment is visible to a callee in another module

- indexed assignment is visible to a callee in another module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("indexed assignment is visible to a callee in another module")
gwv_reset()
expect gwv_w_indexed_xmod() == 56
```

</details>

<details>
<summary>Advanced: push loop growth is visible to a callee in another module</summary>

#### push loop growth is visible to a callee in another module

- push loop growth is visible to a callee in another module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push loop growth is visible to a callee in another module")
gwv_reset()
expect gwv_w_push_loop_xmod() == 7
```

</details>


</details>

#### assignment nested in if/while is visible to a callee in another module

- assignment nested in if/while is visible to a callee in another module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assignment nested in if/while is visible to a callee in another module")
gwv_reset()
expect gwv_w_nested_if_xmod() == 778
```

</details>

### module global write-back on return still works

#### value written by a returned writer stays visible afterwards

- value written by a returned writer stays visible afterwards


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("value written by a returned writer stays visible afterwards")
gwv_reset()
gwv_w_then_return_n()
expect gwv_read_n() == 99
```

</details>

#### reset republishes the initial values

- reset republishes the initial values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reset republishes the initial values")
gwv_reset()
expect gwv_read_n() == 0
expect gwv_read_len() == 4
expect gwv_read_at(2) == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/global_write_visible_to_callee_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering module global write is visible to a callee, module global write is visible across a module boundary, module global write-back on return still works.
- module global write is visible to a callee
- module global write is visible across a module boundary
- module global write-back on return still works

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `7143c52e60723dbf1d57a545f8c87330b0e121c73ebd4abaffeb6c0080249a92`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7143c52e60723dbf1d57a545f8c87330b0e121c73ebd4abaffeb6c0080249a92`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7143c52e60723dbf1d57a545f8c87330b0e121c73ebd4abaffeb6c0080249a92`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/global_write_visible_to_callee_spec.spl
mirror: doc/06_spec/01_unit/compiler/global_write_visible_to_callee_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/global_write_visible_to_callee_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/global_write_visible_to_callee_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/global_write_visible_to_callee_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scalar assignment is visible to a same-module callee' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/global_write_visible_to_callee_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'whole-array assignment is visible to a same-module callee' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/global_write_visible_to_callee_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'indexed assignment is visible to a same-module callee' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
