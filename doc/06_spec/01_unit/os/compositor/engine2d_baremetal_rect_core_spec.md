# Engine2d Baremetal Rect Core Specification

> Tests covering rect_core_draw_rect_filled w<=0/h<=0 guard, rect_core_draw_rect_filled clamp-then-exclude combinations, rect_core_clear delegates to rect_core_draw_rect_filled, rect_core_present.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Baremetal Rect Core Specification

## Scenarios

### rect_core_draw_rect_filled w<=0/h<=0 guard

#### w == 0 returns immediately (does not reach clamping or the extern call)

- w == 0 returns immediately (does not reach clamping or the extern call)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("w == 0 returns immediately (does not reach clamping or the extern call)")
rect_core_draw_rect_filled(10, 10, 0, 0, 0, 5, 0xFFFFFFFFu32)
assert_true(true)
```

</details>

#### w negative returns immediately

- w negative returns immediately


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("w negative returns immediately")
rect_core_draw_rect_filled(10, 10, 0, 0, -3, 5, 0xFFFFFFFFu32)
assert_true(true)
```

</details>

#### h == 0 returns immediately

- h == 0 returns immediately


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("h == 0 returns immediately")
rect_core_draw_rect_filled(10, 10, 0, 0, 5, 0, 0xFFFFFFFFu32)
assert_true(true)
```

</details>

#### h negative returns immediately

- h negative returns immediately


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("h negative returns immediately")
rect_core_draw_rect_filled(10, 10, 0, 0, 5, -3, 0xFFFFFFFFu32)
assert_true(true)
```

</details>

### rect_core_draw_rect_filled clamp-then-exclude combinations

#### x0<0 clamps to 0, while a fully out-of-range y excludes the rect (x1<=x0 branch untouched, y1<=y0 true)

- x0<0 clamps to 0, while a fully out-of-range y excludes the rect (x1<=x0 branch untouched, y1<=y0 true)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("x0<0 clamps to 0, while a fully out-of-range y excludes the rect (x1<=x0 branch untouched, y1<=y0 true)")
# width=10,height=10,x=-5,y=20,w=3,h=3
# x0=-5 -> clamp to 0 (x0<0 branch TRUE). y0=20 (y0<0 branch FALSE).
# x1=-5+3=-2 (x1>width FALSE, stays -2). y1=20+3=23 -> clamp to
# height=10 (y1>height branch TRUE).
# Exclusion check: x1(-2) <= x0(0) is TRUE -> returns before extern.
rect_core_draw_rect_filled(10, 10, -5, 20, 3, 3, 0xFF00FF00u32)
assert_true(true)
```

</details>

#### y0<0 clamps to 0, while a fully out-of-range x excludes the rect

- y0<0 clamps to 0, while a fully out-of-range x excludes the rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("y0<0 clamps to 0, while a fully out-of-range x excludes the rect")
# width=10,height=10,x=20,y=-5,w=3,h=3
# x0=20 (x0<0 FALSE). y0=-5 -> clamp to 0 (y0<0 branch TRUE).
# x1=23 -> clamp to width=10 (x1>width branch TRUE). y1=-5+3=-2
# (y1>height FALSE, stays -2).
# Exclusion check: x1(10) <= x0(20) is TRUE -> returns before extern.
rect_core_draw_rect_filled(10, 10, 20, -5, 3, 3, 0xFF00FF00u32)
assert_true(true)
```

</details>

#### x1>width clamps to width, combined with a fully out-of-range y excluding the rect

- x1>width clamps to width, combined with a fully out-of-range y excluding the rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("x1>width clamps to width, combined with a fully out-of-range y excluding the rect")
# width=10,height=10,x=20,y=0,w=5,h=5
# x0=20 (x0<0 FALSE). y0=0 (y0<0 FALSE).
# x1=25 -> clamp to width=10 (x1>width branch TRUE). y1=5
# (y1>height FALSE).
# Exclusion check: x1(10) <= x0(20) is TRUE -> returns before extern.
rect_core_draw_rect_filled(10, 10, 20, 0, 5, 5, 0xFF00FF00u32)
assert_true(true)
```

</details>

#### y1>height clamps to height, combined with a fully out-of-range x excluding the rect

- y1>height clamps to height, combined with a fully out-of-range x excluding the rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("y1>height clamps to height, combined with a fully out-of-range x excluding the rect")
# width=10,height=10,x=0,y=20,w=5,h=5
# x0=0, y0=20 (both clamp-guards FALSE for the 0-origin axis).
# x1=5 (x1>width FALSE). y1=25 -> clamp to height=10 (y1>height TRUE).
# Exclusion check: y1(10) <= y0(20) is TRUE -> returns before extern.
rect_core_draw_rect_filled(10, 10, 0, 20, 5, 5, 0xFF00FF00u32)
assert_true(true)
```

</details>

#### x1>width clamps while y1>height also clamps on the same call, and the rect is still excluded

- x1>width clamps while y1>height also clamps on the same call, and the rect is still excluded


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("x1>width clamps while y1>height also clamps on the same call, and the rect is still excluded")
# width=10,height=10,x=12,y=12,w=3,h=3
# x0=12 (x0<0 FALSE), y0=12 (y0<0 FALSE).
# x1=15 -> clamp to width=10 (x1>width branch TRUE).
# y1=15 -> clamp to height=10 (y1>height branch TRUE).
# Exclusion check: x1(10) <= x0(12) is TRUE -> returns before extern.
rect_core_draw_rect_filled(10, 10, 12, 12, 3, 3, 0xFF00FF00u32)
assert_true(true)
```

</details>

### rect_core_clear delegates to rect_core_draw_rect_filled

#### clearing a zero-width canvas is a no-op that returns before the extern call

- clearing a zero-width canvas is a no-op that returns before the extern call


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("clearing a zero-width canvas is a no-op that returns before the extern call")
rect_core_clear(0, 10, 0xFF000000u32)
assert_true(true)
```

</details>

#### clearing a zero-height canvas is a no-op that returns before the extern call

- clearing a zero-height canvas is a no-op that returns before the extern call


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("clearing a zero-height canvas is a no-op that returns before the extern call")
rect_core_clear(10, 0, 0xFF000000u32)
assert_true(true)
```

</details>

#### clearing a negative-height canvas is a no-op that returns before the extern call

- clearing a negative-height canvas is a no-op that returns before the extern call


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("clearing a negative-height canvas is a no-op that returns before the extern call")
rect_core_clear(10, -1, 0xFF000000u32)
assert_true(true)
```

</details>

### rect_core_present

#### runs without error (present is a documented no-op on this narrow core)

- runs without error (present is a documented no-op on this narrow core)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("runs without error (present is a documented no-op on this narrow core)")
rect_core_present()
assert_true(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/engine2d_baremetal_rect_core_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering rect_core_draw_rect_filled w<=0/h<=0 guard, rect_core_draw_rect_filled clamp-then-exclude combinations, rect_core_clear delegates to rect_core_draw_rect_filled, rect_core_present.
- rect_core_draw_rect_filled w<=0/h<=0 guard
- rect_core_draw_rect_filled clamp-then-exclude combinations
- rect_core_clear delegates to rect_core_draw_rect_filled
- rect_core_present

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `435c36757e5e9bed9ecfd80f8a93d874d2385edfbf929fb7ec9cdd394e2e6102`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `435c36757e5e9bed9ecfd80f8a93d874d2385edfbf929fb7ec9cdd394e2e6102`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `435c36757e5e9bed9ecfd80f8a93d874d2385edfbf929fb7ec9cdd394e2e6102`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/compositor/engine2d_baremetal_rect_core_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/engine2d_baremetal_rect_core_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/os/compositor/engine2d_baremetal_rect_core_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/engine2d_baremetal_rect_core_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/engine2d_baremetal_rect_core_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/01_unit/os/compositor/engine2d_baremetal_rect_core_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'w == 0 returns immediately (does not reach clamping or the extern call)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/engine2d_baremetal_rect_core_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'w negative returns immediately' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/engine2d_baremetal_rect_core_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'h == 0 returns immediately' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
