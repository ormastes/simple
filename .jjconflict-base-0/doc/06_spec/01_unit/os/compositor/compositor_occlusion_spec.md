# Compositor Occlusion Specification

> Tests covering WS-D6 compositor occlusion culling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compositor Occlusion Specification

## Scenarios

### WS-D6 compositor occlusion culling

#### whole-framebuffer equivalence, chrome-only windows
_Every layout renders identically with and without culling._

#### two identical rects — NOT culled, the lower shadow still shows

- two identical rects — NOT culled, the lower shadow still shows
- the chrome drop shadow reaches past the covering rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("two identical rects — NOT culled, the lower shadow still shows")
step("the chrome drop shadow reaches past the covering rect")
_assert_identical([20, 16, 150, 110, 20, 16, 150, 110], false, 0)
```

</details>

#### strictly contained window — the cull case

- strictly contained window — the cull case
- upper window clears the lower one's shadow band too


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("strictly contained window — the cull case")
step("upper window clears the lower one's shadow band too")
_assert_identical([40, 40, 100, 60, 15, 12, 175, 130], false, 1)
```

</details>

#### covered by the UNION of two windows, by neither alone

- covered by the UNION of two windows, by neither alone
- exact region subtraction, not a bounding-box guess


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("covered by the UNION of two windows, by neither alone")
step("exact region subtraction, not a bounding-box guess")
_assert_identical([30, 25, 120, 90, 20, 15, 90, 115, 100, 15, 95, 115], false, 1)
```

</details>

#### partial overlap — must NOT be culled

- partial overlap — must NOT be culled
- a false cull here shows up as missing pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("partial overlap — must NOT be culled")
step("a false cull here shows up as missing pixels")
_assert_identical([10, 10, 120, 90, 60, 40, 120, 90], false, 0)
```

</details>

#### disjoint windows — nothing culled

- disjoint windows — nothing culled


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("disjoint windows — nothing culled")
_assert_identical([5, 5, 60, 45, 130, 95, 60, 45], false, 0)
```

</details>

#### occluder one pixel short of covering — must NOT be culled

- occluder one pixel short of covering — must NOT be culled
- off-by-one in the coverage test is caught whole-buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("occluder one pixel short of covering — must NOT be culled")
step("off-by-one in the coverage test is caught whole-buffer")
_assert_identical([30, 25, 120, 90, 30, 25, 120, 89], false, 0)
```

</details>

#### single window and empty desktop

- single window and empty desktop


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("single window and empty desktop")
_assert_identical([20, 20, 120, 90], false, 0)
_assert_identical([], false, 0)
```

</details>

#### whole-framebuffer equivalence, content-bearing windows
_PIXEL_SURFACE windows are the expensive path culling skips._

#### occluded pixel-surface window — the expensive cull

- occluded pixel-surface window — the expensive cull
- its per-pixel put_pixel blit is skipped entirely


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("occluded pixel-surface window — the expensive cull")
step("its per-pixel put_pixel blit is skipped entirely")
_assert_identical([40, 40, 100, 60, 15, 12, 175, 130], true, 1)
```

</details>

#### two stacked pixel-surface windows — NOT culled

- two stacked pixel-surface windows — NOT culled


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("two stacked pixel-surface windows — NOT culled")
_assert_identical([20, 16, 140, 100, 20, 16, 140, 100], true, 0)
```

</details>

#### pixel-surface window partially overlapping another

- pixel-surface window partially overlapping another


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("pixel-surface window partially overlapping another")
_assert_identical([10, 10, 120, 90, 50, 35, 120, 90], true, 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/compositor_occlusion_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WS-D6 compositor occlusion culling.
- WS-D6 compositor occlusion culling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `75948abaf83063887658dfa50f89a647629627ac9680cbe9a425a6e6e9d7654a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `75948abaf83063887658dfa50f89a647629627ac9680cbe9a425a6e6e9d7654a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `75948abaf83063887658dfa50f89a647629627ac9680cbe9a425a6e6e9d7654a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/compositor/compositor_occlusion_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/compositor_occlusion_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/compositor_occlusion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/compositor_occlusion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/compositor_occlusion_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two identical rects — NOT culled, the lower shadow still shows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/compositor_occlusion_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'strictly contained window — the cull case' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/compositor_occlusion_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covered by the UNION of two windows, by neither alone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
