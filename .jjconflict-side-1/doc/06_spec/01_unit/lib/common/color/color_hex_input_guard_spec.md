# Color Hex Input Guard Specification

> Tests covering color hex input guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Color Hex Input Guard Specification

## Scenarios

### color hex input guards

#### keeps valid shorthand color parsing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps valid shorthand color parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid shorthand color parsing")
val c = from_hex("#F0A")
assert_equal(c.r, 255)
assert_equal(c.g, 0)
assert_equal(c.b, 170)
```

</details>

#### keeps valid full color parsing

- keeps valid full color parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid full color parsing")
val c = from_hex("#8040C0")
assert_equal(c.r, 128)
assert_equal(c.g, 64)
assert_equal(c.b, 192)
```

</details>

#### rejects invalid shorthand characters instead of partial parsing

- rejects invalid shorthand characters instead of partial parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid shorthand characters instead of partial parsing")
val c = from_hex("#F0G")
assert_equal(c.r, 0)
assert_equal(c.g, 0)
assert_equal(c.b, 0)
```

</details>

#### rejects invalid full color characters instead of coercing nibbles

- rejects invalid full color characters instead of coercing nibbles


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid full color characters instead of coercing nibbles")
val c = from_hex("#12Z456")
assert_equal(c.r, 0)
assert_equal(c.g, 0)
assert_equal(c.b, 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/color/color_hex_input_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering color hex input guards.
- color hex input guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `1aad686fa212fa47588dcf93cc96af22e87b05154299b3159242dbfbb1ca84e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1aad686fa212fa47588dcf93cc96af22e87b05154299b3159242dbfbb1ca84e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1aad686fa212fa47588dcf93cc96af22e87b05154299b3159242dbfbb1ca84e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/color/color_hex_input_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/color/color_hex_input_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/color/color_hex_input_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/color/color_hex_input_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/color/color_hex_input_guard_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps valid shorthand color parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/color/color_hex_input_guard_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps valid full color parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/color/color_hex_input_guard_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid shorthand characters instead of partial parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
