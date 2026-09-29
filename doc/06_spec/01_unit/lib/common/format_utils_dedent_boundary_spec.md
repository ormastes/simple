# `dedent` leaves an all-space string unchanged at the boundary where it should be emptied

> `dedent(text, spaces)` strips up to `spaces` leading space characters. The boundary guard was `i > 0 and i < text.len()`, so whenever the scan consumed every character in `text` (i.e. `i == text.len()`, e.g. the whole string is spaces and there are at least `spaces` of them, or `text` is shorter than `spaces` but entirely spaces) the function fell through to the `else` branch and returned the ORIGINAL unstripped text instead of the empty string. `text.substring(i, text.len())` with `i == text.len()` is a valid empty-range call, so the fix is simply to drop the redundant upper-bound check.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `dedent` leaves an all-space string unchanged at the boundary where it should be emptied

`dedent(text, spaces)` strips up to `spaces` leading space characters. The boundary guard was `i > 0 and i < text.len()`, so whenever the scan consumed every character in `text` (i.e. `i == text.len()`, e.g. the whole string is spaces and there are at least `spaces` of them, or `text` is shorter than `spaces` but entirely spaces) the function fell through to the `else` branch and returned the ORIGINAL unstripped text instead of the empty string. `text.substring(i, text.len())` with `i == text.len()` is a valid empty-range call, so the fix is simply to drop the redundant upper-bound check.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib / text formatting |
| Status | Active |
| Source | `test/01_unit/lib/common/format_utils_dedent_boundary_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`dedent(text, spaces)` strips up to `spaces` leading space characters. The
boundary guard was `i > 0 and i < text.len()`, so whenever the scan consumed
every character in `text` (i.e. `i == text.len()`, e.g. the whole string is
spaces and there are at least `spaces` of them, or `text` is shorter than
`spaces` but entirely spaces) the function fell through to the `else` branch
and returned the ORIGINAL unstripped text instead of the empty string.
`text.substring(i, text.len())` with `i == text.len()` is a valid empty-range
call, so the fix is simply to drop the redundant upper-bound check.

## Scenarios

### dedent boundary at i == text.len()

#### empties a string that is exactly `spaces` leading spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### empties a string shorter than `spaces` but entirely spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(dedent(" ", 5), "")
```

</details>

#### still strips a normal prefix, leaving the remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(dedent("    hello", 2), "  hello")
```

</details>

#### leaves a string with no leading spaces unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(dedent("hello", 2), "hello")
```

</details>

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

- Canonical SPipe generation for source `cade3439fe6e1c28001ba27c01bc096b4edff9ecdeb4fb54c0fe413816b5ce18`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cade3439fe6e1c28001ba27c01bc096b4edff9ecdeb4fb54c0fe413816b5ce18`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cade3439fe6e1c28001ba27c01bc096b4edff9ecdeb4fb54c0fe413816b5ce18`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/common/format_utils_dedent_boundary_spec.spl
mirror: doc/06_spec/01_unit/lib/common/format_utils_dedent_boundary_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/format_utils_dedent_boundary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/format_utils_dedent_boundary_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/format_utils_dedent_boundary_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/common/format_utils_dedent_boundary_spec.spl:30:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'empties a string that is exactly `spaces` leading spaces' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/format_utils_dedent_boundary_spec.spl:35:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'empties a string shorter than `spaces` but entirely spaces' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/format_utils_dedent_boundary_spec.spl:38:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'still strips a normal prefix, leaving the remainder' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/format_utils_dedent_boundary_spec.spl:41:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'leaves a string with no leading spaces unchanged' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
