# Bare Bool Types Spec — Semantic Alias Pattern and Lint Level

> Tests the semantic alias pattern (D-4), predicate naming convention (D-1 spirit), and lint level for `bare_bool`:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bare Bool Types Spec — Semantic Alias Pattern and Lint Level

Tests the semantic alias pattern (D-4), predicate naming convention (D-1 spirit), and lint level for `bare_bool`:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | fix-bare-bool-suppressions |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/quality/code_quality/bare_bool_types_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the semantic alias pattern (D-4), predicate naming convention (D-1 spirit),
and lint level for `bare_bool`:

- Group 1: `build_default_levels` returns `"warn"` for `bare_bool` (not deny).
- Group 2: `type Enabled = bool` transparent alias round-trips correctly (D-4 pattern).
- Group 3: Predicate-prefix functions with non-bool params returning bool are
  semantically correct and match the D-1 spirit.

## Scenarios

### bare_bool lint — default level

#### AC-1a: build_default_levels returns warn for bare_bool

- AC-1a: query the live lint config API, not the source text
   - Expected: levels.get("bare_bool") ?? "" equals `warn`
   - Expected: levels.get("primitive_api") ?? "" equals `deny`
   - Expected: strict.get("bare_bool") ?? "" equals `warn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1a: query the live lint config API, not the source text")
val levels = build_default_levels()
expect(levels.get("bare_bool") ?? "").to_equal("warn")  # oracle: bare_bool stays advisory
expect(levels.get("primitive_api") ?? "").to_equal("deny")  # oracle: deny stays reserved for primitive_api
val strict = profile_default_levels(LintProfile.Strict)
expect(strict.get("bare_bool") ?? "").to_equal("warn")  # oracle: strict profile keeps bare_bool advisory, never deny
```

</details>

### bare_bool types — transparent alias pattern

#### AC-2a: transparent bool alias equals underlying bool true

- AC-2a: transparent bool alias equals underlying bool true
   - Expected: flag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2a: transparent bool alias equals underlying bool true")
type Enabled = bool
val flag: Enabled = true
expect(flag).to_equal(true)
```

</details>

#### AC-2b: transparent bool alias equals underlying bool false

- AC-2b: transparent bool alias equals underlying bool false
   - Expected: flag is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2b: transparent bool alias equals underlying bool false")
type Deleted = bool
val flag: Deleted = false
expect(flag).to_equal(false)
```

</details>

#### AC-2c: transparent bool alias can be negated like a bool

- AC-2c: transparent bool alias can be negated like a bool
   - Expected: b is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-2c: transparent bool alias can be negated like a bool")
type Active = bool
val a: Active = true
val b = not a
expect(b).to_equal(false)
```

</details>

### bare_bool types — predicate prefix convention

#### AC-3a: is_* fn with non-bool param can return bool

- AC-3a: is_* fn with non-bool param can return bool
   - Expected: is_above_threshold(150) is true
   - Expected: is_above_threshold(50) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3a: is_* fn with non-bool param can return bool")
fn is_above_threshold(value: i64) -> bool:
    value > 100
expect(is_above_threshold(150)).to_equal(true)
expect(is_above_threshold(50)).to_equal(false)
```

</details>

#### AC-3b: has_* fn with non-bool param can return bool

- AC-3b: has_* fn with non-bool param can return bool
   - Expected: has_content("hello") is true
   - Expected: has_content("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3b: has_* fn with non-bool param can return bool")
fn has_content(s: text) -> bool:
    s.len() > 0
expect(has_content("hello")).to_equal(true)
expect(has_content("")).to_equal(false)
```

</details>

#### AC-3c: can_* fn with no params can return bool

- AC-3c: can_* fn with no params can return bool
   - Expected: can_proceed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3c: can_* fn with no params can return bool")
fn can_proceed() -> bool:
    true
expect(can_proceed()).to_equal(true)
```

</details>

#### AC-3d: should_* fn with non-bool param can return bool

- AC-3d: should_* fn with non-bool param can return bool
   - Expected: should_retry(1) is true
   - Expected: should_retry(5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-3d: should_* fn with non-bool param can return bool")
fn should_retry(attempts: i64) -> bool:
    attempts < 3
expect(should_retry(1)).to_equal(true)
expect(should_retry(5)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `26fec68d0ffee3f666aff97eee985eeb8151d83e4ddcacfd1587c1d6f9d021a9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `26fec68d0ffee3f666aff97eee985eeb8151d83e4ddcacfd1587c1d6f9d021a9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `26fec68d0ffee3f666aff97eee985eeb8151d83e4ddcacfd1587c1d6f9d021a9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/quality/code_quality/bare_bool_types_spec.spl
mirror: doc/06_spec/03_system/quality/code_quality/bare_bool_types_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/quality/code_quality/bare_bool_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/quality/code_quality/bare_bool_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/quality/code_quality/bare_bool_types_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1a: build_default_levels returns warn for bare_bool' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/bare_bool_types_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2a: transparent bool alias equals underlying bool true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/bare_bool_types_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2b: transparent bool alias equals underlying bool false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
