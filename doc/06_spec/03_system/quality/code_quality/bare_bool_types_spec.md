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
| Updated | 2026-08-26 |
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

- AC-1a: build_default_levels returns warn for bare_bool
   - Expected: source contains `levels["bare_bool"] = "warn"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1a: build_default_levels returns warn for bare_bool")
val source = rt_file_read_text("src/compiler/90.tools/lint/_LintMain/config_and_model.spl")
expect(source.contains("levels[\"bare_bool\"] = \"warn\"")).to_equal(true)
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

- Canonical SPipe generation for source `d35b08868561295b982b0b7dbc83d4dd30d263b02da9af1c1b350dee3acf2e08`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d35b08868561295b982b0b7dbc83d4dd30d263b02da9af1c1b350dee3acf2e08`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d35b08868561295b982b0b7dbc83d4dd30d263b02da9af1c1b350dee3acf2e08`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/quality/code_quality/bare_bool_types_spec.spl
mirror: doc/06_spec/03_system/quality/code_quality/bare_bool_types_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/quality/code_quality/bare_bool_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/quality/code_quality/bare_bool_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/quality/code_quality/bare_bool_types_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/quality/code_quality/bare_bool_types_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1a: build_default_levels returns warn for bare_bool' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/bare_bool_types_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2a: transparent bool alias equals underlying bool true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/bare_bool_types_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2b: transparent bool alias equals underlying bool false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
