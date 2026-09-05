# Toml Value Guard Specification

> Tests covering TOML value guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Toml Value Guard Specification

## Scenarios

### TOML value guards

#### keeps valid scalar values and inline comments

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps valid scalar values and inline comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid scalar values and inline comments")
val entries = toml_parse("name = \"ok\" # comment\nenabled = true\nport = 8080\n")
assert_equal(toml_get(entries, "name"), "ok")
assert_equal(toml_get_bool(entries, "enabled"), true)
assert_equal(toml_get_int(entries, "port"), 8080)
```

</details>

#### rejects trailing text after scalar values

- rejects trailing text after scalar values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects trailing text after scalar values")
val entries = toml_parse("name = \"ok\"junk\nenabled = truex\nport = 8080abc\n")
assert_equal(toml_get(entries, "name"), "")
assert_equal(toml_get_bool(entries, "enabled"), false)
assert_equal(toml_get_int(entries, "port"), 0)
```

</details>

#### rejects oversized integer values before conversion

- rejects oversized integer values before conversion


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects oversized integer values before conversion")
val entries = toml_parse("port = 9223372036854775808\nvalid = 9223372036854775807\n")
assert_equal(toml_get_int(entries, "port"), 0)
assert_equal(toml_get_int(entries, "valid"), 9223372036854775807)
```

</details>

#### rejects oversized negative integer values before conversion

- rejects oversized negative integer values before conversion


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects oversized negative integer values before conversion")
val entries = toml_parse("port = -9223372036854775808\nvalid = -9223372036854775807\n")
assert_equal(toml_get_int(entries, "port"), 0)
assert_equal(toml_get_int(entries, "valid"), -9223372036854775807)
```

</details>

#### rejects trailing text after arrays

- rejects trailing text after arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects trailing text after arrays")
val entries = toml_parse("items = [1, 2]junk\nvalid = [a, b]\n")
assert_equal(toml_get_array(entries, "items").len(), 0)
assert_equal(toml_get_array(entries, "valid").len(), 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/toml_value_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TOML value guards.
- TOML value guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `4a435fec57bf612a4e431b71fc82d5442a6139f582a9377cc92d67e85c95d75c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4a435fec57bf612a4e431b71fc82d5442a6139f582a9377cc92d67e85c95d75c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4a435fec57bf612a4e431b71fc82d5442a6139f582a9377cc92d67e85c95d75c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/encoding/toml_value_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/toml_value_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/toml_value_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/toml_value_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/toml_value_guard_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps valid scalar values and inline comments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/toml_value_guard_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects trailing text after scalar values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/toml_value_guard_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects oversized integer values before conversion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
