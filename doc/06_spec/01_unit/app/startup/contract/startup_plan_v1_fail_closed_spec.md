# Startup Plan V1 Fail Closed Specification

> Tests covering truncation vectors fail closed, malformed and wrong-version records fail closed, positive control — the decoder is not rejecting everything.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Startup Plan V1 Fail Closed Specification

## Scenarios

### truncation vectors fail closed

#### rejects an empty record

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects an empty record


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty record")
val d = startup_plan_decode("")
assert_false(d.ok)
assert_eq(d.error_kind, startup_plan_error_truncated())
assert_eq(d.plan.route_kind, "")
```

</details>

#### rejects a record cut to the version line only

- rejects a record cut to the version line only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a record cut to the version line only")
val d = startup_plan_decode("startup_plan: v1\n")
assert_false(d.ok)
assert_eq(d.error_kind, startup_plan_error_truncated())
```

</details>

#### rejects a record cut mid-field

- rejects a record cut mid-field


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a record cut mid-field")
val full = valid_text()
val d = startup_plan_decode(full.substring(0, 40))
assert_false(d.ok)
assert_eq(d.error_kind, startup_plan_error_truncated())
```

</details>

#### rejects a record whose hash value is cut short

- rejects a record whose hash value is cut short


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a record whose hash value is cut short")
val full = valid_text()
val d = startup_plan_decode(full.substring(0, full.len() - 2))
assert_false(d.ok)
assert_eq(d.error_kind, startup_plan_error_hash())
```

</details>

#### rejects a record missing the plan_hash line

- rejects a record missing the plan_hash line


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a record missing the plan_hash line")
val d = startup_plan_decode(drop_line(valid_text(), "plan_hash"))
assert_false(d.ok)
assert_eq(d.error_kind, startup_plan_error_truncated())
```

</details>

#### rejects a record whose last key is itself truncated

- rejects a record whose last key is itself truncated


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a record whose last key is itself truncated")
val d = startup_plan_decode(
    drop_line(valid_text(), "plan_hash") + "plan_h\n")
assert_false(d.ok)
assert_eq(d.error_kind, startup_plan_error_truncated())
```

</details>

#### rejects a record missing an interior field

- rejects a record missing an interior field


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a record missing an interior field")
val d = startup_plan_decode(drop_line(valid_text(), "load_policy"))
assert_false(d.ok)
assert_eq(d.error_kind, startup_plan_error_truncated())
```

</details>

#### rejects a record missing the version header

- rejects a record missing the version header


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a record missing the version header")
val d = startup_plan_decode(drop_line(valid_text(), "startup_plan"))
assert_false(d.ok)
assert_eq(d.error_kind, startup_plan_error_truncated())
```

</details>

### malformed and wrong-version records fail closed

#### rejects a wrong-version record

- rejects a wrong-version record


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a wrong-version record")
val bad = valid_text().replace("startup_plan: v1",
    "startup_plan: v2")
val d = startup_plan_decode(bad)
assert_false(d.ok)
assert_eq(d.error_kind, startup_plan_error_version())
assert_eq(d.plan.command_id, "")
```

</details>

#### rejects an unknown key in a frozen slot

- rejects an unknown key in a frozen slot


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown key in a frozen slot")
val bad = valid_text().replace("target_id:", "target_ident:")
val d = startup_plan_decode(bad)
assert_false(d.ok)
assert_eq(d.error_kind, startup_plan_error_malformed())
```

</details>

#### rejects trailing content after plan_hash

- rejects trailing content after plan_hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects trailing content after plan_hash")
val d = startup_plan_decode(valid_text() + "extra: 1\n")
assert_false(d.ok)
assert_eq(d.error_kind, startup_plan_error_malformed())
```

</details>

#### rejects a non-numeric profile_id

- rejects a non-numeric profile_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a non-numeric profile_id")
val bad = valid_text().replace("profile_id: 3", "profile_id: three")
val d = startup_plan_decode(bad)
assert_false(d.ok)
assert_eq(d.error_kind, startup_plan_error_malformed())
```

</details>

#### rejects a tampered body whose hash was not recomputed

- rejects a tampered body whose hash was not recomputed


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a tampered body whose hash was not recomputed")
val bad = valid_text().replace("command_id: build",
    "command_id: publish")
val d = startup_plan_decode(bad)
assert_false(d.ok)
assert_eq(d.error_kind, startup_plan_error_hash())
```

</details>

#### rejects a tampered plan_hash over an untouched body

- rejects a tampered plan_hash over an untouched body


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a tampered plan_hash over an untouched body")
val good = valid_text()
val bad = drop_line(good, "plan_hash") +
    "plan_hash: 0000000000000000\n"
val d = startup_plan_decode(bad)
assert_false(d.ok)
assert_eq(d.error_kind, startup_plan_error_hash())
```

</details>

### positive control — the decoder is not rejecting everything

#### still accepts a valid plan in the same spec

- still accepts a valid plan in the same spec


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still accepts a valid plan in the same spec")
val d = startup_plan_decode(valid_text())
assert_true(d.ok)
assert_eq(d.error_kind, "")
assert_eq(d.plan.command_id, "build")
assert_eq(d.plan.profile_id, 3)
```

</details>

#### proves the hash discriminates: different plans, different hashes

- proves the hash discriminates: different plans, different hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("proves the hash discriminates: different plans, different hashes")
val a = startup_plan_from_request(startup_request_v1(
    "simple", "build", 3, 0, startup_entry_kind_command(), 1, 2, 2))
val b = startup_plan_from_request(startup_request_v1(
    "simple", "test", 3, 0, startup_entry_kind_command(), 1, 2, 2))
val c = startup_plan_from_request(startup_request_v1(
    "simple", "build", 4, 0, startup_entry_kind_command(), 1, 2, 2))
val e = startup_plan_from_request(startup_request_v1(
    "simple", "build", 3, 0, startup_entry_kind_script(), 1, 2, 2))
assert_true(a.plan_hash != b.plan_hash)
assert_true(a.plan_hash != c.plan_hash)
assert_true(a.plan_hash != e.plan_hash)
assert_true(b.plan_hash != c.plan_hash)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/startup/contract/startup_plan_v1_fail_closed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering truncation vectors fail closed, malformed and wrong-version records fail closed, positive control — the decoder is not rejecting everything.
- truncation vectors fail closed
- malformed and wrong-version records fail closed
- positive control — the decoder is not rejecting everything

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `f041cb75d6dddaa216f64961fa87185ee01f7cefa90a1a954f2b78c1ddc8ecdb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f041cb75d6dddaa216f64961fa87185ee01f7cefa90a1a954f2b78c1ddc8ecdb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f041cb75d6dddaa216f64961fa87185ee01f7cefa90a1a954f2b78c1ddc8ecdb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/startup/contract/startup_plan_v1_fail_closed_spec.spl
mirror: doc/06_spec/01_unit/app/startup/contract/startup_plan_v1_fail_closed_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/startup/contract/startup_plan_v1_fail_closed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/startup/contract/startup_plan_v1_fail_closed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/startup/contract/startup_plan_v1_fail_closed_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an empty record' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/contract/startup_plan_v1_fail_closed_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a record cut to the version line only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/contract/startup_plan_v1_fail_closed_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a record cut mid-field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
