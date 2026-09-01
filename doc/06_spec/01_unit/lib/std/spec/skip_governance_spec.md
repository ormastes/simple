# Skip Governance Specification

> Tests covering WP-9 skip governance: valid full-metadata skip, WP-9 skip governance: skip_it (carries no metadata by construction), WP-9 skip governance: bare pending (carries no metadata by construction), WP-9 skip governance: free-text-only reason (a string with no structured record), WP-9 skip governance: weak reason (empty/short/filler-word, via validate_free_text_skip), WP-9 skip governance: weak reason on a resolved SDN record, WP-9 skip governance: expired record, WP-9 skip governance: ownerless record, WP-9 skip governance: unregistered skip_ref id (no SDN record at all).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skip Governance Specification

## Scenarios

### WP-9 skip governance: valid full-metadata skip

#### passes at critical

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-MC-099
```

</details>

#### passes at robust

- passes at robust
   - Expected: v.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes at robust")
val v = validate_skip_ref_record(_full_record("Real HW dependency, tracked separately", "team-avionics", "2999-01-01"), "robust")
expect(v.ok).to_equal(true)
```

</details>

#### passes at moderate

- passes at moderate
   - Expected: v.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes at moderate")
val v = validate_skip_ref_record(_full_record("Real HW dependency, tracked separately", "team-avionics", "2999-01-01"), "moderate")
expect(v.ok).to_equal(true)
```

</details>

### WP-9 skip governance: skip_it (carries no metadata by construction)

#### is REJECTED under critical

- is REJECTED under critical
   - Expected: validate_skip_it("critical").ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is REJECTED under critical")
expect(validate_skip_it("critical").ok).to_equal(false)
```

</details>

#### passes under robust (unchanged default)

- passes under robust (unchanged default)
   - Expected: validate_skip_it("robust").ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes under robust (unchanged default)")
expect(validate_skip_it("robust").ok).to_equal(true)
```

</details>

#### passes under moderate (unchanged default)

- passes under moderate (unchanged default)
   - Expected: validate_skip_it("moderate").ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes under moderate (unchanged default)")
expect(validate_skip_it("moderate").ok).to_equal(true)
```

</details>

### WP-9 skip governance: bare pending (carries no metadata by construction)

#### is REJECTED under critical

- is REJECTED under critical
   - Expected: validate_bare_pending("critical").ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is REJECTED under critical")
expect(validate_bare_pending("critical").ok).to_equal(false)
```

</details>

#### passes under robust (unchanged default)

- passes under robust (unchanged default)
   - Expected: validate_bare_pending("robust").ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes under robust (unchanged default)")
expect(validate_bare_pending("robust").ok).to_equal(true)
```

</details>

#### passes under moderate (unchanged default)

- passes under moderate (unchanged default)
   - Expected: validate_bare_pending("moderate").ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes under moderate (unchanged default)")
expect(validate_bare_pending("moderate").ok).to_equal(true)
```

</details>

### WP-9 skip governance: free-text-only reason (a string with no structured record)

#### is REJECTED under critical even with a substantive-looking reason

- is REJECTED under critical even with a substantive-looking reason
   - Expected: v.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is REJECTED under critical even with a substantive-looking reason")
val v = validate_free_text_skip("Deferred pending FPGA rev-C bring-up, see ISSUE-42", "critical")
expect(v.ok).to_equal(false)
```

</details>

#### passes under robust (unchanged default)

- passes under robust (unchanged default)
   - Expected: v.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes under robust (unchanged default)")
val v = validate_free_text_skip("Deferred pending FPGA rev-C bring-up, see ISSUE-42", "robust")
expect(v.ok).to_equal(true)
```

</details>

#### passes under moderate (unchanged default)

- passes under moderate (unchanged default)
   - Expected: v.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes under moderate (unchanged default)")
val v = validate_free_text_skip("Deferred pending FPGA rev-C bring-up, see ISSUE-42", "moderate")
expect(v.ok).to_equal(true)
```

</details>

### WP-9 skip governance: weak reason (empty/short/filler-word, via validate_free_text_skip)

#### is REJECTED under critical

- is REJECTED under critical
   - Expected: validate_free_text_skip("", "critical").ok is false
   - Expected: validate_free_text_skip("todo", "critical").ok is false
   - Expected: validate_free_text_skip("later", "critical").ok is false
   - Expected: validate_free_text_skip("Condition not met", "critical").ok is false
   - Expected: validate_free_text_skip("Condition matched", "critical").ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is REJECTED under critical")
expect(validate_free_text_skip("", "critical").ok).to_equal(false)
expect(validate_free_text_skip("todo", "critical").ok).to_equal(false)
expect(validate_free_text_skip("later", "critical").ok).to_equal(false)
expect(validate_free_text_skip("Condition not met", "critical").ok).to_equal(false)
expect(validate_free_text_skip("Condition matched", "critical").ok).to_equal(false)
```

</details>

#### passes under moderate (unchanged default)

- passes under moderate (unchanged default)
   - Expected: validate_free_text_skip("", "moderate").ok is true
   - Expected: validate_free_text_skip("todo", "moderate").ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes under moderate (unchanged default)")
expect(validate_free_text_skip("", "moderate").ok).to_equal(true)
expect(validate_free_text_skip("todo", "moderate").ok).to_equal(true)
```

</details>

### WP-9 skip governance: weak reason on a resolved SDN record

#### is REJECTED under critical (Weak, not just FreeTextOnly)

- is REJECTED under critical (Weak, not just FreeTextOnly)
   - Expected: v.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is REJECTED under critical (Weak, not just FreeTextOnly)")
val v = validate_skip_ref_record(_full_record("todo", "team-avionics", "2999-01-01"), "critical")
expect(v.ok).to_equal(false)
```

</details>

#### passes under moderate (unchanged default)

- passes under moderate (unchanged default)
   - Expected: v.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes under moderate (unchanged default)")
val v = validate_skip_ref_record(_full_record("todo", "team-avionics", "2999-01-01"), "moderate")
expect(v.ok).to_equal(true)
```

</details>

### WP-9 skip governance: expired record

#### is REJECTED under critical

- is REJECTED under critical
   - Expected: v.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is REJECTED under critical")
val v = validate_skip_ref_record(_full_record("Real HW dependency, tracked separately", "team-avionics", "2000-01-01"), "critical")
expect(v.ok).to_equal(false)
```

</details>

#### is REJECTED under critical when expiry is missing entirely

- is REJECTED under critical when expiry is missing entirely
   - Expected: v.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is REJECTED under critical when expiry is missing entirely")
val v = validate_skip_ref_record(_full_record("Real HW dependency, tracked separately", "team-avionics", ""), "critical")
expect(v.ok).to_equal(false)
```

</details>

#### passes under moderate (unchanged default)

- passes under moderate (unchanged default)
   - Expected: v.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes under moderate (unchanged default)")
val v = validate_skip_ref_record(_full_record("Real HW dependency, tracked separately", "team-avionics", "2000-01-01"), "moderate")
expect(v.ok).to_equal(true)
```

</details>

### WP-9 skip governance: ownerless record

#### is REJECTED under critical

- is REJECTED under critical
   - Expected: v.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is REJECTED under critical")
val v = validate_skip_ref_record(_full_record("Real HW dependency, tracked separately", "", "2999-01-01"), "critical")
expect(v.ok).to_equal(false)
```

</details>

#### passes under moderate (unchanged default)

- passes under moderate (unchanged default)
   - Expected: v.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes under moderate (unchanged default)")
val v = validate_skip_ref_record(_full_record("Real HW dependency, tracked separately", "", "2999-01-01"), "moderate")
expect(v.ok).to_equal(true)
```

</details>

### WP-9 skip governance: unregistered skip_ref id (no SDN record at all)

#### is REJECTED under critical (skip_ref returns an empty sentinel, not a fabricated reason)

- is REJECTED under critical (skip_ref returns an empty sentinel, not a fabricated reason)
   - Expected: v.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is REJECTED under critical (skip_ref returns an empty sentinel, not a fabricated reason)")
val empty = SkipRecord(
    id: "unregistered", category: "", reason: "", owner: "",
    requirement: "", alternative_evidence: "", venue: "",
    expiry: "", issue: ""
)
val v = validate_skip_ref_record(empty, "critical")
expect(v.ok).to_equal(false)
```

</details>

#### passes under moderate (unchanged default)

- passes under moderate (unchanged default)
   - Expected: v.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes under moderate (unchanged default)")
val empty = SkipRecord(
    id: "unregistered", category: "", reason: "", owner: "",
    requirement: "", alternative_evidence: "", venue: "",
    expiry: "", issue: ""
)
val v = validate_skip_ref_record(empty, "moderate")
expect(v.ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/spec/skip_governance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WP-9 skip governance: valid full-metadata skip, WP-9 skip governance: skip_it (carries no metadata by construction), WP-9 skip governance: bare pending (carries no metadata by construction), WP-9 skip governance: free-text-only reason (a string with no structured record), WP-9 skip governance: weak reason (empty/short/filler-word, via validate_free_text_skip), WP-9 skip governance: weak reason on a resolved SDN record, WP-9 skip governance: expired record, WP-9 skip governance: ownerless record, WP-9 skip governance: unregistered skip_ref id (no SDN record at all).
- WP-9 skip governance: valid full-metadata skip
- WP-9 skip governance: skip_it (carries no metadata by construction)
- WP-9 skip governance: bare pending (carries no metadata by construction)
- WP-9 skip governance: free-text-only reason (a string with no structured record)
- WP-9 skip governance: weak reason (empty/short/filler-word, via validate_free_text_skip)
- WP-9 skip governance: weak reason on a resolved SDN record
- WP-9 skip governance: expired record
- WP-9 skip governance: ownerless record
- WP-9 skip governance: unregistered skip_ref id (no SDN record at all)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-MC-099`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `325b93cd435425d3b96c42aaa7fd092643b00a459974e4abb13a3fd46453f52f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `325b93cd435425d3b96c42aaa7fd092643b00a459974e4abb13a3fd46453f52f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `325b93cd435425d3b96c42aaa7fd092643b00a459974e4abb13a3fd46453f52f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/lib/std/spec/skip_governance_spec.spl
mirror: doc/06_spec/01_unit/lib/std/spec/skip_governance_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/std/spec/skip_governance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/std/spec/skip_governance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/std/spec/skip_governance_spec.spl:49:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'passes at critical' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/std/spec/skip_governance_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes at robust' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/spec/skip_governance_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes at moderate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/spec/skip_governance_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is REJECTED under critical' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
