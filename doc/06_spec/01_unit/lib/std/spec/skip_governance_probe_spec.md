# Skip Governance Probe Specification

> Tests covering skip_governance import graph and basic behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skip Governance Probe Specification

## Scenarios

### skip_governance import graph and basic behavior

#### loads and resolves an unregistered id to an empty record

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads and resolves an unregistered id to an empty record
   - Expected: rec.id equals `nonexistent-id-xyz`
   - Expected: rec.owner equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads and resolves an unregistered id to an empty record")
val rec = skip_ref_in_dir("nonexistent-id-xyz", "test/01_unit/lib/std/spec/fixtures/skip")
expect(rec.id).to_equal("nonexistent-id-xyz")
expect(rec.owner).to_equal("")
```

</details>

#### flags short/empty reasons as weak (via validate_free_text_skip)

- flags short/empty reasons as weak (via validate_free_text_skip)
   - Expected: validate_free_text_skip("", "critical").ok is false
   - Expected: validate_free_text_skip("todo", "critical").ok is false
   - Expected: validate_free_text_skip("Condition not met", "critical").ok is false
   - Expected: validate_free_text_skip("Deferred pending FPGA rev-C bring-up, see ISSUE-42", "critical").ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags short/empty reasons as weak (via validate_free_text_skip)")
expect(validate_free_text_skip("", "critical").ok).to_equal(false)
expect(validate_free_text_skip("todo", "critical").ok).to_equal(false)
expect(validate_free_text_skip("Condition not met", "critical").ok).to_equal(false)
expect(validate_free_text_skip("Deferred pending FPGA rev-C bring-up, see ISSUE-42", "critical").ok).to_equal(false)
```

</details>

#### rejects skip_it under critical, passes under moderate

- rejects skip_it under critical, passes under moderate
   - Expected: crit.ok is false
   - Expected: mod.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects skip_it under critical, passes under moderate")
val crit = validate_skip_it("critical")
expect(crit.ok).to_equal(false)
val mod = validate_skip_it("moderate")
expect(mod.ok).to_equal(true)
```

</details>

#### flags a stale expiry as expired (via validate_skip_ref_record)

- flags a stale expiry as expired (via validate_skip_ref_record)
   - Expected: validate_skip_ref_record(stale, "critical").ok is false
   - Expected: validate_skip_ref_record(fresh, "critical").ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags a stale expiry as expired (via validate_skip_ref_record)")
val stale = SkipRecord(
    id: "x", category: "hw", reason: "Real HW dependency, tracked separately",
    owner: "team", requirement: "", alternative_evidence: "", venue: "",
    expiry: "2000-01-01", issue: "ISSUE-1"
)
expect(validate_skip_ref_record(stale, "critical").ok).to_equal(false)
val fresh = SkipRecord(
    id: "y", category: "hw", reason: "Real HW dependency, tracked separately",
    owner: "team", requirement: "", alternative_evidence: "", venue: "",
    expiry: "2999-01-01", issue: "ISSUE-1"
)
expect(validate_skip_ref_record(fresh, "critical").ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/spec/skip_governance_probe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering skip_governance import graph and basic behavior.
- skip_governance import graph and basic behavior

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

- Canonical SPipe generation for source `a9a80abfb53b241ac591533b7ea31827aec9470441f4f60cc1a591263def3b19`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a9a80abfb53b241ac591533b7ea31827aec9470441f4f60cc1a591263def3b19`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a9a80abfb53b241ac591533b7ea31827aec9470441f4f60cc1a591263def3b19`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/std/spec/skip_governance_probe_spec.spl
mirror: doc/06_spec/01_unit/lib/std/spec/skip_governance_probe_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/std/spec/skip_governance_probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/std/spec/skip_governance_probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/std/spec/skip_governance_probe_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads and resolves an unregistered id to an empty record' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/spec/skip_governance_probe_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags short/empty reasons as weak (via validate_free_text_skip)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/spec/skip_governance_probe_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects skip_it under critical, passes under moderate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
