# Run Sdn Lints Profile Specification

> Tests covering run's simple.sdn lints.profile tier (WP-4).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Run Sdn Lints Profile Specification

## Scenarios

### run's simple.sdn lints.profile tier (WP-4)

#### resolves lints.profile to critical when the key is present

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves lints.profile to critical when the key is present
   - Expected: run_read_sdn_lints_profile("test/fixtures/project_sdn_profile/with_profile/simple.sdn") equals `critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves lints.profile to critical when the key is present")
expect(run_read_sdn_lints_profile("test/fixtures/project_sdn_profile/with_profile/simple.sdn")).to_equal("critical")
```

</details>

#### resolves to \

- resolves to \
   - Expected: run_read_sdn_lints_profile("test/fixtures/project_sdn_profile/without_profile/simple.sdn") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves to \")
expect(run_read_sdn_lints_profile("test/fixtures/project_sdn_profile/without_profile/simple.sdn")).to_equal("")
```

</details>

#### no longer accepts the removed TOML-ish [lints] shape

- no longer accepts the removed TOML-ish [lints] shape
   - Expected: run_read_sdn_lints_profile("test/fixtures/project_sdn_profile/legacy_toml/simple.sdn") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no longer accepts the removed TOML-ish [lints] shape")
expect(run_read_sdn_lints_profile("test/fixtures/project_sdn_profile/legacy_toml/simple.sdn")).to_equal("")
```

</details>

#### returns \

- returns \
   - Expected: run_read_sdn_lints_profile("test/fixtures/project_sdn_profile/no_such_dir/simple.sdn") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns \")
expect(run_read_sdn_lints_profile("test/fixtures/project_sdn_profile/no_such_dir/simple.sdn")).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/run_sdn_lints_profile_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering run's simple.sdn lints.profile tier (WP-4).
- run's simple.sdn lints.profile tier (WP-4)

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

- Canonical SPipe generation for source `49d3a218f7a146675cc571d2404ebf551c7d45537f80f2ca4d3991c28a889d4e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `49d3a218f7a146675cc571d2404ebf551c7d45537f80f2ca4d3991c28a889d4e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `49d3a218f7a146675cc571d2404ebf551c7d45537f80f2ca4d3991c28a889d4e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/io/run_sdn_lints_profile_spec.spl
mirror: doc/06_spec/01_unit/app/io/run_sdn_lints_profile_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/io/run_sdn_lints_profile_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/io/run_sdn_lints_profile_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/io/run_sdn_lints_profile_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves lints.profile to critical when the key is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/run_sdn_lints_profile_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves to \' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/run_sdn_lints_profile_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no longer accepts the removed TOML-ish [lints] shape' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
