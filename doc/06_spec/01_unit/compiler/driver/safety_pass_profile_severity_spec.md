# Safety Pass Profile Severity Specification

> Tests covering safety pass profile-gated severity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Safety Pass Profile Severity Specification

## Scenarios

### safety pass profile-gated severity

#### maps moderate to Advisory

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps moderate to Advisory
   - Expected: safety_pass_severity_for_name("moderate") equals `SafetyPassSeverity.Advisory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps moderate to Advisory")
expect(safety_pass_severity_for_name("moderate")).to_equal(SafetyPassSeverity.Advisory)
```

</details>

#### maps strict to Advisory

- maps strict to Advisory
   - Expected: safety_pass_severity_for_name("strict") equals `SafetyPassSeverity.Advisory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps strict to Advisory")
expect(safety_pass_severity_for_name("strict")).to_equal(SafetyPassSeverity.Advisory)
```

</details>

#### maps robust to Warn (the migration window — never Deny)

- maps robust to Warn (the migration window — never Deny)
   - Expected: safety_pass_severity_for_name("robust") equals `SafetyPassSeverity.Warn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps robust to Warn (the migration window — never Deny)")
expect(safety_pass_severity_for_name("robust")).to_equal(SafetyPassSeverity.Warn)
```

</details>

#### maps critical to Deny

- maps critical to Deny
   - Expected: safety_pass_severity_for_name("critical") equals `SafetyPassSeverity.Deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps critical to Deny")
expect(safety_pass_severity_for_name("critical")).to_equal(SafetyPassSeverity.Deny)
```

</details>

#### deprecated lib behaves as strict (Advisory)

- deprecated lib behaves as strict (Advisory)
   - Expected: safety_pass_severity_for_name("lib") equals `SafetyPassSeverity.Advisory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deprecated lib behaves as strict (Advisory)")
expect(safety_pass_severity_for_name("lib")).to_equal(SafetyPassSeverity.Advisory)
```

</details>

#### deprecated reliable behaves as robust (Warn, not Deny)

- deprecated reliable behaves as robust (Warn, not Deny)
   - Expected: safety_pass_severity_for_name("reliable") equals `SafetyPassSeverity.Warn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deprecated reliable behaves as robust (Warn, not Deny)")
expect(safety_pass_severity_for_name("reliable")).to_equal(SafetyPassSeverity.Warn)
```

</details>

#### deprecated mission-critical behaves as critical (Deny)

- deprecated mission-critical behaves as critical (Deny)
   - Expected: safety_pass_severity_for_name("mission-critical") equals `SafetyPassSeverity.Deny`
   - Expected: safety_pass_severity_for_name("mission_critical") equals `SafetyPassSeverity.Deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deprecated mission-critical behaves as critical (Deny)")
expect(safety_pass_severity_for_name("mission-critical")).to_equal(SafetyPassSeverity.Deny)
expect(safety_pass_severity_for_name("mission_critical")).to_equal(SafetyPassSeverity.Deny)
```

</details>

#### empty name resolves to Advisory (default unchanged)

- empty name resolves to Advisory (default unchanged)
   - Expected: safety_pass_severity_for_name("") equals `SafetyPassSeverity.Advisory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty name resolves to Advisory (default unchanged)")
expect(safety_pass_severity_for_name("")).to_equal(SafetyPassSeverity.Advisory)
```

</details>

#### unknown name resolves to Advisory, does not crash

- unknown name resolves to Advisory, does not crash
   - Expected: safety_pass_severity_for_name("not-a-real-profile") equals `SafetyPassSeverity.Advisory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown name resolves to Advisory, does not crash")
expect(safety_pass_severity_for_name("not-a-real-profile")).to_equal(SafetyPassSeverity.Advisory)
```

</details>

#### env var unset resolves to Advisory

- env var unset resolves to Advisory
   - Expected: safety_pass_severity() equals `SafetyPassSeverity.Advisory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env var unset resolves to Advisory")
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
expect(safety_pass_severity()).to_equal(SafetyPassSeverity.Advisory)
```

</details>

#### env var robust resolves to Warn

- env var robust resolves to Warn
   - Expected: safety_pass_severity() equals `SafetyPassSeverity.Warn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env var robust resolves to Warn")
rt_env_set("SIMPLE_SAFETY_PROFILE", "robust")
expect(safety_pass_severity()).to_equal(SafetyPassSeverity.Warn)
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
```

</details>

#### env var critical resolves to Deny

- env var critical resolves to Deny
   - Expected: safety_pass_severity() equals `SafetyPassSeverity.Deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env var critical resolves to Deny")
rt_env_set("SIMPLE_SAFETY_PROFILE", "critical")
expect(safety_pass_severity()).to_equal(SafetyPassSeverity.Deny)
rt_env_set("SIMPLE_SAFETY_PROFILE", "")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/safety_pass_profile_severity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering safety pass profile-gated severity.
- safety pass profile-gated severity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `8223f5659b551c6910fafbed4c5a28e769a80f927a5194dd8cf8766b2a4280a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8223f5659b551c6910fafbed4c5a28e769a80f927a5194dd8cf8766b2a4280a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8223f5659b551c6910fafbed4c5a28e769a80f927a5194dd8cf8766b2a4280a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/safety_pass_profile_severity_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/safety_pass_profile_severity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/safety_pass_profile_severity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/safety_pass_profile_severity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/safety_pass_profile_severity_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps moderate to Advisory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/safety_pass_profile_severity_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps strict to Advisory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/safety_pass_profile_severity_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps robust to Warn (the migration window — never Deny)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
