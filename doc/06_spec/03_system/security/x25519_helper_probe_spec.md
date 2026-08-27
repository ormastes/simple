# X25519 Helper Probe Specification

> Tests covering x25519 helper portable probe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519 Helper Probe Specification

## Scenarios

### x25519 helper portable probe

#### records scalar and public key widths

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records scalar and public key widths
   - Expected: X25519_A_HEX.len() equals `64`
   - Expected: X25519_A_PUBLIC_HEX.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records scalar and public key widths")
expect(X25519_A_HEX.len()).to_equal(64)
expect(X25519_A_PUBLIC_HEX.len()).to_equal(64)
```

</details>

#### records shared secret width

- records shared secret width
   - Expected: X25519_SHARED_HEX.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records shared secret width")
expect(X25519_SHARED_HEX.len()).to_equal(64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Security |
| Status | Active |
| Source | `test/03_system/security/x25519_helper_probe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering x25519 helper portable probe.
- x25519 helper portable probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `083a77556aca3a7a54abd2f62728687cd9592d6e061573302424a8e9c5091655`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `083a77556aca3a7a54abd2f62728687cd9592d6e061573302424a8e9c5091655`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `083a77556aca3a7a54abd2f62728687cd9592d6e061573302424a8e9c5091655`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/security/x25519_helper_probe_spec.spl
mirror: doc/06_spec/03_system/security/x25519_helper_probe_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/security/x25519_helper_probe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/security/x25519_helper_probe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/security/x25519_helper_probe_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/security/x25519_helper_probe_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records scalar and public key widths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/security/x25519_helper_probe_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records shared secret width' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
