# Capability Gating Specification

> Tests covering OriginGuard.check, SessionToken, CapabilityPolicy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Capability Gating Specification

## Scenarios

### OriginGuard.check

#### allows a matching origin

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allows a matching origin
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("allows a matching origin")
val guard = OriginGuard(allowed: ["https://app.example.com"])
val headers = "Origin: https://app.example.com\r\nHost: app.example.com\r\n"
val result = guard.check(headers)
expect(result.is_ok()).to_equal(true)
```

</details>

### SessionToken

#### serializes a token with the grant id

- serializes a token with the grant id
   - Expected: tok.serialize() contains `.dev.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("serializes a token with the grant id")
val tok = SessionToken.issue("dev", "https://app.example.com", 60000u64, "test-secret-key")
expect(tok.serialize().contains(".dev.")).to_equal(true)
```

</details>

#### percent-encodes dots in the serialized origin segment

- percent-encodes dots in the serialized origin segment
   - Expected: tok.serialize() contains `%2E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("percent-encodes dots in the serialized origin segment")
val tok = SessionToken.issue("dev", "https://app.example.com", 60000u64, "test-secret-key")
expect(tok.serialize().contains("%2E")).to_equal(true)
```

</details>

### CapabilityPolicy

#### default-deny policy denies InputInject

- default-deny policy denies InputInject
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("default-deny policy denies InputInject")
val policy = CapabilityPolicy.new("win-1")
val result = check_capability(policy, Capability.InputInject)
expect(result.is_err()).to_equal(true)
```

</details>

#### granting InputInject allows it

- granting InputInject allows it
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("granting InputInject allows it")
val policy = CapabilityPolicy.new("win-1")
val granted_policy = grant(policy, Capability.InputInject)
val result = check_capability(granted_policy, Capability.InputInject)
expect(result.is_ok()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/ui.web/capability_gating_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering OriginGuard.check, SessionToken, CapabilityPolicy.
- OriginGuard.check
- SessionToken
- CapabilityPolicy

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6177a640c4b9b1779def15667b04957e981f3fe0700668c2a57580189aaa1bd9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6177a640c4b9b1779def15667b04957e981f3fe0700668c2a57580189aaa1bd9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6177a640c4b9b1779def15667b04957e981f3fe0700668c2a57580189aaa1bd9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/ui.web/capability_gating_spec.spl
mirror: doc/06_spec/integration/app/ui.web/capability_gating_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/ui.web/capability_gating_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/ui.web/capability_gating_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/ui.web/capability_gating_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows a matching origin' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/ui.web/capability_gating_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serializes a token with the grant id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/ui.web/capability_gating_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'percent-encodes dots in the serialized origin segment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
