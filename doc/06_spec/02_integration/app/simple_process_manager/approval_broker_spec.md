# Approval Broker Specification

> request_approval → SignedAction path; spoofed (unsigned / forged) action is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Approval Broker Specification

request_approval → SignedAction path; spoofed (unsigned / forged) action is

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Red (no impl yet) |
| Source | `test/02_integration/app/simple_process_manager/approval_broker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

request_approval → SignedAction path; spoofed (unsigned / forged) action is
rejected by verify_response. Chrome-secret / platform-probe flow documented
in describe block; spec exercises the SPM-signed path only (simplification).

## Scenarios

### Approval Broker

### request_approval

#### AC-6: approved intent yields SignedAction carrying correct intent

- AC-6: approved intent yields SignedAction carrying correct intent


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: approved intent yields SignedAction carrying correct intent")
val broker = ApprovalBroker.new_for_test(pending_dir: "/tmp/spm_approval", chrome_secret: "secret".bytes())
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val intent = ApprovalIntent(
    app: "banking",
    action: "transfer",
    required: id_path_intern("id.user.banking.act"),
    level: AuthorityLevel.Sensitive)
broker.test_simulate_user_accept(intent)
val result = broker.request_approval(intent, principal)
expect result.ok to_equal true
```

</details>

### verify_response

#### AC-6: legitimate SPM-signed action verifies

- AC-6: legitimate SPM-signed action verifies


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: legitimate SPM-signed action verifies")
val broker = ApprovalBroker.new_for_test(pending_dir: "/tmp/spm_approval", chrome_secret: "secret".bytes())
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val intent = ApprovalIntent(
    app: "banking",
    action: "transfer",
    required: id_path_intern("id.user.banking.act"),
    level: AuthorityLevel.Sensitive)
val signed = broker.test_sign(intent, principal)
expect broker.verify_response(signed) to_equal true
```

</details>

#### AC-6: unsigned action is rejected

- AC-6: unsigned action is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: unsigned action is rejected")
val broker = ApprovalBroker.new_for_test(pending_dir: "/tmp/spm_approval", chrome_secret: "secret".bytes())
val principal = Principal(kind: PrincipalKind.Local, id: "eve")
val intent = ApprovalIntent(
    app: "banking",
    action: "transfer",
    required: id_path_intern("id.user.banking.act"),
    level: AuthorityLevel.Sensitive)
val unsigned = SignedAction(intent: intent, principal: principal, hmac: [])
expect broker.verify_response(unsigned) to_equal false
```

</details>

#### AC-6: forged hmac is rejected

- AC-6: forged hmac is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6: forged hmac is rejected")
val broker = ApprovalBroker.new_for_test(pending_dir: "/tmp/spm_approval", chrome_secret: "secret".bytes())
val principal = Principal(kind: PrincipalKind.Local, id: "eve")
val intent = ApprovalIntent(
    app: "banking",
    action: "transfer",
    required: id_path_intern("id.user.banking.act"),
    level: AuthorityLevel.Sensitive)
val forged = SignedAction(intent: intent, principal: principal, hmac: "wrong_bytes".bytes())
expect broker.verify_response(forged) to_equal false
```

</details>

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `92286fa6f8b6fbf2a206fdf4007634d1861d0751bbacd706af5290226e5a808e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `92286fa6f8b6fbf2a206fdf4007634d1861d0751bbacd706af5290226e5a808e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `92286fa6f8b6fbf2a206fdf4007634d1861d0751bbacd706af5290226e5a808e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/app/simple_process_manager/approval_broker_spec.spl
mirror: doc/06_spec/02_integration/app/simple_process_manager/approval_broker_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/simple_process_manager/approval_broker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/simple_process_manager/approval_broker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/simple_process_manager/approval_broker_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: approved intent yields SignedAction carrying correct intent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/simple_process_manager/approval_broker_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: legitimate SPM-signed action verifies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/simple_process_manager/approval_broker_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: unsigned action is rejected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
