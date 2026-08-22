# Approval Broker Specification

> Verifies the approval broker behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Approval Broker Specification

Verifies the approval broker behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Red (no impl yet) |
| Source | `test/02_integration/app/simple_process_manager/approval_broker_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the approval broker behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Approval Broker

### request_approval

#### AC-6: approved intent yields SignedAction carrying correct intent

- Verify: AC-6: approved intent yields SignedAction carrying correct intent


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-SIMPLE_PROCESS_MANAGER_APPRO-001
step("Verify: AC-6: approved intent yields SignedAction carrying correct intent")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: AC-6: legitimate SPM-signed action verifies


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-SIMPLE_PROCESS_MANAGER_APPRO-001
step("Verify: AC-6: legitimate SPM-signed action verifies")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: AC-6: unsigned action is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-SIMPLE_PROCESS_MANAGER_APPRO-001
step("Verify: AC-6: unsigned action is rejected")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: AC-6: forged hmac is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-SIMPLE_PROCESS_MANAGER_APPRO-001
step("Verify: AC-6: forged hmac is rejected")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d4e3fab867301c31d09c28ea13440daf35a7ab507d436b489d56f0bba3a6edbc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d4e3fab867301c31d09c28ea13440daf35a7ab507d436b489d56f0bba3a6edbc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d4e3fab867301c31d09c28ea13440daf35a7ab507d436b489d56f0bba3a6edbc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/app/simple_process_manager/approval_broker_spec.spl
mirror: doc/06_spec/02_integration/app/simple_process_manager/approval_broker_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/simple_process_manager/approval_broker_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/app/simple_process_manager/approval_broker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/simple_process_manager/approval_broker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
