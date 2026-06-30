# Approval Broker Specification

> request_approval → SignedAction path; spoofed (unsigned / forged) action is

<!-- sdn-diagram:id=approval_broker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=approval_broker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

approval_broker_spec -> std
approval_broker_spec -> lib
approval_broker_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=approval_broker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

request_approval → SignedAction path; spoofed (unsigned / forged) action is
rejected by verify_response. Chrome-secret / platform-probe flow documented
in describe block; spec exercises the SPM-signed path only (simplification).

## Scenarios

### Approval Broker

### request_approval

#### AC-6: approved intent yields SignedAction carrying correct intent

1. required: id path intern
2. broker test simulate user accept


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. required: id path intern
2. expect broker verify response


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. required: id path intern
2. expect broker verify response


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. required: id path intern
2. expect broker verify response


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
