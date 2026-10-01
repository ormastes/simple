# SPM Service RPC Specification

> Round-trip: request/response identical over SimpleOS transport and host

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SPM Service RPC Specification

Round-trip: request/response identical over SimpleOS transport and host

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Red (no impl yet) |
| Source | `test/integration/app/simple_process_manager/spm_service_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Round-trip: request/response identical over SimpleOS transport and host
transport. Privilege check RPC and window-register RPC exercised.

## Scenarios

### SPM service RPC

### transport parity

#### AC-3: host socket round-trip returns identical bytes

- AC-3: host socket round-trip returns identical bytes
   - Expected: resp.body.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-3: host socket round-trip returns identical bytes")
val svc = SpmService.new_for_test()
val req = SpmRequest(kind: "ping", body: "hello".bytes(), token_hint: AuthorityToken.public_none())
val host_bytes = spm_encode_request(req)
val host = SpmTransportHost.mock_bound(fn(incoming): svc.handle(incoming))
val resp = host.send(req)
expect resp.ok to_equal true
expect(resp.body.len() > 0).to_equal(true)
```

</details>

#### AC-3: SimpleOS mock transport yields same encoded request bytes as host

- AC-3: SimpleOS mock transport yields same encoded request bytes as host


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-3: SimpleOS mock transport yields same encoded request bytes as host")
val req = SpmRequest(kind: "ping", body: "hello".bytes(), token_hint: AuthorityToken.public_none())
val host_bytes = spm_encode_request(req)
val simpleos_bytes = spm_encode_request(req)
expect host_bytes.len() to_equal simpleos_bytes.len()
```

</details>

### privilege_service.check

#### AC-3: rejects request with token lacking id_path

- AC-3: rejects request with token lacking id_path


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-3: rejects request with token lacking id_path")
val svc = SpmService.new_for_test()
val principal = Principal(kind: PrincipalKind.Local, id: "eve")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.mail"),
    level: AuthorityLevel.Internal,
    principal: principal)
val req = SpmRequest(kind: "priv_check", body: "id.user.banking.view".bytes(), token_hint: token)
val resp = svc.handle(req)
expect resp.ok to_equal false
```

</details>

#### AC-3: allows request with matching token id_path

- AC-3: allows request with matching token id_path


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-3: allows request with matching token id_path")
val svc = SpmService.new_for_test()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.banking"),
    level: AuthorityLevel.Sensitive,
    principal: principal)
val req = SpmRequest(kind: "priv_check", body: "id.user.banking.view".bytes(), token_hint: token)
val resp = svc.handle(req)
expect resp.ok to_equal true
```

</details>

### window_registry.register

#### AC-3: window_register RPC uses the shared record body contract

- AC-3: window_register RPC uses the shared record body contract
   - Expected: wire.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-3: window_register RPC uses the shared record body contract")
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.banking"),
    level: AuthorityLevel.Sensitive,
    principal: principal)
val rec = WindowRecord(
    wid: 1, generation: 0, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 0, bytes: 0),
    acl_id_path: id_path_intern("id.user.banking.view"))
val req = SpmRequest(kind: "win_register", body: window_record_encode(rec), token_hint: token)
val wire = spm_encode_request(req)
expect req.body.len() to_equal window_record_encode(rec).len()
expect(wire.len() > 0).to_equal(true)
```

</details>

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

- Canonical SPipe generation for source `14711237ccb754410ee54be56c460368e46ddf56ecf886bfeeb457ac8e4b7646`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `14711237ccb754410ee54be56c460368e46ddf56ecf886bfeeb457ac8e4b7646`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `14711237ccb754410ee54be56c460368e46ddf56ecf886bfeeb457ac8e4b7646`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/simple_process_manager/spm_service_spec.spl
mirror: doc/06_spec/integration/app/simple_process_manager/spm_service_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/simple_process_manager/spm_service_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/simple_process_manager/spm_service_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/simple_process_manager/spm_service_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: host socket round-trip returns identical bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/simple_process_manager/spm_service_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: SimpleOS mock transport yields same encoded request bytes as host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/simple_process_manager/spm_service_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-3: rejects request with token lacking id_path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
