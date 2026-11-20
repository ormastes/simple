# Container completion shared authority body

Status: **AWAITING_VERIFICATION** — source-authored specifications and manual.
No compiler, seed, tests, signer, container, or wire codec was executed to qualify
this artifact. No runtime PASS or coverage claim is made.

Source: `test/01_unit/app/buildrunner/remote_container_authority_v2_spec.spl`.
Implementation: `src/app/buildrunner/remote_container_authority_v2.spl`.

`remote_container_completion_authority_v2` is the authority body shared by the V3
completion verify (`remote_container_authority_v3.spl`) and the Host-signed
reset-failure receipt verify (`remote_container_reset_failure_signed_v3.spl`). It
checks, in order: the original grant and human approval, the scoped execution-host
key, separate host/issuer/approver keys, the build/test operation, the exact task
and request payload, resources, host, operation id, assignment and controller fences,
the request and grant authorization digests, and the completion time.

milestone_0060 retired the V2 completion record, its signature domain, wire codec
and verify, together with the rest of the V2 remote-container path. Signature,
observation-digest and wire cases are pinned for V3 by
`remote_container_authority_v3_spec.spl` and `remote_container_session_v3_spec.spl`.

| Scenario | Intended assertion |
| --- | --- |
| Original bindings | The fixture claim and expected fences are admitted. |
| Current host authority | Revoked, rotated, wrong-role, wrong-signer and wrong-scope keys reject; reusing either issuer or approver public key for the host rejects. |
| Original signatures | Corrupted issuer and human-approval signatures reject. |
| Original task/request/grant | Changed task arguments, source, toolchain, inputs, outputs, attempt or claimed task identity, request payload, or claimed authorization digests reject. |
| Parent fence and identity | Changed assignment/controller expectations and different host/operation claims reject. |
| Current time/context | Future completion, expired grant or host key, and changed policy/revocation/session context reject. |

The shared authority fixture supplies deterministic original grant/approval/key/
task data; the claim is passed directly, so no case needs a host signature.
