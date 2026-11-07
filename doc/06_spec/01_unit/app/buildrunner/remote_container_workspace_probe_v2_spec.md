# Same-process workspace access probe V2

Status: **AWAITING_VERIFICATION** — source-authored manual. No compiler, seed,
unit suite, process, container or workspace probe was executed while authoring.

Source: `test/01_unit/app/buildrunner/remote_container_workspace_probe_v2_spec.spl`.
Implementation: `src/app/buildrunner/remote_container_workspace_probe_v2.spl`.

The producer calls `remote_container_workspace_probe_v2(task, attempt_root)`
before starting its compiler or tests. The helper validates the task, requires
actual current directory to equal the resolved `<attempt_root>/work`, and calls
the existing worker's no-follow input/producer digest verifier before probe
effects. It reads `remote-workspace/<task.id>.nonce` as exactly 64 lowercase hex
digits plus LF, then checks the digest over the actual read bytes against the
declared input. The protected host must generate a fresh attempt-bound nonce
before signing the task; this helper cannot infer freshness by itself.

The probe leaf is `.simple-container-access-<nonce>`. Two successive cycles each
exclusively create a canonical marker bound to task identity and nonce, read it
back through the bounded no-follow file facade, compare it exactly and remove
the owned marker. The second exclusive create supplies a positive removal/
absence observation; no `exists()==false` result is treated as proof. Failure to
create never grants ownership to remove a preexisting path. Changed/unreadable
markers fail closed and are left for the outer workspace owner.

Only successful cycles return the bounded exact receipt:
`SIMPLE-REMOTE-CONTAINER-WORKSPACE-PROBE-2`, task identity, nonce and
`write-read-delete`, each terminated by LF. Pure
`remote_container_workspace_receipt_validate_v2(task, nonce, payload)` checks
the exact receipt and pin; it is structural validation, not I/O authority.

| Scenario | Intended assertion |
| --- | --- |
| Pure receipt | Exact task identity, canonical nonce input pin and bounded receipt validate as values. |
| Stale task | Changed retry, argv or source rejects an old receipt. |
| Nonce pin | Another nonce, uppercase/short nonce and a missing declared pin reject. |
| Framing | Other version, missing newline, trailing rows and oversized text reject. |
| Real wrong-cwd refusal | A real temporary work directory differs from the test process cwd; admission rejects before effects. A subsequent exclusive create positively proves the probe path was untouched. |
| Existing file preservation | A real preexisting file remains byte-identical when cwd admission rejects. This does not claim that the correct-cwd exclusive-create rejection path ran. |

The repository exposes no functional same-process cwd-changing facade (its
infrastructure `set_current_dir` reports unsupported). Correct-cwd success,
input mutation rejection under that cwd, and preexisting-probe rejection after
input admission therefore still require a real child launched with an owned
cwd. Those execution cases are explicitly pending; no stub, fake cwd or
pre-recorded probe receipt stands in for them.

The helper identifies no user from environment variables and makes no ACL,
selected-user, provider, execution or container-isolation claim. Its caller must
serialize preflight in the private workspace before workload start. Path-based
exclusive-create/read/remove facades do not attest an inode against hostile
concurrent replacement; changed markers and failed cleanup cannot yield success.
Independent common-API user inspection and signed parent evidence remain
separate requirements. No PASS or runtime qualification is asserted.
