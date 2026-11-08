# Actual signed configured binding

Status: **AUTHORED_UNRUN**. This is authored executable acceptance source, not a passing socket, authority, broker, Container or compiler qualification.

The configured implementation is currently held for startup credential privacy
and owner-bearing journal open/close corrections. This scenario must consume
those actual fixes before execution; its supplied private fixtures do not
waive either production requirement.

Source: `test/03_system/app/llm_caret/feature/smux_signed_binding_socket_spec.spl`.
Helpers: `test/helpers/smux_signed_binding_fixture_v3.spl`, `smux_binding_authority_fixture_v3.spl`, and the existing real socket/owned-process fixture modules.

## Mandatory private provisioning

`SMUX_SOCKET_TEST_CONFIG` retains the existing exact nine fields for the real compiled smux and broker: root, brokerProgram, brokerDigest, smuxProgram, smuxDigest, delegatedCgroupPath, memoryLimitBytes, snapshotDigest, cacheIdentity. Explicit regular no-follow compiled binaries, matching digests, fresh private root, actual delegation and resource enforcement are required. Missing backend support fails, never skips.

`SMUX_SIGNED_BINDING_TEST_CONFIG` names a private mode-0600 regular SDN file in a private mode-0700 current-UID directory. It has exactly these nine text fields:

| Field | Required actual input |
| --- | --- |
| hostRoot | Protected enrolled host root with fixed stream policy, actual retained running workload, signed parent budget record, exclusive journal writer available, and pre-provisioned private `smux-helper-staging` directory. |
| helperRequestTemplate | Private canonical HostHelperRequestV1 packet containing the actual retained parent assignment/budget proof and a distinct unused helper operation/reservation. Its grant limits and current validity must cover actual plan resources and a 1–30 second operation duration. |
| executionProofTemplate | Private canonical execution-proof packet for that template, with actual execution grant/approval parameters. |
| issuerSeed | Private mode-0600 file containing exactly 32 bytes as 64 canonical lowercase hex characters, for the installed issuer identity/key revision. |
| approverSeed | Private mode-0600 file with the same encoding for the installed approver identity/key revision. |
| policyDigest | Exact pinned digest of the installed host authority policy. |
| orchestratorProgram | Explicit regular no-follow compiled orchestrator executable supporting actual host-status and host-inspect. |
| orchestratorDigest | Matching observed SHA256 digest of that binary. Path/hash verification is not a pinned-execution claim. |
| markerTriggerPath | Existing private regular mode-0600 data file mounted into the already signed, running workload by approved provisioning. The workload must repeatedly read its current line and emit it with CRLF; the attachment helper must not manufacture this marker. |

The two supplied keys must serve the same issuer/approver identities and revisions for preparation and execution. Real signatures are checked against the pinned installed policy before server startup, and again for the exact resolved demand. No fixed test seeds, fabricated host scope, synthetic clock, invented authority executable or direct engine commands are used. Parent budget proof bytes must match the actual protected retained record. Template expiry and resource limits are not relaxed.

The broker fixture root must be disjoint from the enrolled root, keys and marker. The approved workload marker directory must not expose the host root or authority keys. All private paths require trusted immutable ancestry, normalized absolute paths and current-UID mode checks. Stat/ID fixture oracles require `/usr/bin/stat`, `/usr/bin/id` and C/POSIX locale. Checks do not claim race-proof handle-relative filesystem authority.

## Scenario

1. **Read actual enrolled host fence and validate private fixture authorities.** Separate bounded compiled host-status and host-inspect calls record the actual current reservation fence and exact running workload native identity before the configured smux owner acquires the host writer. An intervening fence change causes preparation to fail; it is not retried with a new UID.
2. **Create vacant target and publish the canonical output plan.** Real authenticated CLI requests create a metadata-only vacant session, discover generated target fences and request planning. Read only the fixed protected canonical output-plan artifact at `<hostRoot>/journal/smux-binding-output-plans/<sha256-binding-uid>.sdn`. The actual host owner requires its journal child to be `journal`; parent budget records are also under that journal child. Match the plan's full digest, immutable binding request, helper/parent identities and initial runtime native identity.
3. **Sign and prepare the exact helper demand through the retained host owner.** Derive attach-broker demand and CPU/memory from the actual plan; bind the reservation using the actual fence and actual monotonic clock. Sign canonical grant/approval messages with supplied policy-matched keys. Exclusively create fresh mode-0600 staged request/execution packets, read back and synchronize them. Real authenticated preparation uses the existing retained host writer; no second host writer is opened.
4. **Bind once and capture a fresh workload nonce through the sole pane reader.** One real bind request must produce a strictly correlated adopted-opening reply. This is adoption, not readiness. Then generate fresh entropy, write only that data line into the approved existing marker file without replacing its mounted inode, and capture through real compiled smux requests until that nonce appears. No agent reference is independently read and no helper stdin is used.
5. **Clean the attachment and verify host settlement without stopping the workload.** Request session cleanup, accepting pending cleanup rather than claiming removal. Bounded same-owner inspection must reach exact correlated released state through actual native proof, host settlement and typed ACK. Confirm session absence, allowing the owner to have removed it automatically. Authenticated stop, fixture stdout EOF and actual grouped-owner terminal cleanup then close the test server. Only afterward does a separate compiled host-inspect independently confirm that the same Container native identity is still running.

## Failure and lifetime ownership

Each effect helper returns an updated carrier before any scenario assertion; the spec retains it globally after start, exercise and finish. It contains only authority paths/public packets, never private seed bytes in diagnostics. Socket tokens are redacted. Live refs remain process-local registry-lifetime values and cannot be serialized or restored after restart.

Binding is never automatically retried. Cleanup/inspection uses the same binding UID and exact retained owner with finite turn/deadline limits. If settlement remains unconfirmed, the fixture returns the retained live server carrier and protected host recovery state without cancelling its outer broker and discarding nested authority. The server's finite fixture lifetime remains in force; test isolation is not evidence of nested helper teardown. A known prebegin prepared-only result can close the writer while retaining its durable charge; it never counts as release or a passing positive scenario.

The shared real socket fixture bounds server lifetime to 45 seconds, publication to 8 seconds, each compiled request to 5 seconds, captures to 16 KiB, and fixture stdout drain/proof cleanup separately. Nonce capture and settlement each have an 8-second caller deadline and finite turn limit. A slow or saturated real backend fails honestly. Request timeouts remain uncertainty, never success.

The pre-existing workload and its signed parent allocation are provisioning-owned and deliberately remain running. This scenario owns and settles only its attachment helper and test server. No Windows support, remote gateway, interactive input, geometry, workload completion or termination is inferred.

Configured discovery uses immutable `OWNER` and exclusively published `OWNER.ready`.
The fixture validates the exact five-field newline-terminated record, unchanged
input nonce/token, private ready file, and actual service incarnation correlation.
A PID remains diagnostic. A stale/malformed ready record fails the scenario; it
is not removed or accepted as readiness. Runtime status remains AUTHORED_UNRUN.
