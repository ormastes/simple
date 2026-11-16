# Windows primary service V5 native acceptance procedure

Status: **ALL NATIVE CASES NOT_RUN — ACTUAL FIXTURES UNAVAILABLE**.
This is a source-grounded manual procedure, not an executable positive spec,
runtime PASS, native Windows qualification, or release admission. No test,
build, native operation or deployment was executed while authoring it.

## Inspected entrypoints and real prerequisites

The consumer is `src/os/apps/smux/server.spl`,
`runtime_connection_owner_v5.spl`, `runtime_connection_dispatch_v5.spl` and
`runtime_connection_request_v5.spl`. The command composition was inspected at
`/home/yoon/dev/simple-parallel-podman-ci-20261107/src/app/orchestrator/host_primary_service_v5.spl`.
The separate Host worktree and its retained journal foundation must be
integrated before these procedures can run together.

Use the exact command shape:

```text
host-primary-service <backend> <installed-anchor> <policy-pin-or-dash> <binding-file-or-dash> 127.0.0.1:0 <credential-file>
```

For this Windows route, backend is `windows-docker-process`; policy pin and
binding file must both be genuine, nonempty, **non-dash** installed values.
The installed anchor must resolve an actual enrolled Windows Docker process
deployment: retained private root, current protected policy, configured keys,
installation/provider/policy pins and actual journal writer lease. Scope uses
service-incarnation continuity and an empty boot ID. Prepare a genuinely signed
parent allocation and budget, and sign each exact helper preparation/execution
request against that retained chain. A parent already executing must be the
one named by the connection plan. Reserve a real pane and live authenticated
client attachment at its current epoch/revision/incarnation.

Obtain real fixture instrumentation for claim counts, Engine connection/write
attempts, journal/ledger revisions, native pending/completion observations and
cleanup ownership. Do not construct opaque owners, native absence evidence or
verified admissions from data. Store evidence by IDs/digests; do not publish
credential tokens, private keys or raw handles.

## Actual authenticated request boundary

Use the existing server transport, for example `smux_server_request_within`,
with its retained published endpoint and credential. The command is
`runtime-connection-v5 <token>`. The server authenticates the service credential
before dispatch. `<token>` is strict unpadded Base64URL of canonical SDN with
exact fields `version: 5`, `kind: smux-runtime-connection-request`, `action`,
`bindingUid`, `payload`; there is no source newline. Wire limit is 2097152 UTF8
bytes and token limit 2796203 bytes. No embedded NUL is admitted in the envelope.
This manual asserts no separate Caret client integration.

Nested payload dictionaries are canonical SDN without a trailing newline;
string fields containing requests/proofs use the actual production encoders.

| Action | bindingUid | Exact payload |
|---|---|---|
| host | empty | Dictionary: `action`, `operationId`, `payload` (all text) |
| host-progress, host-cancel | empty | Empty string |
| plan | selected binding | Dictionary: `request`, `cpuMillis`, `memoryBytes`, `clientId`, `attachmentToken`; request/client/token are text, resources integers |
| prepare | selected binding | Encoded `HostHelperRequestV1` text |
| bind | selected binding | Dictionary: text `request`, `proof`; actual helper request and matching encoded execution proof |
| progress, cancel, release | selected binding | Empty string |
| input-resolve | selected binding | Dictionary: text `clientId`, `attachmentToken` |
| input-issue | selected binding | Dictionary: text `clientId`, `attachmentToken`, integer `revision`, text `targetDigest` |
| input-write | selected binding | Dictionary: text `clientId`, `attachmentToken`, `nonce`, integer `revision`, `attempt`, `frameSequence`, text `data`, integer `offset`, `maxBytes` |
| input-observe | selected binding | Empty string |
| input-revoke | selected binding | Dictionary: integer `revision` |

`plan.request` is the V4 primary request encoding: `targetRequest` contains the
V3 binding request and `terminalMode` is stdin or tty. The binding request names
binding/workload/helper IDs, parent budget digest, service incarnation,
session/window/pane and expected epoch/revision/child incarnation. It supplies
no deployment root or native owner.

Replies are canonical `smux-runtime-connection-reply`, version 5, with
`action`, `bindingUid`, `error`, `result`. Inspect the typed result and actual
retained state; an empty error alone does not establish asynchronous completion.

## Native acceptance cases

### 1. Single credential and endpoint refusal — NOT_RUN

Start with one genuine `<credential-file>` and observe that the server retains
that file owner through read, ready publication and close. The wrapper does not
perform a competing credential-path read. Readiness requires publication
`completed`, empty error and state `published`; a previous publication state or
successful cleanup cannot substitute. The ready record contains the marker,
actual loopback address, token, PID and service incarnation.

Try a CLI endpoint other than `127.0.0.1:0`: require
`host-primary-service-loopback-auto-required` before opening the Host domain.
Direct server API mismatch returns `primary-service-loopback-auto-required`
with the supplied domain retained. Missing credential path refuses with
`host-primary-service-credential-required`; Windows dash anchor fields refuse
with `host-service-windows-anchor-fields`. Do not invent a credential-header
endpoint equality rule beyond these implemented checks.

### 2. Startup failure and AlreadyRunning retention — NOT_RUN

Exercise genuine credential open/read/publication failure, bind failure,
entropy failure and provider-policy refusal. Every returned recovery carrier
must retain the actual current owner/domain/cleanup/credential obligations.
In-process AlreadyRunning refuses without disturbing existing globals and
returns the newly supplied domain; it is not permission to duplicate a writer.
Do not use a stale input domain after any effect. An initialization failure may
leave the authenticated cleanup-only listener; it must not advertise ready.
Observe CLI `primary_service_recovery` ownership and `recoveryRequired`, not
only its rendered status string.

### 3. Authentication and envelope negatives — NOT_RUN

Wrong credential returns `smux: unauthorized` before V5 invocation. Missing
configured owner returns `smux: configured provider connection unavailable`.
Unknown/missing fields, invalid action/UID/payload shape and noncanonical tokens
must stop before owner invocation. Representative exact errors are
`runtime-connection-request-action`, `runtime-connection-request-binding`,
`runtime-connection-request-payload-required`, and
`runtime-connection-request-token-base64`. Malformed nested dictionaries return
`runtime-connection-payload-syntax`, `runtime-connection-payload-fields`,
`runtime-connection-payload-text` or `runtime-connection-payload-integer`.

### 4. Actual Host preparation and cooperative execution — NOT_RUN

Through `host`, submit the actual Host `host-prepare` request, then the exact
signed `host-execute` request for its retained operation. Observe real journal
admission and the same server-owned cooperative continuation. Use
`host-progress` until `pending` is false and a final `response`, `exitCode` and
error are available. Pending work, empty initial response and an empty submit
error are not delivery or completion. An exact host-execute retry must observe
retained state, not start another effect. A competing execution refuses with
`runtime-host-execution-pending`. `host-cancel` requests cancellation only on
that retained continuation; it creates neither another execution nor a grant.
Keep listener/pane progress responsive during bounded Host steps.

### 5. Actual connection plan, prepare and bind — NOT_RUN

Submit `plan` for the live pane and attachment. A cooperative inspection may
return `runtime-connection-plan-pending`; drive `progress` while pending and
replay the identical plan request to retrieve its retained plan. Conflicting
inspection returns `runtime-connection-inspection-busy`; changed immutable
request/resources for an existing binding returns `runtime-connection-binding-exists`.

Sign the exact helper plan/request and use `prepare`; record the returned
operation/envelope/intent/prepared-revision/receipt digests. Use `bind` with the
matching signed execution proof, then bounded `progress` until actual pane
adoption. Verify the same committed journal owner is retained after each turn,
one-use consumption cannot reopen a connection, and only the actual returned
session enters the pane. Invalid UID correlation returns
`runtime-connection-binding-mismatch`; wrong helper metadata returns
`runtime-connection-helper-mismatch` or `runtime-connection-helper-unavailable`.

### 6. Sole-reader output and incremental UTF8 — NOT_RUN

Have the actual container emit interleaved stdout/stderr with a multibyte scalar
split across native reads, NUL, malformed bytes and a partial scalar at EOF.
For tty, observe merged output explicitly. Verify the canonical pane is the
only reader, per-channel UTF8 carry remains independent, raw native bytes are
counted once, and presentation replacements do not inflate native counts.
Pending reads emit no invented EOF; actual EOF flushes retained partial bytes.
Neither output EOF nor attachment closure proves workload completion.

### 7. Independent input issuance and actual writes — NOT_RUN

Use `input-resolve` with the current client attachment; its result is the full
target digest. Use that digest and expected revision in `input-issue`; record
the new nonce/revision only when the actual post-install gate matches exactly.
`runtime-connection-input-install-not-current` must not be described as success.
Exercise actual `input-write`, `input-observe`, then `input-revoke` for that
revision. Observation uses the already reserved immutable request and performs
no new write. Input issuance does not grant Geometry; native rights are not
inferred from pane attachment or from public request metadata.

### 8. Immutable ledger, partial, Queued and Unknown — NOT_RUN

Begin at attempt/frame 1 and offset 0. An exact same-attempt retry must return
retained observation without another native write. Changed tuple returns
`runtime-connection-attempt-changed`; a sequence gap returns
`runtime-connection-attempt-not-next`. On known partial completion, only the
exact next attempt at the accepted suffix of the same full payload/frame may
continue; replayed prefix or changed payload returns
`runtime-connection-input-suffix-required`. Only full completion admits the
next frame at offset zero; violations return
`runtime-connection-input-next-frame-required`.

Capture actual Queued and Unknown outcomes. Queued is not delivery; inspect
`disposition`, `acceptedBytes`, `attempt`, `nativeError`. Neither uncertainty nor
missing native history may manufacture zero-byte completion or unblock replay.
New work/lease rotation must refuse with `runtime-connection-input-unresolved`
until exact native observation resolves the reserved attempt. A returned error
after invocation also retains Unknown. Never synthesize these receipts to
claim native coverage.

### 9. Current policy and attachment changes — NOT_RUN

Through the real protected update path change enrolled input principal, allowed
rights or maximum lease duration. The next resolution/issuance/write must
re-read current policy and refuse stale control state with
`runtime-connection-control-policy-changed` or the actual protected-policy
error. Expire/revoke the attachment and confirm stale-target refusals without
another native effect. Do not edit an untrusted local file and call it policy
installation. Observe existing exact receipts independently of new issuance.

### 10. Trusted admitted-only preparation timer — NOT_RUN

Prepare without binding, then request `release`. Before the actual retained
prepare deadline require `prepare-not-expired`, unchanged charge and owner.
The server timer subsequently advances the owner-bearing expiry at/after that
deadline; only the admitted prepared helper may release. Parent and sibling
charges remain. An executing helper must not use this timer as an abort grant;
require `execution-reconciliation-required` or the conservative absence refusal.
Verify returned journal sequence and projected ledger together, including
owner retention on a real post-commit projection failure if a genuine fixture
can induce it. Otherwise leave that exceptional branch untested.

### 11. Exact helper settlement, parent still charged — NOT_RUN

For an actual adopted connection use `release`: revoke native input, close the
exact connection, obtain actual native absence, settle the exact helper on the
same Host ledger, then publish the real acknowledgement back to the pane.
`runtime-connection-cleanup-pending` is not completion. Missing evidence returns
`host-primary-connection-consumption-uncertain` or `primary-connection-consumption-not-claimed`. Verify only that helper's
resources free; the primary workload/parent remains charged and is not stopped
or settled by connection closure. Repeated acknowledgement/release must not
double-free capacity.

### 12. Shutdown and error ownership — NOT_RUN

Authenticated `stop-server` refuses while cleanup/release is pending, including
`smux: stop refused: provider connection cleanup or host release pending`.
Host writer or credential uncertainty must return the corresponding cleanup
refusal, not `smux: stopping server`. Drive one bounded recovery-carrier step
at a time and retain its actual updated owners. Preserve earlier errors and
all pending obligations through reply/transport failure. Credential release
must follow actual Host absence. Successful stop requires no retained Host,
cleanup or credential owner; failure must not fall back to an original copied
domain, detach cleanup, or assume that absent ready publication released it.

## Current gaps: never PASS

- **SOURCE_REVIEWED / native NOT_RUN:** the private terminal-attempt chain
  is implemented and independently source-reviewed for failed/no-connection acquisition (snapshot `5f2f06214ca971d7dc6a215b07f929819c371ed194ef8e5834b29c99317ef0a0`). It requires
  actual cleanup-only positive-claim abandonment or exact closed-attempt native
  evidence before helper settlement. See
  `doc/06_spec/02_integration/lib/windows_primary_connection_attempt_v3_spec.md`.
  Uncertain publication, another winning claimant, missing exact evidence or
  native cleanup still pending must remain charged. This is no longer an
  absent implementation claim, and it is not a reviewed or native PASS. Do not
  fabricate absence or clear an entry to pass stop.
- **SOURCE_REVIEW PENDING / NOT_RUN:** Geometry now has a separate native
  control owner, durable Host attempt history and the six generic V5 actions.
  Its joint provider/Host/consumer review and configured-service acceptance
  scenario are separate from these original twelve procedures. Input never
  grants Geometry authority. No guest-size observation is claimed.

- **NOT_RUN:** actual enrolled/native fixtures, transport race evidence and
  positive native coverage are unavailable. Every case above remains open.

For each eventual execution record the exact source/artifact lineage, installed
policy and writer pins, operation/binding/attachment IDs, returned errors,
native observations and before/after ledger/journal state. A manual checklist,
pure codec case or canonical metadata record cannot replace that evidence.
