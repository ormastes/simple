# Actual controller V2 authorization/correlation test scope

Eight modern SSpec cases import actual controller_dispatch_authorize_v2,
controller_dispatch_host_status_v2, controller_dispatch_validation_match_v2,
controller_dispatch_response_v2, controller_dispatch_observation_match_v2 and
immutable packet retention helpers. No production module was edited and no
fake host function, fake SimpleContainerOwner or stub provider is supplied.

The reusable fixture adapts prior V1 SDK signing/snapshot patterns and the real
V2 wire fixture. It rebinds actual host authority to host-<64hex enrollment pin>
and re-signs four action grant/approval pairs with actual Ed25519 helpers. Four
distinct controller/host issuer/approver public keys are created through the
actual snapshot validator. Typed context is an INTERNAL protected-context unit
assumption; no caller-provided registry or production clock override is added.
Synthetic now100 is confined to these unit calls; real CLI uses native time.

Constructed host status/projection/observation DATA exercises actual correlation
functions only, not native host observation. Linux body uses real canonical
backend request bytes. Windows body remains explicitly opaque common-wire data.
Passing four SDK proof checks does not semantically validate either backend body;
actual core calls real host-validate before journal/capacity admission. Tests make
that separation explicit, including a proof-valid but body-invalid unit packet.

Source audit found and reported wrong journal import, untyped numeric host-status
fields and missing phase-dependent runtime native ID checks. Source owner fixed
canonical import, numeric schema/capacity checks and rejected empty/invalid native
IDs outside prepared/unknown. No source fix was made by this test task. Original
journal close after threaded mutations is safe because close checks lease identity
rather than an old projection revision. No other sequencing P0/P1 was found.

Reviewed order: four proofs -> retained AgentSession UID refusal -> host status ->
ACTUAL host validation -> fresh proofs -> immutable packet/create/bind/begin ->
prepare -> receipt commit -> reload policy/native clock/readiness -> execute.
Exact operation lookup prevents changed-request replays; completed/resume branches
inspect original work rather than mint a new attempt. Objects alone authorize
nothing. The real filesystem test preserves original packet bytes and shows
proof-insensitive input equality never replaces current SDK verification.

HostExecutionObservationV2 source is host-owned, reviewed read-only in
/home/yoon/dev/simple-host-execution-20261107. It is not copied or stubbed here;
its integration and host-local-command dependencies remain required before
execution. Constructed17-fact/scope/runtime observations are PURE correlation
fixtures, not native or authenticated producer proof. Full app/private-root/
backend API/native nonce/crash/unknown-outcome gates remain root/platform work.

No build, test run, admitted SSpec, manual generation, coverage or full-system
qualification occurred. Status: NOT_RUN/awaiting verification. Eight step names
mirror exact case titles; authored ORCH-02/HOST-02 label reconciliation is pending.
