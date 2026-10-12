# Full implementation progress

Source base: c5f33e7b09392200b36b44876aadfac9e5ade251, remote release_phase3. Current isolated implementation workspace: /dev/shm/simple-dbc-runtime-recovery-20261012; native checkout: /mnt/wsl/simple-dbc-native-recovery-20261012; branch work/dbc-full-implementation-20261012. Earlier workspace paths below are historical evidence. Shared release worktree dirty source is other-session work and excluded.

| Feature | New-lane source/evidence | Required completion still missing |
|---|---|---|
| F01 contracts and baseline | Value contracts, codecs, capsule descriptors, WAL admission source; unit/integration scenarios NOT_RUN | Qualified tooling, runtime activation, complete common wire contracts and acceptance |
| F02 host registry and roles | Bounded pinned-role resolver, closed SDN decoder, dependency query; source tests NOT_RUN | Authenticated enrollment/rotation publication, credential/SSH integration and real host rejection receipts |
| F03 scoped grants and approvals | Trusted-value checks plus canonical grant encode/decode/digest source; tests NOT_RUN | Authenticated issuer/approval events, protected owner token, sandbox authority and real containment acceptance |
| F04 managed SSH and sessions | Existing SessionId extended with exact execution binding and distinct control/lease source; tests NOT_RUN | Fixed typed broker, live smux/native lease and persistent binding integration, reconnect/detach/cancel receipts and remote execution |
| F05 Caret/model controls | Detail design and planned owner integration | UI/tool caller wiring, independent approval handling, stale-target rejection and captures |
| F06 exact environments | Exact value matching and actual task/environment admission source | Discovery/placement integration and independent native/emulated mismatch execution evidence |
| F07 snapshots/build execution | Task digest binding, durable admission/claim/recovery source; memory enforcement gap documented | Owned reservation/worker confinement, immutable snapshot dispatch, two-host execution and settlement receipts |
| F08 CAS/quotas/group state | Design retained | CAS transfer/integrity, concurrent quota/disk/pin enforcement and qualified group lifetime |
| F09 Windows/host facades | Platform owner design retained | Native Windows V2 service integration and installed-binary/platform receipts |
| F10 signed evidence/GitHub | Protected evidence design retained | Signer isolation, check-specific authenticated receipts, protected verifier and stale/forged-event acceptance |
| F11 SHS/SDN containers | Validated plan/provider design retained | Equivalent digest-bound recipes, qualified real container/image providers and no-downgrade evidence |
| F12 updates/disposable attempts | Snapshot/lifecycle design retained | Update isolation, owned cleanup, rollback integration and update-during-build receipts |
| F13 mirrors/backups | Guarded inbound mirror design retained | Divergence/fetch/gitlink policy implementation and guarded backup acceptance |
| F14 additional hosts/clients | Role-specific platform design retained | Installed native/emulated role integration and independent host/client execution receipts |
| F15 TLS/optional RDMA | SSH-first/qualified transport design retained | Secure RPC parity, qualified provider and enabled-hardware grant/retirement evidence |
| F16 operations/performance | Producer-bound recovery failures retained | End-to-end failure matrix, observability, measured startup/latency/RSS baseline and release-blocking acceptance |

Every feature remains incomplete. These rows describe this new lane's evidence, not a claim that legacy owners have no implementation. Existing owner code does not qualify the newly selected integrated behavior without matching acceptance receipts.

## M0 runtime inventory

Neither main shared workspace nor release_phase3 shared workspace has bin/simple or bin/release. bin/simple-interp searches only those deployed paths and fails closed. Candidate binaries found under bootstrap/diagnostic trees have not been admitted for general test/SPipe use. No Rust seed or unqualified Phase 3 substitution is permitted. Remote cross-host/platform/provider evidence has not been collected.

New tests: test/01_unit/lib/common/contracts/distributed_control_v2_spec.spl. Execution NOT_RUN; coverage not claimed. Source contracts are not authentication, durable command admission, a sandbox or a working remote tool. No feature completion or Phase 3 PASS is claimed.

Next: locate or build an admitted pure-Simple self-hosted runtime under bootstrap owner rules; run focused contract tests once, then connect shared facets and existing Caret/build owners with real integrated SPipe scenarios. Numerical routing/performance NFRs remain proposed pending measured baseline; semantic no-fallback requirements are selected.

## M1 composition increment

Source: src/app/llm_caret/workbench/distributed_composition.spl. Seven closed descriptors cover HostAuthority, Session, Build, Artifact, EvidenceCI, SourceLifecycle and Client. Facet IDs share KpfId128 namespace 0x4442435632 and are declared once; all consumers require explicit facets. Existing mdsocpp_seal_v1 owns graph/capability/memory/concurrency validation. Capacities are caller supplied; descriptor construction is not runtime reservation, activation, provider execution or proof of no-GC hot-path behavior.

Tests: test/01_unit/app/llm_caret/distributed_composition_spec.spl adds four positive/rejection scenarios. Execution NOT_RUN. Runtime path rechecked this continuation: deployed bin/simple and bin/release/x86_64-unknown-linux-gnu/simple remain absent. Remote release_phase3 remains c5f33e7b0. Next source work: canonical versioned codec and existing-owner admission wiring, with bounded transport and durable operation receipts.

## M1 wire protocol increment

common/contracts/distributed_control_codec_v2.spl reuses the existing canonical builder wire owner for environment and operation records. V2 headers, fixed field count, trailing-field rejection and 64 KiB pre-allocation payload bound prevent implicit V1 interpretation or discarded constraints. Canonical environment bytes are SHA-256 identified. Integer encoding and decoding share an explicit 16-digit upper bound; zero policy/generation/resource values are rejected. Seven malformed-wire/round-trip/digest scenarios are authored in distributed_control_codec_v2_spec.spl. Runtime execution NOT_RUN.

Next integration must hash the actual typed BuildTask request into payload_digest, compare an observed worker environment to requested identity before reservation, and authenticate the grant issuer independently. These pure codecs do not constitute a remote broker or durable admission. F01 remains incomplete; full F02–F16 scope remains OPEN.

## Existing builder owner and admission binding

Inspection found bootstrap_builder/manager.spl is a compatibility facade over app/buildrunner/runner.spl, which in turn exports common/task_runner/scheduler. Preserve that canonical owner. New app/buildrunner/distributed_admission.spl binds authorized operation to canonical serialized BuildTaskV1 bytes and exact requested/observed environment before any process or resource side effect. It rejects alternate hosts, toolchain substitutions, altered duration/memory, unlimited V1 timeout and monitor-only memory mode. It is not yet called from a service entrypoint; durable operation journal and authenticated broker remain required. No runtime execution or feature PASS claimed.

## Build admission regression increment

Added eight real-call scenarios in test/01_unit/app/buildrunner/distributed_admission_spec.spl. Exact task acceptance is paired with source/argv sabotage, host redirect, resource substitution, monitor-mode memory downgrade, toolchain change and emulated test substitution. Execution remains NOT_RUN. Existing task_runner/journal.spl already provides PureDatabase-backed segmented WAL with owner lock, exact revision and replay validation; next durable operation work must reuse that foundation. Runtime verification gap is tracked in doc/08_tracking/bug/distributed_control_runtime_verification_unavailable_2026-10-12.md.

## Durable operation increment

Added immutable operation state (admitted/executing/outcome-unknown/terminal) and a domain ledger over the existing segmented WAL. It validates nonce-bound parent lease and exact revision, checks transitions before publication, updates the runtime index only after WAL commit and replays bounded history once at open. Exact-envelope duplicates preserve known/unknown outcomes; changed bytes under one ID fail. Six state regression scenarios authored. Runtime/storage crash tests NOT_RUN.

The storage owner explicitly provides process-crash publication recovery, not authenticated power-loss durability. No stronger claim is made. Broker integration must persist admitted and executing transitions before side effects and recover executing records as ownership uncertainty; notifications and cleanup receipts remain to wire. Memory index is rebuildable, never the durable authority. Tests and code remain unqualified/unlanded.

## Separate frozen-build/feature lanes

Mounted checkout is frozen for runtime bootstrap at 4b9139d8a (native tool alias fix). Feature edits continue only in the preserved RAM checkout, rooted at a9a0ca107, and must be integrated after the live build ends. No live source is overwritten. Added indexed journal lookup with owner/revision checks and build submission facade that authorizes actual task/environment, returns exact duplicate state, or commits first admission through WAL before returning NEWLY_ADMITTED. It does not spawn workers, claim execution, authenticate issuer identity by itself, or provide transport entrypoints. Runtime tests and integration remain NOT_RUN.

## Native filesystem recovery and interrupted execution

Mounted bootstrap successfully built its Rust packages but failed immutable authority publication with `target mode mismatch`: the mounted filesystem could not retain exact Unix read-only modes. A private native tmpfs source checkout at `/mnt/wsl/simple-dbc-native-recovery-20261012` passed an exact 0400 mode fixture. Its source at 61515a72a combines the prior feature commits with the tool alias repair; tracked authority script executable mode is preserved. Bulk build output remains on the mounted drive via the checkout build directory link. Canonical fresh Stage 2 recovery restarted against that source with existing Cargo caches, and disk preflight passed 536 GiB against the unchanged 20 GiB floor. Admission remains pending; no test PASS is claimed. The native source is frozen while that process runs.

Further feature work stays in the RAM checkout: `distributed_operation_journal_recover_execution_v2` checks the current owner/revision and publishes an executing-to-outcome-unknown transition through the existing WAL. Other states remain unchanged. A real-WAL integration scenario closes an executing owner, replaces it, retains uncertainty through another reopen, rejects a second execution transition, and checks repeat recovery publishes no extra event. This is an internal owner operation; startup/service enumeration and reconciliation wiring remain required. Execution NOT_RUN.

## Durable execution claim

`distributed_build_begin_v2` reauthorizes the actual task and environment at dispatch time, requires an exact previously admitted envelope, and commits its executing transition before returning to the command owner. Already executing, uncertain and terminal dispositions reject a second claim. The integration suite now uses this owner operation for interrupted-execution recovery and checks that expiry leaves the admitted state unchanged while a valid claim publishes exactly one additional event. No process is spawned by this boundary: service dispatch, authenticated caller construction, provider containment and authoritative outcome reconciliation remain required. Runtime execution NOT_RUN. This increment stays outside the live native bootstrap source.

Dispatch inspection confirms a concrete F07 dependency: `builder_worker_memory_admit_v1` rejects positive enforced-memory budgets, retains a no-child-started receipt and settles no-parent-owned capacity. The existing worker starts only a monitor/process-group provider with enforcement None. F07 must implement and qualify the cgroup/Job host provider before distributed execution can work; the new strict admission must not be relaxed to route through this worker. Detail design now records this actual boundary. The altered-task integration scenario checks rejection at both submission and execution claim, including a post-rejection authoritative lookup. All scenarios remain NOT_RUN.

The first native-source restart was deliberately stopped (exit 143) after reviewing downstream runtime capsule permission requirements: its mounted output authority would have the same filesystem limitation. Latest recovery uses native output `/mnt/wsl/simple-dbc-native-bootstrap-20261012`, with only the mutable Cargo target linked to its retained mounted cache. The journal recovery increment is integrated before the new source freeze. Build preflight still measures the mounted bulk build directory, and bootstrap free-space/resource guards remain enabled. Temporary native source/output must be preserved until admitted lineage can be transferred through the canonical owner; no completion is claimed.

## Compiler matrix failures and integrated repair candidates

The native build directory is now checkout-owned; preflight measures the actual Cargo target against its unchanged 20 GiB floor. Source/output guards retain their unchanged 10 GiB floor. Stage 2 digest 041e685fdbb0bb24eeec571a28d8bea57537909cd642116372bf4a8407fce1c8 passed admission, but its in-process matrix failed both mandatory tool builds. CLI failed source-root ownership selection for a nested loader leaf. Test runner failed 46 callback-field MIR diagnostics. A separate Result fixture aborted in Cranelift on a verification-only witness; the package-only app facade had no code-bearing MIR for the native module build. Unexecuted module/spec rows remain blocked, not passing evidence.

Reviewed candidates are integrated with the feature increments: nested loader resolution preserves explicit overlays and exact ownership rejection; array-loop bindings retain declared element types; callback recovery uses a registered declared composite layout; Cranelift erases only ResultMatchSemantic ghost metadata. The Result regression demands Ok(5) and propagated Err("odd"). All newly authored behavioral regressions remain NOT_RUN. Rebuild/admission and failed tool verification must prove these repairs before runtime/feature qualification or landing. Old admitted artifacts and failure receipts remain retained.

## Current recovery candidate and bounded verification

Native frozen bootstrap source is now `6ec114562`, integrating the nested compiler owner repair, exact record-declaration capture filtering, declared field ownership/type propagation into lifted lambdas, and scratch reclamation around canonical MIR identity hashing. Repair regressions remain NOT_RUN until a rebuilt producer runs them. The prior `4c479a0d…` producer passed the focused Result match/try witness once; that evidence does not qualify the CLI, test runner, or distributed features.

The first new bootstrap attempt stopped at the unchanged 10 GiB disk preflight. Owned old `build/phase_snapshots` were archived and byte-compared into `/mnt/c/Temp/dbc-owned-phase-snapshots-before-capture-rebuild-20261012.tar` before reclaiming their native storage. Bootstrap restarted with unchanged disk/RSS/admission policies and non-delegated compiler testing. Its active log is `/mnt/c/Temp/dbc-capture-scratch-owner-bootstrap-after-archive-20261012.log`; no terminal PASS is claimed. Native source remains frozen while this build runs; further feature edits belong only to the RAM checkout.

A cleanup agent inspected temporary files and worktrees. Seventeen apparently prunable registrations still refer to existing directories; no additional deletions were safe. Active sessions, unknown ownership and bootstrap evidence were preserved. F01 remains incomplete, F02–F16 remain open, and only the initial documentation PR has landed on `release_phase3`.

## F02 host-role boundary increment

Added `workbench/distributed_host_roles_v2.spl` with bounded snapshot lookup, exact registry revision and host-key digest checks, duplicate-ID rejection, and independent credential identity/reference/revision/revocation checks. It does not read secrets, connect, auto-enroll, or establish authentication from caller-provided values. Six unit scenarios include all four revoked roles, stale rotation, changed key, duplicate and unknown host, and invalid secret references. Tests are NOT_RUN. Strict SDN and authenticated enrollment/rotation ownership, dependency inspection and real transport wiring remain required for F02 completion. Further source work stays outside the live frozen native compiler checkout.

## F02 strict SDN decoding increment

Added an exact versioned host registry decoder over the shared SDN owner, with 64 KiB/128-host limits, structural guarding, duplicate diagnostics, closed fields and scalar types, independent role records and preserved revocation. A bounded second issue-aware parse is confined by design to configuration publication, never the request path. Six real source-fixture scenarios cover nested records, top/nested duplicate keys, unknown/missing fields, wrong types/version, revoke-then-reject and size/capacity/duplicate-host rejection. Tests remain NOT_RUN. The decoder is not yet wired to authenticated configuration publication, enrollment, rotation or SSH, so F02 is still incomplete.

## F02 credential dependency inspection increment

Added a bounded exact-reference query returning every affected host/role revision, including revoked dependencies and shared-reference roles. Stale, duplicate or malformed snapshots reject partial results. Two new source scenarios cover shared SSH/signer references, retained revocation/revision information and stale publication rejection. Tests remain NOT_RUN. This query supplies rotation planning data; authenticated enrollment and atomic rotation/revocation publication, secret-provider integration and SSH caller wiring still remain open.

## Rebuilt producer and callback behavioral failure

Producer c27cb117… at frozen source 6ec114562 rebuilt 1,237 modules and passed bootstrap sanity plus receiver/runtime checks; the compiler verification matrix is still live. The exact callback checker compiled and linked but failed execution output: text-returning field printed an integer instead of port, and captured record-returning array-loop callback yielded 0 instead of 20. Evidence and exhausted scoped retry budget are recorded in native_function_field_callback_abi_2026-10-12.md. Successful closure lowering is not successful callback execution. Full runtime qualification, distributed feature testing and landing remain blocked by unresolved tool/runtime evidence; no Phase 3 PASS is claimed.

## Current matrix test-runner failure

The c27cb117… test-runner build failed MIR lowering at 334400 ms with B5b: match has multiple wildcard arms, before native-cache planning. Root cause and source/function location are not established by the emitted diagnostic. This run does not verify the scratch repair's RSS effect. The separate CLI build and overall matrix remain live; no new build/retry was launched. Evidence is recorded in native_test_runner_multiple_wildcard_mir_2026-10-12.md.

## Terminal recovery qualification verdict

Session30186 is terminal: exit1 at stage2-compiler-tests. c27cb117… CLI build failed status88 after793 seconds with5882956 KiB peak versus5859375 KiB cap, during HIR; test-runner failed status1 after373 seconds with2946784 KiB peak on B5b multiple wildcard arms. Both artifacts are producer-failed and behavior_qualified=0. These earlier failures leave the native-cache scratch RSS repair unverified. Source-only wildcard owner diagnostics and facade classification are not present in this frozen producer. Deployed bin/simple and bin/release remain absent in both shared workspaces. No further full rebuild, Stage3 resume, seed tooling substitution or exhausted callback retry was launched. Preserve rejection/receipts/capsules. Full F01–F16 acceptance and landing remain incomplete; only the initial documentation PR is merged.

## Durable terminal checkpoint

Terminal c27 compiler matrix evidence is preserved in `/mnt/c/Temp/dbc-c27-terminal-compiler-matrix-evidence-20261012.tar` (452024320 bytes), byte-compared against the retained native tree. No evidence/cache/lineage was deleted. All repair/feature increments have persistent Git bundles beside the recovery archive. The full feature scope is retained above; no feature was narrowed to its currently authored helper or unit fixture.

## F03 canonical grant wire increment

Shared V2 codec now serializes every grant scope, policy/revocation, expiry and budget field plus a bounded distinct operation list; it rejects oversized frames, unsupported versions, trailing fields, invalid/oversized integers and noncanonical bytes. SHA-256 identifies the exact encoded body. Five source scenarios use independently specified golden bytes and explicit negative cases. Execution NOT_RUN; these are not signatures or authenticated approval events. Issuer key/identity binding, authenticated approval wrapper, trusted owner token and service/OS enforcement remain missing, so F03 is incomplete. No failed producer was used for general tests and no bootstrap retry was launched.

## F03 existing permission gate repair

Source inspection found unknown default modes passed through permission_decision and run_tool's deny/ask-only gate to actual dispatch. The existing owner now rejects invalid modes before allow shortcuts and independently requires exact allow before execution. Two regression scenarios include a real bash marker noncreation oracle; execution NOT_RUN. This repairs local gate logic without claiming remote authentication, approval or sandbox enforcement. No runtime/build retry was launched.

## F03 issuer and human-approval verification reference

Added HostAuthority-private cold verification using existing pure Ed25519 and separate canonical issuer/approval domains. Protected publisher key policies bind exact roles, revisions, scopes, budgets, policy/revocation and expiry; the approval binds grant digest and the complete operation envelope, preventing replay under a changed ID or payload. Six source scenarios sign independent golden messages with deterministic test keys and cover forged signatures, changed request binding, revoked/rotated keys, shared authority keys, budget expansion and expired approval. Tests NOT_RUN. Private keys, authenticated trust-root/approval publication, opaque owner-token publication, non-bypassable broker integration, sandbox enforcement and bounded no-allocation activation remain unimplemented/unqualified; F03 is incomplete. No build or exhausted callback retry ran.

## F03 authority snapshot selection increment

Added a private bounded publisher/index value with once-per-publication validation and exact role/identity lookup before signature verification. Competing revisions, foreign roles, malformed/inconsistent metadata, missing keys and stale service generations fail closed; revoked records remain visible but unusable. Six source scenarios reuse deterministic golden signature fixtures without importing another executable spec. Existing six signature scenarios retain the same independent oracles after helper extraction. Tests remain NOT_RUN. Protected trust-root loading, authenticated atomic generation publication, approval/audit persistence, service context, broker wiring and bounded activation remain open; no cold reference object is claimed as an admitted hot capsule.

## Shared signed-frame boundary increment

Moved signed grant/approval value shapes into common contracts, keeping trusted publisher keys/snapshots private. Added bounded canonical signed-frame codecs over the existing wire and binary-inspection owners; metadata validation is shared with signing-message construction. Five public codec scenarios include golden frames, malformed/canonical signature hex, version/trailing/truncation/size and integer/signature-length rejection. Two additional authority snapshot scenarios decode actual signed frames before private-key-policy lookup and require forged wire-valid approval rejection. All execution remains NOT_RUN; decoding does not authenticate. No runtime/bootstrap or exhausted callback verification ran. Host aliases for real platform/two-host acceptance were requested as missing target information; none have been assumed or enrolled.

Working and staged direct-env-runtime guards passed for the signed-frame increment. This is source facade-rule evidence only, not production verify PASS, signature execution, coverage, no-GC activation or Phase3 qualification.

## Reviewable unfinished work branch

Draft PR https://github.com/ormastes/simple/pull/3350 targets release_phase3. Its initial head is b3cfecfb685967ef5760575319b98a04bb1f368c; fetched target was27b46d5fd1. The draft contains only this lane's 71 changed files and explicitly records failed runtime qualification, NOT_RUN feature tests, cold-reference allocation limits and all F01–F16 completion gaps. It remains OPEN/DRAFT, not ready or merged; initial documentation PR3161 is still the only landing claimed. Unrelated dirty shared worktrees are excluded. Local caller/auth-provider research now identifies the actual bearer adapter, synthetic privilege-token limitations and configured credential-store seam; it does not substitute those for authenticated distributed caller publication.

## F04 session binding and control increment

Extended the existing single session identity contract with host-boot/service-instance/request-ticket/PID/start binding, exact mismatch rejection, distinct control scopes/domain routing and separate input/geometry lease checks. Monotonic lease expiry is explicitly nanoseconds in the owning host/service epoch. Detach preserves running process and working turn state. A separate Session-owner observation adapter requires confirmed running V4 data; UI-only identity users do not acquire that dependency. Seven pure source scenarios cover changed/reused identity, separate verbs/leases, stale/expired authority and detach independence. Execution NOT_RUN; metadata does not reconstruct a native lease or authenticate caller/provider facts. Broker/smux/persistence/remote acceptance and bounded activation remain open.
