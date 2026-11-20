# Feature Expert — Simple Orchestrator / Simple Container / Simple CI orchestration

## Role

Own process knowledge for the SIMPLEORCH lane: a Simple-native container
orchestrator, one portable container-management core, small host-specific
runtime providers, and the CI orchestration built on top of them.

## Feature Links

- Research (design authority): [`doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md`](../../../01_research/os/container/simple_orchestrator_and_container_2026-09-06.md)
- Lane state / milestone table: `.spipe/simple_orchestrator/state.md`
- Contract: `src/lib/common/contracts/orchestration/resource_v1.spl`
- Spec: `test/01_unit/lib/common/contracts/orchestration/resource_v1_spec.spl`
- Generated manual: `doc/06_spec/01_unit/lib/common/contracts/orchestration/resource_v1_spec.md`
- Fixtures: `test/fixtures/orchestration/`
- Requirements / plan / design pages: not written yet — the research doc's
  ORCH-001..016 table, §15.2 milestones and §14 acceptance catalog stand in.

## Do not touch

`src/os/services/container/**` is owned by `container_live_wiring`,
`simpleos_harden_t3ctr_manager`, `simpleos_harden_t4oci_import` and
`process-isolation`. Research §8.4 requires parity fixtures before any
extraction. Extend `src/app/ci/` for the CI half; do not add a second scheduler.

## Current state

The CI application EXECUTES. `Pipeline` decodes and expands into ordered `Job`s;
`src/app/ci/pipeline_runner.spl` launches real host processes on the
`native-process` lane and writes nonce-verified receipts. 24 examples green — on
the RUST SEED only; nothing here is self-hosted evidence yet.

The `native-container` lane is BLOCKED on this host (docker socket group-denied;
`runc --rootless` dies on `kernel.apparmor_restrict_unprivileged_userns=1`).
TODO DB rows 275-277. A blocked container job is recorded BLOCKED and never
downgraded to a host process — that refusal is asserted in the spec.

**Corrected 2026-09-07:** an earlier revision of this file said M2+ was blocked
because `src/lib/nogc_async_mut/kernel_plugin/` is absent. The directory is
still absent, but it blocks only ORCH-015 (bounded no-GC async hot paths). A
synchronous Job/CI runner needs none of it, and one was built and run. Do not
repeat that inference.

## Verification commands

```bash
bin/simple test test/01_unit/lib/common/contracts/orchestration/resource_v1_spec.spl --no-session-daemon
bin/simple spipe-docgen test/01_unit/lib/common/contracts/orchestration/resource_v1_spec.spl --output doc/06_spec --no-index   # require 0 stubs
sh scripts/check/lint-cached.shs src/lib/common/contracts/orchestration/resource_v1.spl
sh scripts/check-workspace-root-guard.shs audit --strict   # PRE-EXISTING RED (211, all tools/ + var/lib); this lane adds 0
```

Record binary identity with every run — `bin/simple` is a symlink other lanes
replace mid-session:

```bash
readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)" && bin/simple --version | head -2
```

## Traps found in this lane (2026-09-07)

- **`namespace` is a hard-rejected identifier.** A struct field, local, or field
  read named `namespace` is refused by the compiler's common-mistake check ("Use
  'mod' for modules instead of 'namespace'") — and it is NOT in
  `doc/07_guide/quick_reference/syntax_quick_reference.md`'s 124-keyword list.
  `ObjectMetaV1.ns` carries `metadata.namespace` because of this. Record:
  [`doc/08_tracking/bug/namespace_identifier_hard_rejected_2026-09-07.md`](../../../08_tracking/bug/namespace_identifier_hard_rejected_2026-09-07.md).
- **An SDN value containing a colon must be quoted.** `image:
  registry.example/probe@sha256:aa` parses as a nested mapping, so a text decode
  rejects it on type. Correct parser behaviour; quote such values in fixtures.
- **The strict profile needed no new duplicate-key detector.**
  `parse_with_spans_and_issues` already returns `SdnIssue(kind:
  "duplicate_key", …)` with 1-based line/col, and its span map is keyed by the
  same dotted path the schema uses — so "any issue rejects" gives real source
  locations for free. Do not write a second detector.
- **`text.to_int()` fails open to 0 on garbage**, so quantity parsing uses a
  local digits-only converter that returns -1. Keep it that way; a rounded or
  zeroed quantity would be a placement decision made on a guess.

## Update Rule

Update this file whenever a milestone row in `.spipe/simple_orchestrator/state.md`
changes state, a new contract or provider lands, or a trap above is fixed.

## Slice-2 surfaces (2026-09-07)

- CI contract: `src/lib/common/contracts/orchestration/ci_v1.spl` (`Job`,
  `Pipeline`, `expand_pipeline`)
- CI runner: `src/app/ci/pipeline_runner.spl` (`probe_linux_oci`, `run_pipeline`,
  `JobReceiptV1`, `RunReceiptV1`)
- Specs: `test/01_unit/lib/common/contracts/orchestration/ci_v1_spec.spl`,
  `test/02_integration/app/ci/pipeline_runner_spec.spl`,
  `test/01_unit/lib/common/sdn/sdn_sequence_duplicate_key_spec.spl`
- Blocked-lane row:
  `doc/08_tracking/todo/simple_orchestrator_native_container_lane_blocked_2026-09-07.md`

```bash
bin/simple test test/01_unit/lib/common/contracts/orchestration/ci_v1_spec.spl --no-session-daemon
bin/simple test test/02_integration/app/ci/pipeline_runner_spec.spl --no-session-daemon
bin/simple test test/01_unit/lib/common/sdn/sdn_sequence_duplicate_key_spec.spl --no-session-daemon
```

## More traps found (2026-09-07)

- **SDN block-sequence entries were reported as duplicate keys.** `- name: a` /
  `- name: b` produced `duplicate_key @ spec.jobs.- name` — note the glued `- `
  marker, which is the tell. Every strict consumer therefore refused any
  multi-entry sequence. Fixed in `_sdn_issue_block`; record:
  [`sdn_block_sequence_entries_reported_as_duplicate_keys_2026-09-07.md`](../../../08_tracking/bug/sdn_block_sequence_entries_reported_as_duplicate_keys_2026-09-07.md).
- **`simple lint` can abort, and the verdict still says "1 with findings".**
  `error: semantic: class CodeLine has no field named code` depends on the linted
  file's import closure, not its content — a 4-line file that only imports
  `ci_v1` aborts while `ci_v1` itself lints clean. Do not record that as a
  quality failure against the file. Record:
  [`lint_codeline_has_no_field_code_closure_dependent_2026-09-07.md`](../../../08_tracking/bug/lint_codeline_has_no_field_code_closure_dependent_2026-09-07.md).
- **An ordering oracle whose fixture is already in topological order is
  vacuous.** The first diamond fixture declared jobs in dependency order, so
  deleting the dependency edges did not change the result. Any ordering test
  needs a fixture whose declaration order is NOT a valid execution order.
- **`unshare -U` succeeds here while `unshare -Ur` and nested namespaces fail.**
  Probing "can I make a user namespace" says yes and is useless; probe the
  operation runc actually performs (`unshare --user --mount true`).

## Shared server selection and controller gateway (2026-11-15)

The [server-context guide](../../../07_guide/tooling/orchestration_server_contexts.md)
describes the authored `server-resolve` and `server-request` CLI, shared and
per-consumer SDN mappings, explicit container endpoints, SSH profiles and
installed controller gateway policy. [Host identity setup](../../../07_guide/tooling/orchestration_host_identity.md)
owns key and peer-policy provisioning. See [architecture](../../../04_architecture/server_contexts.md)
and the [verification plan](../../../03_plan/sys_test/server_contexts.md).

Keep submit/inspect/cancel with existing journal owners and signed
dispatch/resume/inspect-execution with existing execution/host authorization
owners. Framing correlation and selected endpoints grant no domain authority.
Do not report desired cancellation as observed termination or retry an
uncertain mutation with a new UID. Pure tests and the
[unit manual](../../../06_spec/01_unit/lib/common/config_core/server_context_v1_spec.md)
are authored, NOT_RUN. This increment supplies no remote/container deployment
receipt, native qualification or completed orchestration milestone.

`simple orchestrator container-plan-prepare` produces an unsigned candidate
with public server discovery before hashing. Candidate scope/policy are
unverified inputs; reservation, signing, submission and dispatch composition
remain open. Follow the host identity guide's ordered generation/pin/profile/
exchange flow; pending public registration grants no login authority. Windows
external SSH key-path projection fails closed until its separate capability is
available. These source paths and their manuals remain NOT_RUN.

## Linux service V4 host composition — service 40 (2026-11-16)

- **Owner module:** `src/lib/nogc_sync_mut/orchestration/host_linux_service_current_v4.spl` (#9745, #9747, #9754).
  Spec: `test/01_unit/lib/orchestration/host_linux_service_current_v4_spec.spl`. Fixture:
  `test/fixtures/orchestration/host_linux_service_verifier_fixture_v1.spl` (`..._ops_v1`, `..._sign_v1`).
  Both PRs are SOURCE_AUTHORED and NOT_RUN.
- **Order is structural.**
  - Startup uses `records_load_v4` through the protected readers with a fresh clock. It checks the sealed proof
    against the installed binding and credential, using policy re-read through the reader and never the proof's
    own bytes.
  - It compares the actual native borrow, mints a service-incarnation scope, and opens the journal with
    `host_capacity_owner_open_linux_v3` at the installed `journalRoot`.
  - The current record is published (no-replace) and read back before `published`.
  - `status_v4()` is the only ready/status producer, and `current_v4()` always rechecks everything.
- **Prepare/execute.** Signed prepare uses the landed `prepare_v1`; a same-ID replay keeps the original deadline,
  and both renewal and late retry are refused. The association is published scope-fenced and read back before the
  prepared reply. Execute requires the stored association bytes, fresh signatures and a live receipt.
- **Execution commit** (#9754): `host_capacity_owner_begin_associated_v3` binds the payload to the association
  itself, requires a Linux-protected current journal plus `continuity_proven`, re-authorizes with a fresh context,
  and runs ONE begin on the original reservation. `host_linux_service_execute_v4` handles three cases:
  - an identical archived packet is replayed with no effect;
  - a conflicting packet is refused;
  - otherwise it archives the packet (no-replace) and commits.
  It replies `execution-admitted`; the native launch is not composed.
- **Arm** (#9755): `HostLocalRootV3.LinuxService` is handled at all 11 exhaustive matches. Through the shared
  domain only status and close reach it; every other route refuses it. The 26 Windows-only wildcard matches
  already refuse.
- **Custody fix** (#9751): no panic after acquisition or after a committed begin in host execution.
- **Lease tokens** (#9775): each smux client lease token is
  `hex(HMAC-SHA256(owner_nonce, "smux-client-lease-v1|" + len:session|len:client|gen))[0:32] + ":" + gen`.
  The nonce never appears in a token or on the wire. Its only other use is process-internal: `attachment_owner` in
  service_revision.
- **Serving path + reconcile landed** (#9798, merge 4b89efd8dc4; SOURCE_AUTHORED, specs NOT_RUN). Independent
  opus review reached r3 APPROVE.
  - `host_linux_service_open_installed_v4` runs the read-only checks first. It then does the durable fresh-epoch
    admission, `lend_service_identity_v1`, `lend_store_inventory_v1`, a re-pin, and `start_v4`. Start publishes,
    then calls `host_linux_service_reconcile_flip_v4(owner, native, inventory)`. The flip is the only continuity
    flip; its proof stays private to the module.
  - Production reachability: `host-authenticated-service` -> `open_installed_v3('linux-service')` -> the opener.
  - **M1** `io/linux_fresh_epoch_store_inventory_v1.spl` is an OFFLINE read. The installed provider stays masked
    and never starts. The successor custody re-enumerates its retained graphRoot/runRoot fds, which must be empty;
    any entry refuses. The read is bound to boot, owner generation, process identity, store/partition digests and
    the lender's epoch digest. No provider format is parsed and there are no object rows.
  - **M2** On `MachineFreshEpochAdmissionOwnerV1`, the store-inventory loan exists only inside the service loan,
    in phase `admitted`. While it is active, `end_service_loan_v1`, `transfer_workload_v2`, `start_provider_v1`
    and `close_v1` all refuse. `close_v4` ends it first.
  - **M3 release rule:** released rows release by receipt, and never-begun rows (admitted, or abort receipt) by
    absence. A begun row needs a plan for THIS native machine with an `epoch-`+64hex scope. The plan's boot and
    generation are not compared (owner decision 2026-11-16, after an independent soundness review): the graph root
    is persistent, preparation proved both roots empty and censused the service uid range, and the provider units stay
    masked, so a plan from an earlier boot or process cannot be live. The generation is a process-local counter.
    Repro spec: S40-RECONCILE-12.
  - The provider start is refused for a lent or once-lent epoch (S40-LOAN-06, hermetic).
- **Open owner items (pre-existing):** SB-P1, no check ties a plan's objects to the observed roots ("fixed per
  install" is asserted, not verified); SB-P2, helper and child-barrier rows never release after a reboot.
  Receipts: `.spipe/simple_orchestrator/continuation_20261116/milestone_0020_service40_section_i/` (host-local).
- **The Agent V7 wire (assembly cuts 1-4) is not landed, and it is blocked on a coordinator decision.**
  - In the held cut bytes, nothing ever sets `ServiceSlotV5.installed` (E2-1). Invoke therefore always refuses, and
    invoke is the only creator of `session.workspace`.
  - The installed slot cannot be filled from the Linux-service startup. `HostAgentInstalledOwnerV7`:
    - reads a linux-podman `enrollment-binding.sdn`, which a linux-service root does not have;
    - opens its own journal at `root/journal`, the same path the V4 owner holds;
    - starts the container provider, which M1 keeps masked for the whole fresh epoch;
    - flips `continuity_proven` from ledger flags (Host21).
  - Options: (A) a V4-native agent owner; (B) a separate linux-podman install main; (C) retire the wire.
    See milestone_0020 DESIGN.md.

### Traps
- Never reconcile a Linux journal from ledger flags alone. The capacity owner requires native inventory/quarantine
  completion before admission. An empty projected ledger proves nothing (review P1, #9747).
- The verifier proof's fields are private. Pin it by `binding_digest()` and `credential_digest()`, never by struct
  equality.
- A caller-supplied journal opener is an authority-substitution surface. Open the protected journal inside the
  owner, at the installed root (review P1, #9745).
- Pure Ed25519 in the interpreter is slow. Expiry specs need a margin of 20 s or more plus a clock poll, never a
  1–3 s window.
- An import is not a caller. Before landing a staged unit, check production reachability, not just import
  closure. Specs do not count (wire v7 cut 1 was held for this, 2026-11-16).
- Simple does not enforce field privacy: any module can construct or mutate a "private" class field. A proof
  value is a seal only if it never leaves its module, so do the check and the effect in one call there.
- A start that ALWAYS refuses after durable work (admission, journal open, current publish) is dead weight, not
  fail-closed. Check refusal reachability before admitting a backend at the primary shape.
- `std.spec` `fail()` records the failure and returns. Code after it still runs, so return explicitly.
- Never bind a release to THIS epoch's scope. Every start admits a new epoch, so released and never-begun
  history rows from earlier epochs would quarantine every restart (milestone_0019 r2 P1). Check plan
  boot/generation/scope only for begun, unreleased rows.
- `check-continuity-proven-setters.shs` also counts positional `HostCapacityLedgerV1(` constructions, using a
  paren-depth scan across lines. Multi-line named constructions are therefore fine, but a `)` inside a string can
  skew the scan.

## V4 primary-attach cancel — milestone_0022 N3 (2026-11-17, specs NOT_RUN)
- Authority: `DESIGN.md` of `.spipe/simple_orchestrator/continuation_20261116/milestone_0022_native_attach/` sections 13.3-17.
  Code: `host_linux_helper_store_v1.spl` (R/X codec, full checks, entry guard, AttachCancelled evidence),
  `host_helper_settlement_commit_v1.spl` (cancel commit and `host_helper_cancel_unconsumed_v1`),
  `host_linux_service_current_v4.spl` (`host_linux_service_helper_cancel_resume_v4`).
- A cancel is authorized only by a JOURNAL refusal R (`host-helper-primary-refusal/`). The store copy is a mirror.
  Publish order is always journal first, mirror second, for R and for X. Both publishes are idempotent.
- The provider types the refusal (`ContainerPrimaryOpenRefusalV1`) by OBSERVED custody. Only the exact
  `workspace-primary-custody-required` absence counts as NoCustody; stale or unknown custody fails closed to
  CustodyAdvanced. Only NoCustody or SpawnRejectedRetired may write R.
- The startup resume runs before the reconcile flip. Its owner is adopted even on error. A row error sets
  `reconcile_error` and skips the flip, which quarantines the whole service.
- Charged forever (fail closed until an operator acts): `{}`, `{PA}` alone, any failed open after
  `action_begin_v2`, a crash before the R write, a failed post-consume R publish, R/X with an invalid store,
  a mirror that differs from the journal, and a permanent X settle failure.

## V4 primary-attach output read — milestone_0022 N4 (2026-11-17, specs NOT_RUN)
- `container_primary_output_read_v1(session) -> ContainerPrimaryOutputReadV1 {session, chunks, eof, error}` lives in
  `terminal_session_v2.spl` (NOT v1: v2 already imports v1, so v1 calling `container_terminal_read_v2` would be an
  import cycle). Gate order: adoption, then not native_cleaned, then one `container_terminal_read_v2` call. No max
  parameter: one call = one non-blocking read <= PIPED_RAW_CAP 8192 raw bytes (text cap 3*(cap+3)). Write the
  returned session back. Sticky eof belongs to the agent attachment (PR3b), not the session.
- Invalid UTF-8 is an existing transport property: the stream fails with `process_stdout_failed`.
- Write/geometry are NOT re-implemented: `container_primary_input_write_v1` (adoption + 4096 B) and
  `container_primary_geometry_authorized_v1` (adoption) already gate. Section 5's `container_primary_resize_v1` is
  superseded by the container-owned geometry path (sections 10.3/11).
- Pane binding (milestone_0021 14B): `HostAgentPaneBindingV4 {binding_uid, service_incarnation, session_id,
  window_id, pane_id, service_epoch}` + validate/encode/decode/digest/live_check live in
  `common/contracts/container/primary_attach_v1.spl` (no smux import). Field rules mirror
  `terminal_adoption_valid_v1` including `service_epoch > 0` (14C; `host-agent-pane-binding-epoch-invalid`).
  Decode is strict + byte-exact re-encode; the codec spec pins golden canonical bytes + sha256 digest and the
  exact refusal reason per branch. `live_check` returns `Result<(), text>`.
- `host_agent_attach_adoption_v4(plan, binding, operation_id, lease_epoch)` and the apply helper
  `host_agent_attach_adopt_v4(session, binding, operation_id, lease_epoch) -> ContainerPrimaryAttachAdoptionTurnV1`
  live in `terminal_session_v2.spl`. Gates: binding valid, `0 <= lease_epoch < i64 max`
  (`child_incarnation = 1 + lease_epoch`), `plan.identity.parent_operation_id == operation_id`, plan request digest
  re-derives. The apply helper uses the session's retained plan and always returns the session.
- 14C DROPPED 14B's `plan.identity.binding_digest == pane binding digest`: that field is the control-target binding
  digest compared on every write/geometry (`primary_input_v1`). The plan<->binding pairing is the controller-signed
  attach digest over `{planDigest, paneBindingDigest}`; PR3b refuses `attach-binding-plan` before archive.
- Read wrapper specs: `primary_output_read_admitted_v4_spec` drives data/eof/write-back with a real UNOWNED
  `/bin/sh` ref in the fixture session (owned v2 slot binding not exercised); the dead fixture ref (pid 71, owned
  root) surfaces `stale_process_reference` on POSIX (`process_stdout_failed` on the non-POSIX stub).
- PR3b owns: signature/authorize-kind verification of the binding, calling `host_agent_pane_binding_live_check_v4`
  with the agent/service's own live incarnation/epoch, storing the binding on the attachment.
- Specs: `test/01_unit/lib/nogc_async_mut/container/primary_terminal/` and `.../agent_pane_binding/` (one scenario
  family per file).

## V4 agent attach/detach machine — milestone_0021 PR3b part 1 (2026-11-17, specs NOT_RUN)
- Window end (14A F2): with a LIVE attachment the step driver stops at the signed window end and fixes outcome
  `failed` + the window-end marker digest. A run with NO live attachment keeps its final Inspect (m23, 2026-11-17):
  the attachment step answers `native` so the Inspect records the exit first (`succeeded`/exit digest when the
  workload exited), and the window-end marker only when it still runs. (PR3b part 1 had dropped that Inspect.)
- Entries: `host_agent_attach_apply_v4` / `host_agent_detach_apply_v4` are the ONLY signed entries (decode ->
  authorize -> 14C check -> pure check -> archive no-replace + read-back -> consume -> effects); the archive writer
  is private. The attach packet NAMES `planDigest`/`paneBindingDigest`; the signature covers those, and bytes that
  are not the named ones answer `attach-binding-plan` before archive.
- Release port answers are finite by construction: `non_advancing` counts Wait / same-rank Progress (cap 64 -> RB
  `attachment-no-progress`); only a wait while `pending` and the RP expire wait (bounded by prepare deadline + 5 s,
  then RB `attachment-expire-overdue`) are uncounted. Part 2 must answer charged-forever states Blocked up front.

## V4 agent attach/detach — milestone_0021 PR3b part 2 (2026-11-17, specs NOT_RUN)
- Production release port `host_agent_attachment_release_step_v4(call, HostAgentReleaseContextV4{capacity,
  store, monotonic_ms})`: RP expire (monotonic clock; `prepare-not-expired` = Wait, `reopen-required` = Blocked);
  RV geometry cancel-then-drain (budget 1 ms per call); charged-forever classification (`host_agent_release_charged_v4`)
  BEFORE U' (journal-R-bound `host_helper_cancel_unconsumed_v1`) or S (cleanup core -> settle core ->
  `simple_container_primary_session_return_v3`, Wait while `pending`). FL: the machine asks the port to classify
  (read-only); Blocked -> RB in the same call, else d1.
- F/B (milestone_0026, NOT_RUN): `host_primary_attach_quiesce_fallback_core_v3` (bundle bound first; proof-only, bounded
  cancel on each retry while the proof is pending, never retires descriptors) and `host_primary_attach_settle_retired_core_v3` (re-reads the
  `ContainerPrimaryTransportRetirementV3`, refuses a held session / empty proof / foreign plan or native, reaps, commits the
  ack, then consumes the spawn). Release port: F = quiesce (`fallback_quiesced`) -> `simple_container_primary_attach_cleanup_v3`
  -> `cleaned` -> settle_retired -> d4 clears the retirement -> `returned`; B = quiesce, drop the spawn, then S. d3 repeats until the container reports no error. B stores `quiesce_proof_digest` (sha256 of the quiesce proof) before it drops the spawn (11.4 "kept only in the proof"); the summary keeps it and inspect reports `quiesceProofDigest`. A `Rejected`
  spawn is Blocked `...-native-absence-unproven`. Trap: quiesce must not retire descriptors, the container's
  `fallback_cleanup_v3` retires them (a second retire with a reference is `stale_process_reference`).
- milestone_0031 attach hardening (2026-11-18, SOURCE_AUTHORED / NOT_RUN):
  - F15 pin: before the archive `container_stream_policy_template_pin_v2` requires the signed stream policy's root,
    broker program/digest/budget and delegated cgroup to EQUAL the enrollment-pinned `agent_helper_template`, and its
    environment to equal it or be empty (empty = no variables, the provider launches with the policy environment);
    `container-stream-policy-pin-{root,broker,cgroup,environment,profile}`. Still policy-controlled, constrained only by
    the native custody bind/validate (`bind_workspace_primary_attach_v3`, the remaining host-side pin): directory,
    memory policy, snapshot digest, cache identity, child image mode.
  - Post-begin refusals moved: pre-archive `attach-plan-terminal-mode` (tty only), `host-primary-parent-operation-mismatch`,
    the plan<->helper association (`host_agent_attach_association_check_v4`, action derived from helper kind as begin
    does) and the open entry guard in `linux_service_attach_admit_v4`; pre-BEGIN `host_primary_attach_open_precheck_v1`
    (entry guard, parent executing, provider plan reproduction; RP on refusal). Lease-bound checks stay after begin;
    a helper with `consumption_attempted == false` and no R is 11.4 U (not charged): U' writes the pre-consume R itself
    (Blocked at once on `host-primary-refusal-precondition`/`linux-helper-store-invalid`), then cancels.
- The OP attach effects are bound since m23 part B (below); the RELEASE port never starts them
  (`linux-host-agent-attach-open-abandoned`).
- Write-back: ports lend `agent.container` and return `container`/`capacity`; every caller adopts the capacity (single
  journal writer). `step_v4`/`close_v4` take `HostHelperStoreV1(helper_store, Some(capacity.journal))`;
  `helper_store` is opened at `start_v4`; m23 (2026-11-17): it is NOT rechecked in `current_v4()` any more. The
  recheck is `linux_service_helper_store_v4(owner)`, per helper-dependent operation, lending root "" (unopened) when
  the store is no longer the derived valid one; the helper evidence arm confines an unusable store to attach-domain
  rows (a journal-only connection row, PC without R/X, keeps its connection evidence; R/X beside PC stays Err).
- Close C2 runs one release step before the wedged return, only for a LIVE attachment, with the caller's real
  monotonic clock (`linux_service_close_monotonic_v4`); the service close keeps the capacity owner, journal AND both
  protected readers open while an attachment is live. Pane io reads ONLY via `container_primary_output_read_v1` (eof sticky).
- Clocks (m23 P2-5, fixed): facts carry `now` (grant clock, `not_after`) and `monotonic_ms` (receipt prepare
  deadline); the attachment stores the deadline converted to the grant clock (`host_agent_attach_grant_deadline_v4`),
  so every attachment bound runs on the grant clock; the expire core still reads the receipt's own monotonic deadline.
- m23 part B (2026-11-17, SOURCE_AUTHORED / NOT_RUN): the cv4 attach arm is BOUND to `host_agent_attach_apply_v4`.
  - Packet: `helperExecuteSigned`/`helperExecuteApproval` (the controller's `host_helper_execute_v1` grant over the
    helper operation) and `streamPolicy` (canonical `ContainerStreamPolicyV2`, must hash to the signed plan's
    `policy_digest`, else `attach-stream-policy`); both are in the signed attach payload digest. Verified before the
    archive by `host_agent_attach_helper_authorize_v4` (issuer == controller_ref, signatures, live clock/generation/
    revocation) and again, fresh, by helper prepare/begin. Codec: `container_stream_policy_{encode,decode}_v2`.
  - Everything refusable runs BEFORE the archive (the one slot is never burnt by a detectable refusal): helper store
    opened (`attach-helper-store`), Create runtime known and equal to the plan's (`attach-runtime-missing`,
    `attach-plan-runtime`), helper operation new on the journal (`attach-helper-operation-reused`), signed window seen by a step
    (`agent.not_after`), live epoch (`linux_service_live_epoch_v4`: the transfer's epoch record must still digest to
    `initial_epoch`; its `epoch_generation` is the epoch, no setter), live incarnation = `scope.continuity_id`, and
    `admit` = `linux_service_attach_admit_v4` (new helper id, then `host_helper_prepare_check_v1`, the read-only
    twin of helper prepare's checks). A stream policy is also bounded by the 1 MiB attach packet cap.
  - Effects run in the step driver only (`host_agent_attachment_open_step_v4(call, context, open, refresh)`): sub-step
    1 helper prepare; sub-step 2 helper begin + open core + adoption in ONE call (never split: a helper executing with
    no open attempt has no journal refusal R and could never be released). `HostAgentOpenContextV4` is rebuilt per call
    from the installed policy, service scope and the archived execute (parent = the row's PREPARE operation, not the
    execute envelope). A forced release (`call.release`: detach stage, wedged/failed, close, signed detach) never
    prepares or begins.
  - `host_linux_service_agent_terminal_authority_v4(owner) -> Result<HostAgentTerminalAuthorityV4, text>`: read-only,
    re-verifies the archived attach packet under the live context for a ready/adopted attachment; inspect reports it
    as `terminalAuthority`. Never cache it.
  - Still open: geometry (the service has no installed-policy-v3 source, `policy_bytes` is "", Resize is
    refused by the adapter); owner/domain lease + pane-io pass-throughs wait for their smux caller. Bug record: `doc/08_tracking/bug/v4_attach_helper_charge_held_without_records_2026-11-17.md`.

## Exact cleanup scope — AT-CTR-03 (2026-11-17, specs NOT_RUN)
- `container/providers/linux/cleanup_scope_v1.spl`: fixture-owned sentinel network/volume commands (`simpleorch-sentinel-` prefix + `io.simpleorch.sentinel` label), `cleanup_destroy_scope_error_v1` (destroy may name ONLY the run's own native id; no network/volume/prune/-v/-a; never a sentinel) and `cleanup_sentinels_intact_v1`.
- Wired into `oci_runtime_v1` destroy BEFORE `live_enabled`/`_execute`; pinned by a provider-level spec in `cleanup_scope_v1_spec`. Live proof `cleanup_scope_live_v1_spec` records `pending("BLOCKED: <unset vars>")` without `SIMPLE_CTR_CLEANUP_ENGINE/IMAGE/FIXTURE_ID`.
- Not covered: Windows-engine sentinels (still ENV-BLOCKED).

### PR3c smux consumer (milestone_0024, AUTHORED, NOT_RUN)
- The pane holds only a `HostAgentPaneLeaseV4`; smux actions `host-agent-pane-claim` / `host-agent-pane-read` (runtime_host_continuation_v6.spl, core `os.apps.smux.runtime_agent_pane_v1`) reach the agent through `host_service_domain_attachment_lease_v3` / `host_service_domain_pane_io_v3` -> `host_linux_service_attachment_lease_v4` / `host_linux_service_pane_io_v4`, both gated on `host_linux_service_agent_terminal_authority_v4` (expired approvals refused after restart) and using the service's own grant clock.
- The request payload is the controller-signed binding uid of the intended pane (`attach-binding-mismatch` otherwise, lease kept). The lease record is kept only on success, `attach-not-ready` and a binding mismatch; any other refusal drops it. After a smux restart the lease is gone (agent issues it once): re-attach. smux never cleans native state. `host-agent-pane-resize` stays refused (no installed-policy source on V4); `host-agent-pane-write` is the next slice (needs the smux control lease/target).
- PR3c S3 (AUTHORED, NOT_RUN): pane actions are refused while a connection is pending; the owner gate runs a smux registry consistency check (service incarnation + pane listed by `smux_list_panes`; `attach-binding-registry-mismatch`, lease kept) AFTER the signed authority verifies. An observed revoke tombstones the pane (`runtime-agent-pane-revoked`, no agent call) until an attach of a DIFFERENT run succeeds; a replayed attach of the held run changes nothing. Brokered panes never call `smux_pane_cleanup_primary_v5` (design 11.1 wins over 9.1).

## AT-OPS-01 drain/update handoff (2026-11-17, SOURCE_AUTHORED / NOT_RUN)
- Owner decisions: D1 exit-then-adopt (no live custody transfer), D2 build on the V4 service start path, D3 signed
  operation kind `service-handoff`, D4 exact wire version `service-handoff-v1` only (anything else refused).
- Contract `common/contracts/orchestration/host_service_handoff_v1.spl`; driver `nogc_sync_mut/orchestration/host_service_handoff_v1.spl`
  (never imports the service owner). Old owner: dispatch action `host_service_handoff_v1` (wire route `host-service-handoff`
  in `host_service_domain_v3`) verifies issuer == controller_ref, scope, signatures at its clock, its own current record
  digest and agent slot, then publishes `service-handoff/pending-<n>.sdn` (no-replace, read back) and only then sets
  `draining` (inspect, detach and cancel stay; every other action and `status_v4` refuse). The service manager then
  stops the unit (V6 `service-stop` is not a route; exit is the manager's job) and the owner close releases the writer.
- Successor: `host_linux_service_start_v4` VERIFIES a pending record after the journal writer is held and the current
  record is published, before the reconcile flip (a refusal sets `reconcile_error`: quarantine; status refuses), and
  CONSUMES it (`service-handoff/adopted-<n>.sdn`, no-replace, exact verified digest) only after the reconcile flip.
  The handoff never flips continuity; the reconcile re-proves exclusion. An approval that expired while the service
  was down is refused at the successor (APPROVAL_EXPIRED).
- Recovery (coordinator decision 2026-11-18, option a): a pending record the successor cannot verify (expired
  approval, policy bump) quarantines the start. A controller-signed ABANDON (operation kind `service-handoff-abandon`,
  payload names the pending sequence + digest + host; wire route `host-service-handoff-abandon`, dispatch
  `host_service_handoff_abandon_v1`, NOT gated on the quarantine) is verified through the same V4 path and published
  no-replace as `service-handoff/abandoned-<n>.sdn`; the pending record is kept as evidence and never adopted. After
  the unit restarts, the sequence is consumed and the start is fresh (the reconcile re-proves exclusion). Operator
  journal repair stays the last resort. Unsigned or mismatched abandons are refused.
- INSTALL REQUIREMENT: the installed authority policy's controller key must list BOTH operation kinds,
  `service-handoff` and `service-handoff-abandon` (the policy `operations` list), or every handoff/abandon is refused
  with `OPERATION_DENIED`.
- Specs: `test/01_unit/lib/orchestration/host_service_handoff_v1_spec.spl`; live env-gated, two-process
  `test/03_system/tools/host_service_handoff_live_spec.spl` (pending until its fixture env exists).

### Charged attach-helper recovery (milestone_0036, AUTHORED, NOT_RUN)
Bug `v4_attach_helper_charge_held_without_records_2026-11-17` (partially fixed; see its status). Two release paths for a charged V4 attach-broker helper row:
- Deadline reap (automatic, at service start inside `host_linux_service_helper_cancel_resume_v4`, before the flip). `host_helper_begin_checked_v1` publishes `host-helper-deadlines/<sha(op)>.sdn` (attach-broker only) after the signed proof is stored and BEFORE the executing commit: deadline = min of the four controller-signed expiries (recomputed at reap from the retained proofs, never re-verified: expired or prior-session grants cannot verify), proof digest, policy generation/revision/revocation epoch. `host_helper_deadline_reap_v1` acts only when the clock is STRICTLY past the deadline, generations match, markers are exactly `{}` or `{PA}` and death is proven: no PA = no spawn (the consume publish precedes the only spawn); PA + absent `broker.claim` at the consumed plan's launch root = never forked; PA + present claim = the matching broker's own terminal/unlaunched receipt (`group_process_stream_cleanup_proof_v2`). Proof only (no cancel, no N record). It then writes R (journal first, mirror second) and the EXISTING cancel releases. Anything unmet = Ok(false), row untouched.
- Signed operator abandon: operation kind `helper-abandon` (add it to the controller key's policy `operations` list), route `host-helper-abandon`, dispatch `host_helper_abandon_v1`, NOT gated on the quarantine, refused while draining and while the agent holds that helper's attachment in a stage other than `release-blocked`. Payload `HostHelperAbandonV1` names the helper op, its journal-derived request/receipt digests, the observed marker text (`state=..;pc=..;pa=..;n=..;r=..;x=..;o=..;rm=..;xm=..;store=valid|unusable`, `?` = unreadable) and the custody attestation. The service verifies (issuer == controller_ref, V4 signatures at this clock), checks the row, records proof `host-helper-abandon-proof/<sha(op)>/<digest>.sdn` (two segments: the old `<sha(op)>-<digest>.sdn` was 133 bytes, over `OPERATION_JOURNAL_SEGMENT_LIMIT_V3` = 128, so every publish was refused; pinned by `journal_proof_path_segments_v1_spec`) then marker `host-helper-primary-abandoned/<sha(op)>.sdn` (single writer, no-replace) and settles through the capacity owner. The evidence arm (`host_helper_abandoned_evidence_v1`) sits in `host_linux_completion_evidence_v3` BEFORE the store check and reads no store/R/X/mirror. A start finishes a recorded-but-unsettled abandon first.
- milestone_0043 (Opus re-review B): "never consumed" is a journal fact. The agent publishes `host-helper-reap-markers/<sha(op)>.sdn` before `host_helper_begin_v1`; the open core publishes `host-helper-consume-intents/<sha(op)>.sdn` (PA digest) before PA. The reap (`host_helper_reap_intent_gate_v1`) reaps `{}` only with no intent and `{PA}` only with a digest-matching intent, so a PA lost from the store holds the row. A recorded abandon is re-verified at restart; failure keeps the row charged and names the reason in the startup quarantine (charged unresolved rows quarantine via the reconcile drain). NOT_RUN specs: `host_helper_deadline_reap_v1_spec.spl`, `host_helper_abandon_v1_spec.spl`.
- milestone_0046 controller half (both abandons now reachable): commands `helper-abandon --operation <helper op>` and `handoff-abandon` (`src/app/orchestrator/host_action_command_v1.spl`). Without `--confirm` they print the Host's exact canonical record + sha256 and sign nothing; with `--confirm <sha256> --key-store --approver --grant-id --expires-in-ms` they re-read it, require that digest, issue via `controller_host_action_issue_v1` (allow-list `CONTROLLER_HOST_ACTION_KINDS_V1` = helper-abandon, service-handoff-abandon; same issuer/approver keys; env digest `sha256("simple-host-service-action-v1\n"+kind)`, budget 1/1) and send. Transport: new V6 action `host-control` (sub table `host_control_operation_v6.spl`: helper-inspect/helper-abandon/handoff-inspect/handoff-abandon -> `host-helper-inspect`/`host-helper-abandon`/`host-service-handoff-inspect`/`host-service-handoff-abandon`), smux `host_control_query_v6`, dispatch mode `host-action` (`controller_dispatch_host_action_begin_v3`/`_send_v3`) whose status gate keeps every identity check but NOT `ready` (the target Host is quarantined). Abandon frames archived create-only at `controller-host-action-v1/<sha(op)>.sdn`; a Host refusal is data; nothing is settled on the controller from Host text. Inspects (`host_helper_abandon_inspect_v1`, `host_service_handoff_abandon_inspect_v1`) share ONE derivation with the commands, are read-only and refused while draining. NOT_RUN specs: `host_control_operation_v6_spec.spl`, `host_control_inspect_v1_spec.spl`, `controller_dispatch_host_action_v3_spec.spl`, `controller_authority_host_action_v1_spec.spl`, `host_action_command_v1_spec.spl`.
- Still held: legacy rows without a deadline record, `{PA}` with a possibly live group or no operator command, `{PA,N}`, a permanent capacity-settle failure, and the agent's own release-blocked attachment object. Design: `.spipe/simple_orchestrator/continuation_20261116/milestone_0036_attach_charge_recovery/DESIGN.md`. Specs: `test/01_unit/lib/orchestration/host_helper_abandon_v1_spec.spl`, `host_helper_deadline_reap_v1_spec.spl`.

### PR4 LinuxService agent-terminal rights (milestone_0025, AUTHORED, NOT_RUN)
- `linux_service_agent_pane_policy_v5` (runtime_connection_policy_v5.spl) is a FIXED ceiling: exactly `[Input]`, 5000 ms lease, no Geometry (Resize is refused on V4). It is not derived from the authority (the loader runs at open, before any attach, and owner_v5 compares reloaded policy to the opened one).
- The right is exercised only while `host_linux_service_agent_terminal_authority_v4` is Ok: `capabilities_v5` (LinuxService arm), the control issue and every Write re-ask it (an expired/revoked approval ends it mid-connection).
- `host_linux_service_agent_pane_control_target_v4` (current_v4) -> `host_agent_pane_control_target_v4` (attachment_v4) builds the `SessionRuntimeControlTargetV1` from the verified binding, `lease_epoch` (attachment_generation), the attachment plan and the attached session's adoption; `client_id` = `agent-pane-` + signed binding uid. Err unless authority is Ok and the session is adopted as the binding names it.
- `host-agent-pane-write` is intercepted in `smux_runtime_connection_host_constrained_v5` (the only place with the control owner): body = exact SDN dict {bindingUid, attempt, writeId, offset, maximum, data}; a fresh Input lease per Write, revoked on return; the port installs the lease on the native input gate (refusing an unresolved/unknown previous outcome) before the write. `smux_agent_pane_op_refusal_v1` is replaced by `smux_agent_pane_resize_refusal_v1`.
- Follow-up (AUTHORED, NOT_RUN): the native input gate is closed on return and on every error path after the install (`host_agent_pane_input_close_v4`; a failed close is the Write's `gate_error`, the write outcome stands, lease kept); a failed control-lease revoke after a completed write rides in the response as `revokeError` (`smux_agent_pane_write_revoke_report_v1`; turn error only when the write itself failed); the issue token is `smux_agent_pane_control_token_v1` (spec-checked against `client_lease_token_valid`).
- Write replay protection (AUTHORED, NOT_RUN; bug `agent_pane_write_unknown_replay_2026-11-18`): the client supplies `writeId` (integer >= 1, bound into `HostAgentPaneWriteV4.write_id`). The AGENT (single owner, no lock) keeps `HostAgentAttachmentV4.pane_writes`, a per-lease ledger of the last 16 Writes whose native write was ATTEMPTED (id, sha256 of {offset, maximum, data}, disposition, accepted bytes, error, gate error); consulted in `host_agent_pane_io_core_v4` before the leaf. An exact retry (same id, same window and bytes) returns the recorded outcome with `replayed: true` and NO second native write, even when the first outcome was Unknown. Refusals (lease kept, nothing written): `attach-pane-write-id-reused` (same id, other bytes/window), `attach-pane-write-id-stale` (id at or below the eviction floor: its record was evicted, so it is never guessed new), `attach-pane-write-record-unavailable` (malformed/over-bound ledger), `attach-pane-write-id` / `runtime-agent-pane-write-id` (id < 1). A Write refused before the native write (install refusal, shape) is not recorded and may be retried. Retry rule for clients: after an Unknown disposition or a lost reply, retry with the SAME `writeId` and bytes; use a new id only for new bytes. A native write error is recorded too and is replayed on every retry (it drops the pane lease). Ids are scoped per attachment: one writer per pane lease.
- Client parsing of Write errors and response fields: the turn ERROR is `<write error>` plus optional suffixes in this order, `;gate:<native gate close error>` then `;control-revoke:<control lease revoke error>`; split on the first `;` for the primary code. After a COMPLETED write nothing rides in the error: a failed gate close is the response field `gateError` and a failed control-lease revoke is `revokeError` (never retry on these; the write stands). A COMPLETED write whose response could not be merged reports `runtime-agent-pane-write-revoke:<revoke error>`.
- Not authored: Ok-authority grant path (needs a started owner with a ready attach).

## Controller authority issuance + `remote-run-plan` — milestone_0030 PR-1a (2026-11-18, specs NOT_RUN)
- `controller_authority_issue_v1` (src/app/orchestrator/controller_authority_issue_v1.spl): issue-then-verify of ONE
  grant + policy-driven approval (D1 class: approver scope covers the grant, exactly one build/test action plus only
  route actions, `native-container` env bound by digest, approval <= grant expiry). Issuer must equal the configured
  controller. Keys: OpenSSH Ed25519 files in the protected identity store, leaf
  `sha256("simple-controller-authority-key-v1\n" + role + "\n" + identity + "\n" + revision) + ".key"`; read only
  through a cleanly opened store; signed via domain-pinned `host_identity_private_sign_{grant,approval}_v1`.
  The private-file parser (`host_identity_private_run_v1`) parses armour+base64 on `[u8]` (no text copy) and wipes raw, seed and `pair.0` on every post-decode exit (NOT_RUN spec `host_identity_private_wipe_v1_spec.spl`); encode and generate write body/raw/seed/check/entropy by index into pre-sized buffers and wipe all of them on every exit (`host_identity_private_encode_run_v1`, `host_identity_key_generate_from_entropy_run_v1`, NOT_RUN spec `host_identity_encode_wipe_v1_spec.spl`); the decoder reuses one 4-byte quantum buffer (wiped + checked on every exit) and refuses non-canonical armour (70-column lines, LF-terminated, no empty line); encode writes the PEM body by index with no base64 text intermediate (ENCWIPE-08, SEEDWIPE-10, milestone_0043). Still unwiped: std ed25519 temporaries, the hex entropy text, and the caller-owned private file (bug `host_identity_ed25519_std_temporaries_unwiped_2026-11-19`).
- `distributed_authority_snapshot_key_v2`: role-scoped lookup; never resolves a key under another role.
- `orchestrator remote-run-plan`: prints only operationId/grantDigest/planDigest; never prints or writes the signed
  pair; starts no run. The remote run itself (V4 slot kind, V3 executor, chunked route) is blocked on owner decision
  N4 (records: .spipe/.../milestone_0030_remote_container_driver/L6C_STOP_DECISIONS_2.md).
- Trap: on a lent V4 owner the V2 container effect calls are refused (principal None); remote builds must use the V3
  workspace flow, whose observations do not fit the V2 remote evidence freeze.
- D1 class predicate lives in lib: `remote_build_task_class_v1` (src/lib/nogc_sync_mut/daemon_sdk/), returns "" or a
  fixed `remote-build-*` code; the controller issuer calls it now, the Host remote-build route (PR-1c) must call it
  before admitting. The snapshot admits role `execution-host` (N2-a) and refuses an execution-host key that shares
  key material with any issuer/approver key (`AUTHORITY_ROLES_NOT_SEPARATE`), so key separation holds for any snapshot;
  PR-1c must take the execution-host key from the role-scoped snapshot lookup (today's remote_* consumers take
  `host_key` from context).

## Typed V3 workload exit status — milestone_0034 N7 (2026-11-18, specs NOT_RUN)
- V3 replies carry `RuntimeStateV1.workload_exit: RuntimeExitStatusV1`
  (`Unobserved | NotExited(status) | Exited(code) | Unknown(reason)`). It defaults
  to `Unobserved`. The legacy `state.exit_code` stays -1, so never read it.
- The exit is read once, by the `inspect-exit` stage at the start of V3 `Stop` and
  `Destroy`, before the engine stop. After a stop, `.State.ExitCode` holds the
  stop signal. Destroy reuses a completed read.
  `linux_fresh_workspace_exit_status_v3` returns `Exited` only for status
  `exited` or `stopped`, pid 0 and a code in 0..255. Podman reports 0 while created or
  running.
- A read that the engine fails (non-zero exit) or that cannot be decoded becomes
  `Unknown`. It is never success and never a step `Err`. A helper timeout or a
  spawn failure still latches, like any other effect. The read is skipped once
  any `stop` exists, because the code would then be the stop signal.
- Trap: V3 `Inspect` has no exit read. The agent reports a self-exit as
  `failed` until the Destroy reply settles it (`host_agent_destroy_exit_v4`), and
  only `Exited(0)` succeeds. Bug record:
  `doc/08_tracking/bug/agent_v4_self_exit_always_failed_2026-11-18.md`.
- The remote arm (L6c) consumes `RuntimeExitStatusV1` and
  `runtime_exit_status_text_v1`. `runtime_operation_codec_v2` does not yet
  encode `workload_exit`.

## Agent V4 source-return after a staged effect (2026-11-18, specs NOT_RUN)
- A written agent workspace is RETAINED (doc/05_design/agent_workspace_retention_v3.md): retire_native_v3 proves
  native absence at settle; the retention row commits in the same workload_publish_v3 batch as the CPU/memory
  settlement (storage stays charged); source-return ends in phase `retained-returned` and never calls close_v1.
- Trap: final close of a retained workspace still refuses (`machine-fresh-workspace-source-parent-retained`), so
  release_v4 / epoch close / successor advance stay blocked -- owner decision N9; bug record PARTIAL.

## Host remote-build route over authenticated V6 — milestone_0030 (2026-11-19, specs NOT_RUN)

Host side of the remote container build; the controller half is the `remote-run` command (see "Controller remote-run").
- ONE V6 action `remote-build` (N10): payload = `HostRemoteBuildSubRequestV6` {sub: open|input|start|collect|output|cancel,
  frame} (`host_remote_build_operation_v6.spl`); `remote_build_query_v6` (smux continuation) maps it onto the six internal
  `host-remote-build-*` domain actions behind the same pending-execution/connection/geometry gates. Reply envelope is
  1 MiB (HOST_SERVICE_OPERATION_REPLY_MAX_BYTES_V6), NOT 8 MiB: reply chunks are 576 KiB raw; the open record is capped at
  240 KiB because it is escaped three times (frame, sub envelope, V6 payload).
- Port install (N11): `remote_build_port_install_v3` (called by `host-authenticated-service` on a Ready linux-service
  domain). Profile = protected identity store `<anchor parent>/host-identity-profile` (execution-host `.key` leaf + the
  environment as `sha256("simple-remote-build-environment-v1\n"+host)+".profile"`, written by the admin command
  `remote-build-environment-install --store-root --host --environment`; the store accepts ONLY `<64hex>.key|.hosts|.profile`
  leaves, a free-form name can never be read); policy snapshot and host identity come from `remote_build_facts_v4` (re-verified
  records). No readable profile = no port = `linux-host-remote-build-port-missing` at prepare, before slot/charge.
- P2-a: `host_remote_build_profile_gate_v4` runs at prepare (before slot + charge) over a NON-consuming profile read
  (`read_build_workspace_profile_v3` on the admission's service reader). It checks only what the build profile
  determines (image, launcher, arg shape, terminal, memory floor); uid/gid/mount/containment stay at enable.
- N9-a: `close_native_v2` / `close_workload_v3` accept source phase `retained-returned` (root, lease, storage charge
  stay in custody; cleanup_v3 still refuses). A build outcome records `source_return: retained-returned`.
- Merge trap: release retains a written root AT SETTLE (custody already `retained-returned`), so the op (ii) evidence
  read must accept that phase (custody `read_settled_v3`, mount owner `read_settled_build_v3` accepts
  `native-retired-retained`).
- Retention release (milestone_0045, owner decision 2, 2026-11-19, specs NOT_RUN): controller command
  `retention-release --operation <build op>` (host_action_command_v1; two-phase plan/`--confirm`; kind `retention-release`,
  approver keys must be ENROLLED for it) -> V6 `host-control` subs `retention-inspect` / `retention-release` (NOT a
  remote-build sub-op: the run is gone by then). Record `HostRetentionReleaseV1` (host_retention_release_v1.spl): Host part
  (association digest + evidence `outcome`|`reaped` digest, re-derived from the Host journal) + the controller's OWN terminal
  state (completed|failed|cancelled; `outcome-unknown` needs remote-run-abandon first). Host order
  (host_remote_build_retention_release_v1.spl + `linux_service_retention_release_v4`): verify -> archived? -> derive ->
  check -> proof + no-replace marker -> lend root -> provider effect (workspace_retention_release_v1.spl: ADMIT own lease,
  fresh source, `remove_retained_tree_v1` removes the RUN CHILD via the no-follow fd-relative walk
  `retained_tree_remove_v1.spl` (same st_dev AND mnt_id, owner uid == euid under keep-id, symlinks unlinked never
  followed), close every fd, observe the leaf lease, drop the hold after a confirmed close) -> end loan -> archive
  `host-retention-released/`. Slot must be free and no workload run in this incarnation.
- Per-run workspace (milestone_0047, owner decision 1 "use worktree", 2026-11-19, specs NOT_RUN): every workspace run
  (remote build AND agent) stages into its OWN child `run-<sha256(op id)>` (68 bytes) of the admin-provisioned leaf
  (`linux_workspace_run_leaf_v1` / `linux_workspace_run_root_v1`, linux_workspace_profile_v1.spl). The request's ONE mount
  must be that child (source request match, `linux_fresh_workspace_request_v3`, launch `--mount src=`, created-config
  inspect, and P2-a `linux-host-remote-build-profile-run-root` at prepare). `remote-run` host-inputs `hostRoot` names the
  LEAF; the author appends the child. The child is created exclusive + no-follow beneath the held leaf fd AFTER the
  effect is recorded (`workspace_run_directory_create_v1`), proven empty, and its identity is in
  `directory_binding_digest` (binding holds parent, leaf, run). The leaf, its XFS project and quota stay: the admin
  provisions ONCE; release deletes only the run child (`remove_child_tree_v1`), never the leaf.
- Trap: the XFS project quota (hard_bytes) is SHARED by every retained run child: a full project refuses new staging
  until releases happen (fail closed). `run-removed` archives the remaining project usage, not zero.
- Trap: the native owner admits ONE lease per scope (second admit = EBUSY). A retention release therefore ADMITS its own
  lease (only in an incarnation where no workload ran: slot free, `agent_consumed` false) and drops that hold on every
  exit with `workspace_storage_close_retained_v1` (`rt_workspace_storage_close_retained_v1`: closes the native fds like
  process exit, refuses a loaned or released slot, never touches project/quota), so the next prepare admits afresh with
  no restart (the milestone_0047 `retention_lease_held` restart gate was a bug, removed). A failed drop fails the turn
  and the next admission fails closed (EBUSY) until restart. There is no recover entry (milestone_0048 deleted
  `rt_workspace_storage_recover_v1` in C, header, Rust stub and MIR text-ABI arm): reuse would skip the native re-proof.
- Agent workspace close (owner decision 3): DEFERRED by owner 2026-11-19 ("not now"). The agent close path keeps
  refusing (`agent-workspace-retention-requires-authorized-cleanup`); retention-release stays remote-build only. Gap
  record: no controller-side terminal row exists for a V4 agent run, and the Host agent outcome hardcodes
  `source_return: returned` although a staged agent source is retained.
- Trap: `absent-unmeasured` (owner decision 2, amended 2026-11-20 option B, milestone_0049, specs NOT_RUN) on a RESUMED
  release whose run child is gone, or on the FIRST issue for a reaped run that provably never staged: startup publishes
  `host-remote-build-stage-regime/<sha(fence)>` and the stage step publishes `host-remote-build-stage-intent/<sha(op)>`
  (both held writer, no-replace) BEFORE `stage_remote_build_v3`; admit sets `never_staged` only for `reaped` evidence
  whose prior fence has the regime and no intent. Intent present or no regime (pre-0049 incarnation) refuses
  (`workspace-retention-release-run-absent`) after journaling the marker, so the re-issue converges. Agent runs write no
  intent (nothing releases them). Signed record, verification and charge vocabulary unchanged.
- Trap: journal relative path parts are <= 128 bytes; `<sha>-<sha>.sdn` (133) is invalid -- use `<sha>/<sha>.sdn`.
- Trap (milestone_0050 review_b, specs NOT_RUN): a pre-transfer no-workload settle drops `owner.build` but KEEPS the slot,
  so `remote-build open` must refuse an operation with a published outcome or reap index (`linux_service_remote_build_reaped_v4`
  before the execute lookup) -- otherwise a replayed/retried open runs a workload on an already-settled row. An existing
  retention marker must be byte-canonical (`retention_marker_text_v1`) or it is `marker-invalid`, never resumed. The
  controller host-action send archives EVERY non-inspect sub create-only (retention-release included, not only `-abandon`).
### Controller remote-run (milestone_0030 controller half, specs NOT_RUN)
`simple orchestrator remote-run --dispatch-root --config-digest --key-store --approver --spec <dir> --out --grant-id --expires-in-ms`
(`remote_run_command_v1.spl`; pure driver `remote_run_v1.spl`, authoring `remote_run_author_v1.spl`, frames
`remote_run_frames_v1.spl`). N12-a: the task carries NO request pin (a hash cycle: pin -> request args -> invocation ->
task digest -> pin); request->task is the execute-signed association marker, task->request is the controller comparing the
prepare reply's `association.execution` with the draft it authored (`remote_run_association_check_v1`). Flow over ONE
retained reader (`controller_dispatch_remote_*`): status -> associated prepare -> association check -> admit the build row
(`controller_workload_store_admit_remote_build_v1`, single journal writer) -> associated execute (archived no-replace, never
resent) -> open -> input per file -> start -> collect (poll on the reply stage, 9 min bound, then the controller-signed
cancel) -> output chunks -> reassemble -> `accept_wire_v3` on the ROOT's journal (`controller_dispatch_remote_edit_v3`).
A reaped run is answered by the restarted Host with a HOST-SIGNED `service-restart` receipt (milestone_0045, below); a bare
reaped refusal (`linux-host-remote-build-reaped-incomplete`) settles `outcome-unknown` (`host-reaped-unsigned`). One grant lists
{build|test, host_reservation_v1, host_execute_associated_v3, host_agent_cancel_v4}; the approver key must be enrolled for
those operations. Spec dir: task.sdn, environment.sdn, run.sdn, host-inputs.sdn, inputs/<path> (formats in the author
module header). Traps: the Host prepare deadline is its MONOTONIC clock (operator-observed value in run.sdn); host-inputs
are operator-supplied projection inputs (a wrong value is refused at enable, retained workspace charged; the container memory
must equal the task limit, authoring checks it). PLATFORM (milestone_0037): `remote-run` runs from a Windows OR a Linux controller. One guard,
`controller_origin_check_v3` (controller_local_root_v3.spl), serves the local root, the dispatch owner and the V6 exchange:
Windows binds the first caller thread (retained handle, poisoned on exit), Linux admits only the procfs-pinned original
process MAIN thread (`linux_machine_process_origin_check_v1`: tid==pid, fork/PID-namespace quarantine); both give one
canonical native thread per registry, origin only, never authority. The Linux root is `LinuxProtectedRootReaderV1` (read-only
custody of `controller-config-v3.sdn` + `authority-policy.sdn`) plus a child journal `<root>/journal` opened by
`distributed_operation_journal_open_linux_child_v3` (controller-only sibling of the Host entry; the walked parent descriptor must be the
same dev/ino the reader holds, else `protected-storage-parent-identity-mismatch`; named limit: an identity pin on a held descriptor, not an openat from
the reader's own fd, because the storage cell has no fd getter; live swap spec controller_linux_journal_swap_v3_spec.spl is BLOCKED pending); `controller_local_root_install_v3` refuses on Linux
(`controller-local-install-linux-out-of-band`): provision the two byte-exact records into the 0700 private root, the
`--config-digest` pin and the config's own policy digest bind them. TRAP: a `linux_storage` journal has no `windows_store`, so
a `windows_store.is_none()` "legacy path" test silently captured it into pathname IO; every controller object module now asks
`distributed_operation_journal_protected_v3`. Live Linux verification needs a provisioned root (env
SIMPLE_LINUX_CONTROLLER_*, test/02_integration/lib/orchestration/controller_linux_root_v3_spec.spl), still NOT_RUN. A remote-build Host refusal
keeps the dispatch owner `ready` (outcome `host-refused`, encoded V6 reply as response) so the reaped recovery edit can run;
prepare/execute refusals still fail it closed. The admit returns the most advanced store even on error
(`ControllerRemoteBuildAdmitV1`) and resumes an exact-envelope row left `admitted`.
SETTLE (milestone_0037, `remote_run_settle_v1.spl`): a run that ends WITHOUT a signed bundle never leaves the row `executing`.
After the build row is admitted every failure is a journal edit through the root's single writer that publishes a typed
content-addressed record (`controller-remote-settle-v3/<sha256>.sdn`: op id, envelope digest, state, reason from a fixed
vocabulary, `RuntimeExitStatusV1` text) and moves the row: Host stage `failed`/`wedged`/`settled`-without-bundle -> `failed`,
`settled` + cancel cause -> `cancelled`, local timeout (cancel frame sent or unsent), broken exchange after admit or a refused
accept -> `outcome-unknown` (a timeout or a cancel REQUEST proves nothing about the Host; a later authoritative settle or the
reaped receipt finishes it). Exited(0) and `completed` are refused by the settle: only `accept_wire_v3` over a verified bundle
completes a row, first terminal wins. A Host `wedged` run settles `failed` on purpose (the Host itself ended it; unlike a local
timeout, which proves nothing). The reply prints `settled` (`failed|cancelled|outcome-unknown|unsettled:<code>`;
`unsettled:remote-run-settle-already-terminal` after `accept-refused` means the row is already terminal: inspect it);
`accept-refused` (exit 1) is a new state, and a reaped or accepted result may carry `task-journal-release-failed` in `detail`.
TRAP fixed with it: the controller workload replay refused every non-controller operation (`workload-store-foreign-operation`),
so ONE admitted remote build row bricked the root for the next open/restart; `build`/`test` rows are now skipped by
projection (never completed by it). Stale root: the edit closure contract is `ControllerJournalEditV1{journal,result,error}`;
the journal the closure ended with is ALWAYS adopted (`dispatch_retain_v3`), a refusal travels in the response
(`edit-refused:<code>`) and does not kill the link, and a failed task-journal release after a terminal accept is a third result
part, not an error. A restart reconciles by replay of the committed journal (never by the in-memory store). Remaining:
the Linux origin latches `quarantined` for the whole process after one failed procfs verify (one transient failure refuses
remote-run until the process restarts).
RESET-FAILURE EMITTERS (milestone_0038, AT-RUN-02; all specs NOT_RUN): the receipt V3 has four stages
(`remote_container_reset_failure_v3.spl`): `service-restart` (Host-signed since milestone_0045, from the reap record and the
open archive; no binding); the three Host stages `destroy-absence` (Destroy not ok after a
normal exit), `cancel-absence` (self-cancel Destroy not ok after Create) and `cancel-identity` (self-cancel stop/destroy not ok
with no Create) are emitted BY THE HOST. Executor (`host_linux_service_remote_build_v4.spl`): the three Stop/Destroy wedge points
call `remote_build_reset_wedged_v4`, which maps the failure point with `host_remote_build_reset_stage_v4` (pure: failing step,
cancel cause, Create made, exit read) and asks the new port fn `reset_failure` (`remote_build_service_port_v3.spl`) to rebuild
the context from the INSTALLED snapshot, build the receipt from the open record's digests plus the Host's own observations
(native id from `created`, binding digest captured at ENABLE), sign it with the execution-host key under its OWN domain
(`SIMPLE_REMOTE_RESET_FAILURE_SIGNATURE_V3`, `host_identity_private_sign_reset_failure_v3`; the completion domain is untouched so a
receipt is never a completion) and verify it with the controller's verifier before it leaves
(`remote_container_reset_failure_signed_v3.spl`, shared completion authority body). The executor ALWAYS ends `wedged` (record
reserved, charge held, close refuses); the signed wire is held on it and every later collect repeats the same bytes. TRANSPORT
TRAP: the service domain flattens an error reply to `host_service_error_payload_v2` text, so a receipt cannot ride on an error;
the collect answers SUCCESS with kind `linux-host-remote-build-reset-failure` {operationId, stage wedged, cause, receipt}. A port
refusal, an unmapped stage or an empty binding digest wedges exactly as before (a receipt never blocks wedging). Controller:
`remote_run_collect_v1` decodes the reset reply (`remote_run_reset_reply_decode_v1`) and runs
`accept_host_reset_failure_v3` through the root's single writer (`remote_run_host_reset_apply_v1`): verify signature + authority
BEFORE the journal read, bind to the controller's own task/policy/request/grant digests, journal `failed` bound to the receipt
digest, keep `signed-receipt.sdn` beside `receipt.sdn`; an unverifiable/replayed receipt falls back to the existing wedged settle
(`failed`/`host-wedged`), never `completed`. The enable-time binding digest needed a minimal CONTAINER-LIB hunk (another lane's
files): `enable_workspace_source_v3` -> `LinuxFreshWorkspaceEnableTurnV3` -> `LinuxWorkspaceEnableTurnV3` ->
`ContainerWorkspaceEnableTurnV3` carry `binding_digest` (it was only visible at the settled read, after settle). NO V3 STAGE (keep
the generic `host-wedged` settle): Stop failure with no cancel cause or after Create, create/prepare/configuration/start/inspect
wedges, settle, read, source-return, finalize and enable errors. A run lost to a service restart is Host-signed
`service-restart` since milestone_0045.
RECEIPT DURABILITY (milestone_0039; specs NOT_RUN): the Host-signed reset-failure REPLY is archived no-replace + read back via
the held capacity journal (`remote_build_reset_archive_v4`, path `host-remote-build-reset-failure/<sha256(operation id)>.sdn`,
keyed by operation id because a restarted service knows the operation, not the prior fence) BEFORE it is first answered; an
archive error is the plain wedge (no receipt). After a restart the startup reap indexes the operation and the collect route, on
`linux-host-remote-build-reaped-incomplete`, answers `host_remote_build_reset_failure_stored_v4` byte-identically; absent,
corrupt, foreign, non-canonical or receipt-less archives answer "" (milestone_0045: the Host then signs a reaped receipt,
else the refusal settles `outcome-unknown`). Expiry: replay is transport, not authority (the in-memory wedged-with-receipt arm already precedes the deadline check);
the controller verifies grant/approval/window, and open/transfer/reap still refuse an expired approval after restart.
A read-back failure also publishes `<sha256(operation id)>.refused` beside it, and the stored reader answers "" while that marker
exists: an archive that was never answered is never served after a restart (REVIEW_C P3-6; a lost marker keeps the old behaviour).
VERSION SKEW (REVIEW_C P2-2, a deployment requirement, not fixed in code): a controller older than #10398 cannot decode the
SUCCESS-shaped reset-failure reply (strict `remote_run_reply_decode_v1`) and settles `outcome-unknown`; since #10399 the same reply is
also served after a Host restart, where that controller used to get the reaped code and finish `failed`. So the controller must be
upgraded to >= #10398 BEFORE (or together with) any Host carrying #10398/#10399; never run a newer Host against an older controller.
RESET-FAILURE STAGES (milestone_0040; specs NOT_RUN): the Host-signed stage set grew, on the same SIMPLE-REMOTE-RESET-FAILURE-3 wire and
SIGNATURE_V3 domain, from 3 to 10 Host stages via one closed table in `remote_container_reset_failure_v3.spl` (reason / reap /
has-native): `prepare-wedge`, `create-wedge` (reap identity-unresolved, no native id), `configuration-wedge`, `start-wedge`,
`inspect-wedge` (incl. the running poll), `stop-absence` (Stop not ok, no cancel cause) and `cancel-stop-absence` (self-cancel Stop not
ok after Create) (reap incomplete, native id). `host_remote_build_reset_stage_v4` stays total and fail-closed on impossible Create
states; `remote_build_native_step_v4` now takes the port and routes 8 wedge sites through `remote_build_reset_wedged_v4` (sign, archive
durably per #10399, reply; any failure = plain wedge; a deadline-compute error is no issued effect and stays the plain wedge, REVIEW_C
P3-4). Deadline receipts (REVIEW_C P2-1): the self-cancel fires at min(approval, grant, not_after) and the port self-verifies at the Host
clock, so a `deadline` cancel-* receipt exists only when `not_after` ends strictly before both expiries; at either expiry there is no
receipt (generic wedged/failed). Signing one after expiry would need a new authority rule: owner decision, not taken. Compatibility: the stage set is CLOSED, so an older controller fails the signed
decode on a newer stage and falls back to the generic `wedged:reset-receipt-refused` settle: refused, never misclassified. Kept generic
and why: enable error (the binding digest only exists after a successful enable), settle / source-return / host-settle (retried turn
errors, not wedges), read / finalize (self-cancel causes settled `cancelled`, not wedges), transfer-missing / stage-invalid (before the
binding / Host bug). Specs: `remote_container_reset_failure_stages_v3_spec.spl`, `host_remote_build_reset_stages_v4_spec.spl`.

### remote-run settle and unopened-slot hardening (milestone_0043 opus re-review, 2026-11-19, specs NOT_RUN)
- Settle seam: `RemoteRunLinkV1.settle` -> `controller_dispatch_remote_settle_v3`. It is one turn, never
  sends, never changes phase, and reaches the root's single journal writer on a FAILED (cleanup) owner too.
  `link.edit` (`dispatch_remote_ready_v3`) is ready-only, so a settle after a failed send must never use it.
  Trap: `remote_run_wait_v1` returns the owner's sticky error first, so the settle reads `turn.response` directly.
- Flow order: open record encoded and sized -> admit -> prepare -> execute. A refused admit has zero Host
  effect. A pre-execute failure settles via `remote_run_settle_before_execute_apply_v1`: `cancelled` only
  when the controller's create-only execute archive (`controller_dispatch_remote_execute_key_v3`) is
  absent, otherwise `outcome-unknown`.
- Unsigned Host text never ends a row. A settled reply with no bundle (`unbundled`) and a refused reset
  receipt both settle `outcome-unknown`. A `failed`/`wedged` stage reply is `invalid` (the Host never
  sends one). Reaped matches only the exact typed `host_service_error_payload_v2` for this operation's
  collect.
- Accept and reset authority: `issuer == controller_id` plus `distributed_verify_grant_approval_from_snapshot_v2`.
- Grant TTL must cover task timeout + collect bound + 120 s. Checked at grant issuance and again before execute.
- Host: an executing remote-build slot with no opened build is settled cancelled/no-workload `deadline`
  once the execute pair's window passes on the GRANT clock (`linux_service_remote_build_unopened_expire_v4`),
  and open is refused past that window.
- Owner decisions still open (outcome-unknown exit, retained storage, prepared release, quarantined-root
  settle, signed reaped receipt, unopened cancel): records milestone_0043 `OWNER_DECISIONS.md`. Decided in
  milestone_0045 (below) except the quarantined-root settle.

### remote-run completion (milestone_0045, owner decisions 2026-11-19, specs NOT_RUN)
- LATE-RECEIPT EXCEPTION (decision 5; the ONE narrow exception to "expired approvals are refused"): a reset-failure
  receipt may be signed by the Host and accepted by the controller after the approval/grant window, ONLY to journal
  `failed` for that exact op. `remote_container_reset_failure_late_context_v3` re-evaluates the authority at
  `min(approval.expires_at, grant.expires_at) - 1` once now is past it; `signed_at` must still be <= the real clock and is
  clamped to that instant. Issuer, snapshot, generation, revocation and key expiry still apply. Completions never take it
  (`remote_run_context_v1(..., receipt)` uses it only for the reset wire). The deadline cancel-* stages now get receipts.
- Signed reaped receipt (decision 4): every reset-failure stage is Host-signed; the controller-built constructor,
  `accept_reset_failure_v3` and `remote_run_service_restart_receipt_v1` are gone. Collect after a restart: stored reply
  replay -> `host_remote_build_reaped_receipt_v4` (reap index -> reap record task digest -> open archive under the prior
  fence -> port signs `service-restart` with empty native id/binding at the grant clock -> archived no-replace BEFORE the
  answer) -> otherwise the typed refusal, settled `outcome-unknown` by the controller.
- Prepared reservation between prepare and execute (decision 3): no route; it waits for its `prepare_deadline_ms`.
  No controller cancel of a never-opened slot (decision 6 not chosen).
- `remote-run resume --dispatch-root R --config-digest D --spec DIR --out OUT` (decision 1, while the signed window
  is open): no new Host effect. Sequence: begin (status) -> read the controller's create-only open record
  (`controller-remote-open-v3/<sha(op)>.sdn`, archived INSIDE the admit turn by
  `controller_workload_store_admit_remote_build_v1(..., open_record, now)`) and execute archive -> collect/output frames
  only -> the same accept / reset-receipt edits. The spec dir is re-authored with the ARCHIVED `not_after` and must
  reproduce the archived record byte for byte (`remote-run-resume-spec-differs`); the pair/request are never re-authored.
  Refused at/after `min(approval, grant)` expiry (`remote-run-resume-window-ended`); its bounded wait sends no cancel and
  settles `outcome-unknown` (`resume-wait-bounded`). Runs admitted before this change have no open archive
  (`remote-run-resume-unarchived`).
- `remote-run abandon --dispatch-root R --config-digest D --key-store K --approver A --operation O --grant-id G
  --expires-in-ms T` (decision 1, after the window): NO Host contact. Issues a `remote-run-abandon` pair through the
  host-action class (`controller_host_action_issue_v1`; kind added to `CONTROLLER_HOST_ACTION_KINDS_V1`, never sent to a
  Host) with payload digest = the row's envelope digest, then `remote_run_abandon_apply_v1` runs on the root's retained
  store (`controller_workload_store_edit_journal_v1` + `root.retain_v3`): issuer == controller, class, snapshot verify at
  the grant clock, row digest, archived open record proves `now >= min(approval, grant)` of the RUN, then a create-only
  `controller-remote-abandon-v1/<digest>.sdn` record and `failed` bound to its digest. `failed` never enters
  `REMOTE_RUN_SETTLE_STATES_V1`. Approver keys must enroll `remote-run-abandon`.
- VERSION SKEW: a controller older than milestone_0045 refuses a Host-signed `service-restart` and a late receipt and
  settles `outcome-unknown`; upgrade the controller first (same rule as #10398/#10399).

## Unavailable-host rows (2026-11-19)

Every unavailable host or capability row (spec execution NOT_RUN, container live rows, Windows/FreeBSD/VM hosts, live
remote enrollment, operator key-policy enrollment, agent workspace close) has an open BLOCKED Todo DB row (455-459 and
193-195) and a resume plan with owner, prerequisite, resume command and retained artifacts in
`doc/03_plan/agent_tasks/simple_orchestrator_remote_completion.md`. None is PASS.
