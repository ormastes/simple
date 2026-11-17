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
  -> `cleaned` -> settle_retired -> d4 clears the retirement -> `returned`; B = quiesce, drop the spawn, then S. d3 repeats until the container reports no error. B drops the spawn without a stored proof digest (open gap vs 11.4). A `Rejected`
  spawn is Blocked `...-native-absence-unproven`. Trap: quiesce must not retire descriptors, the container's
  `fallback_cleanup_v3` retires them (a second retire with a reference is `stale_process_reference`).
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
