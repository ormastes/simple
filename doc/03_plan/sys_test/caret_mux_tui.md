# Caret CoreMux and optional terminal extension qualification

Selected scope: option A and N2, 2026-10-25. Requirements:
`doc/02_requirements/feature/caret_mux_tui.md` and
`doc/02_requirements/nfr/caret_mux_tui.md`.
Architecture/detail owner: `doc/04_architecture/caret_mux_tui.md` and
`doc/05_design/caret_mux_tui.md`. Capture plan: `caret_mux_tui_tui.md` in that
design directory. These are acceptance obligations, not measured results.

**Status: NOT_RUN.** No executable shared-contract specimen is created until
the production contract and both real backend owners are callable. The reserved
path is `test/03_system/app/llm_caret/feature/caret_mux_tui_spec.spl`; its future
manual mirrors that path under `doc/06_spec/`. Do not add empty cases, fake
failure placeholders, a test-only backend, or a wrapper around existing wrappers.

## Interface agreement and ownership

The architecture owner proposes `common.contracts.mux.core_v1.CoreMuxV1`,
`MuxHandleV1`, `MuxObjectRefV1`, `MuxSnapshotV1`, `MuxErrorV1`, `MuxCapabilityV1`,
`MuxQueryV1`, `MuxCommandV1`, `MuxMutationV1` and `MuxEventBatchV1`.
`query`, `execute` and `poll_events` reach the real selected backend owner;
`mux_connect_v1` selects Smux or Tmux explicitly and binds a namespace.
Optional acquisition uses `mux_acquire_terminal_layout_v1` and
`mux_acquire_terminal_presentation_v1`. Names are pending architecture approval
and real implementation; this plan is not an invented callable interface.

After the contract is concrete, setup uses `caret_mux_setup` to acquire real
owner handles and owned isolated namespaces. `caret_mux_check_state` queries
the authoritative snapshot and verifies expected object identity, geometry,
focus, child state and resource ownership. It must not reconstruct backend
decisions or return success without querying them. Primary flows use
`step("...")`; setup can be `@inline` with normal docgen expansion. Missing
executable, endpoint, provider, permission or required capability fails setup
with a preserved reason. The campaign records dependent rows BLOCKED/NOT_RUN,
never a successful empty scenario.

## Required feature traceability

Every shared row below runs independently on **real smux and real tmux**. Backend
selection is fixed for a row: unavailable tmux must not silently select smux.
Legacy argv/format compatibility runs separately through actual Caret callers.

| Requirement | Planned production-connected scenarios and oracle |
| --- | --- |
| REQ-CMUX-001 | Explicitly connect each backend; create/query sessions, windows and panes through the shared owner. Require real server/child identity and backend/version receipts. Run the audited Caret command/format matrix separately; a model or successful command rendering is insufficient. |
| REQ-CMUX-002 | Create detached sessions in two namespaces; discover them from another client; rename, attach/detach and terminate owned objects. Closing Caret leaves the owner and background child running. Reject missing/ambiguous names without selecting a sibling. Namespace-specific teardown leaves the other namespace alive. |
| REQ-CMUX-003 | Launch a real argument-reporting child with spaces, empty args, Unicode, cwd and environment, then independently query PID/output. Distinguish literal bytes, named Enter, paste-mode delimiters, shell-command evaluation and notifications. A foreign session target cannot change focus or receive output. |
| REQ-CMUX-004 | Reuse the three SMUX geometry regression cases; shared rows add real child-observed resize, zoom/restore, multiple windows/clients, titles, borders, hide/show and rebalance through actual Caret flows. Check stable IDs and authoritative rectangles. Refused mutations preserve prior geometry, or explicit PartialFailure reports exactly what changed. |
| REQ-CMUX-005 | Capture real child output containing wrapped lines, escapes, wide/combining glyphs and bounded history. Compare plain/styled and joined/unjoined semantics against specified child transcript/cell positions. Exercise exited and hidden objects and the exact audited tmux formats; do not invent IDs or omit inconvenient objects. |
| REQ-CMUX-006 | Query each operation's native/emulated/unavailable classification, limits, constraints, backend/version and owner generation. Keep execution evidence separate. Invoke after owner changes or a capability disappears: the stale advertisement cannot authorize success. Any required unavailable capability blocks replacement qualification. |
| REQ-CMUX-007 | Acquire optional leases explicitly. Supported real owners execute complete-plan/presentation operations and return owner-bound revisions. Unsupported acquisition/operation returns typed Unsupported and no mutation, child launch, lease leak, event or automatic migration. Required Caret messaging/title/border operations are not reclassified as optional. |
| REQ-CMUX-008 | Trigger all nine typed outcomes: Unsupported, InvalidRequest, InvalidTarget, PermissionDenied, Unavailable, StaleRevision, Busy, Timeout and PartialFailure. Check commit state, observed revision and cleanup evidence. Reconcile timeout with unknown commit by querying operation/object identity before any non-idempotent retry. |
| REQ-CMUX-009 | Launch the ordinary Caret TUI as a real pane child on both backends. Use existing shared semantic UI commands/widgets, checking focus/input and resize. Optional host surfaces use terminal cell geometry only; no new GUI/web/widget system is accepted. |
| REQ-CMUX-010 | Keep shared semantics, existing Caret caller compatibility, backend-only optional contracts and live host execution as separate result categories. Preserve actual case counts and receipts; source scans, discovery, decoder-only tests and command strings cannot qualify native support. |
| REQ-CMUX-011 | Admit an actual Phase 3 producer/full CLI or matching standalone runner using generation/runtime/Hello lineage. Compile SMUX with that producer and verify product sanity. Phase 2 rebuilds and seed substitution are disallowed. Native specs and docgen require their own callable CLI path; qualified reviewed changes land by PR to release/1.0.0. |

For unsupported/refused operation checks, take a fresh owner snapshot immediately
before and after. Compare revision and mutation-sensitive state: objects, focus,
geometry, child identity, input sequence, notification delivery, leases and
cleanup resources. A clock or already-running child's unrelated output can
advance independently; retain those events separately instead of hiding a
mutation in a blanket snapshot normalization. Check that no operation-correlated
events or native side effects occurred. Failure to observe the owner is
Unavailable/unknown evidence, never proof of unchanged state.

## N2 measurements and failure controls

| NFR | Execution and retained evidence |
| --- | --- |
| NFR-CMUX-001 | Run the shared and Caret lifecycle rows on each real backend, tied to source/producer/runtime/host. An optional Unsupported refusal case may satisfy its refusal contract, but its feature remains UNSUPPORTED, not executed or supported. |
| NFR-CMUX-002 | Pin local CPU/host/provider/terminal fixtures. Record cold connect/build/startup separately. After ten declared warm-up calls, retain 200 metadata samples and 100 layout samples per backend. Metadata timing spans caller submission to validated reply; layout timing ends only when independent child/rendered state settles. Report full distributions and nearest-rank p95: <=100 ms and <=250 ms respectively. Timeouts/refusals remain failures, not omitted samples. |
| NFR-CMUX-003 | Execute a continuous real 24-hour session/reconnect soak on each qualified backend. Timestamp start/end with monotonic duration and wall-clock receipts. Include slow consumers, bounded output/event floods, abrupt client/server disruption, cleanup and concurrent layout conflicts. A shortened, interrupted or simulated run remains incomplete and cannot inherit a soak PASS. |
| NFR-CMUX-004 | Baseline per backend: two isolated namespaces, each with two sessions, at least four total panes and two clients (eight panes/four clients overall). Distribute panes across multiple windows; bind two clients to one session during shared-view cases. Record larger configured scales explicitly. Test every advertised object limit and one-over-limit refusal separately, including host constraints. |
| NFR-CMUX-005 | Record configured byte/item/queue/capture limits and independently observed backpressure. Sample baseline/peak/settled RSS, process/handle counts, refused/dropped work and pending cleanup. Log rotation and capture bounds apply to test collectors too. Retained server sessions are not called leaks; unexpected descendants/handles or incomplete teardown are failures. |
| NFR-CMUX-006 | Kill a client without detach, reconnect with a fresh lease and verify surviving geometry/capacity. Restart/kill the server and query old handles/references: old owner generations cannot address replacement objects. Graceful detach alone does not satisfy this gate. |
| NFR-CMUX-007 | Real child/rendered Unicode/control corpus checks scalar counts, UTF-8 bytes and display-cell coordinates separately. Cover alternate screen, resize, zoom/restore, cursor filtering and input routing. A notification ACK requires evidence of successful native rendering; captured protocol text or queued delivery is insufficient. |
| NFR-CMUX-008 | Use before/after authoritative snapshots and operation-correlated native evidence for refused/unsupported commands. Exercise conflicting complete-plan revisions and interrupted multi-step mutations. If tmux lacks stronger atomicity, retain that limitation/PartialFailure; do not advertise atomic success or roll back only the test's model. |
| NFR-CMUX-009 | Finite per-command and whole-process containment; reuse unchanged green evidence. One shared attempt ledger counts relevant prior cycles across sessions/worktrees toward the hard limit of six. Missing Phase 3/provider/backend yields BLOCKED/NOT_RUN. Do not create a new output directory to reset a failed campaign. |

The soak workload is finite despite its duration: schedule one bounded batch per
minute for 1,440 batches, with bounded command counts, buffers and operation
deadlines. At declared disruption checkpoints, reconcile owner state before the
next batch; no retry-until-green loop is permitted. Run one backend cohort at a
time unless root admits independent resource budgets. The full soak has a hard
deadline of 24 hours plus a declared finite teardown allowance. Completion needs
24 hours of actual observed workload plus terminal cleanup, not merely an elapsed
timer or a PASS marker. An early failure stops and preserves the incomplete run.

## Reuse and fixture gates

Reuse `smux_major_features_phase3_spec.spl` (three composition cases), the
existing Caret messaging suites (13 owned specs), SMUX service/model/protocol
specs and independent-owner/client native fixtures. Do not duplicate those
checks in the shared contract: add only mapping/semantic obligations that the
existing evidence cannot prove. Messaging suites must retain their actual
boundary; acknowledgment bookkeeping alone does not prove native display.

Before implementation of the reserved spec, the architecture owner must confirm
the real contract paths and concrete snapshot/error fields, and each backend
owner must provide callable setup/cleanup and native executable prerequisites.
Only then write real assertions; absence of a fixture remains a missing
deliverable, not a silent skip or fake failing substitute.

New structured configuration and campaign/evidence records use SDN by default.
Record actual namespace/lease/object identities, observed backend version,
operation/revision/commit state, source hashes, Phase 3/runtime/provider receipts,
monotonic times, fixture argv, event bounds, output hashes and terminal cleanup.
JSON is an explicit interoperability export only. Preserve existing immutable
historical and required wire receipts as-is. Do not store tokens in reports.

## Completion gate

All requirements, both backend cohorts, actual Phase 3 SMUX build/sanity, shared
and legacy contracts, applicable optional execution/refusal cases, N2 latency,
stress, crash/reconnect, Unicode and the full per-backend 24-hour soak need real
evidence. Docgen must produce the modern manual with zero stubs. Source-only
design, feature implementation or an authored spec is not qualification.

Current result for every new contract/N2 row: **NOT_RUN**. Production interfaces,
backend fixtures and Phase 3 admission remain prerequisites. No compiler or
backend process was launched while preparing this plan.
