# Mission-Critical Infrastructure Hardening V2 — System Test Plan

**Status:** implementation-ready plan
**Selection:** `C1 + O1 + R2 + M2 + N2`
**Executable spec target:** `test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl`
**Generated operator manual:** `doc/06_spec/03_system/infra/mission_critical_infra_hardening_v2_spec.md`

## Restart12 infrastructure lane status (2026-08-14)

This is the canonical execution plan for the fresh detached `restart12-infra`
lane.  The lane owns the host-independent compiler, SimpleOS-manifest, packed
rendering, allocation, process, and aggregate-contract hardening needed before
the release-facing evidence producers may be trusted.

Current acceptance inventory at `origin/main` (`034b7466c8a`):

- [ ] Compiler admission fixtures use supported whole-value reconstruction;
  tamper tests distinguish pre-hash rejection from correctly re-hashed later
  validation failures.
- [ ] Draw IR generation admission persists active/retired state, fails closed
  at capacity and terminal generation, and recovers only through explicit
  abort/retire transitions.
- [ ] Relaxed allocation profile identity is canonical SHA-256 and the
  fault-injection telemetry/rollback ledger is stable.
- [ ] The certified SimpleOS manifest has canonical content identity, binds
  every payload and stress receipt, and rejects PASS-like evidence on
  unselected cells.
- [ ] DrawIR-v3 owns fixed packed slots, encoding cursor/content hashes,
  immutable sealed publication, a bounded queue, Engine2D consumption
  verification, and retirement.
- [ ] Aggregate receipt lookup guards absence before indexing and all focused
  compiler/rendering/allocation/SimpleOS/aggregate tests pass once.
- [ ] Verification gates for changed compiler/core/lib and rendering scope pass
  once, with no executable specs under `doc/06_spec` and no new runtime/env
  facade bypass.

Known release blockers outside this isolated implementation lane remain
fail-closed: independently signed peer compiler evidence, live trust-key
provisioning, current QEMU/hardware and browser/RenderDoc/Vulkan evidence, a
provenanced target-native SimpleOS compiler payload, platform-specific Metal
evidence, and the 24-hour stress run.  These prevent a mission-critical release
PASS but do not excuse failures in the host-independent contracts above.  This
lane reports `WARN` after a reachable push when only those external evidence
rows remain blocked; any owned acceptance failure prevents integration.

Bootstrap cycle 1 exposed an owned compiler blocker before acceptance testing:
Stage 2 rejected an unparenthesized multiline `if` continuation in the typed
storage view producer.  The bootstrap-safe grouping fix is in this lane and the
language divergence is tracked in
`doc/08_tracking/bug/stage2_multiline_if_continuation_2026-08-14.md`; the next
bootstrap cycle must advance beyond this parse point.

Cycle 2 advanced to the same producer's earlier multiline admission predicate,
confirming the divergence applies generally rather than only to tuple-derived
conditions.  That predicate now uses the same explicit grouping.  Cycle 3 is
the final permitted bootstrap/fix attempt for this lane.

Cycle 3 passed both corrected predicates and completed the Stage 2 build and
sanity gate, then the fresh pure-Simple Stage 2 compiler segfaulted while
self-hosting Stage 3 (`stage3-native-build`, exit 139).  The three-cycle cap is
exhausted.  Therefore the host-independent focused specs and compiler/core/MCP
runtime gates remain unexecuted rather than being rerun through the stale
release compiler or substituted with bootstrap-seed evidence.  Integration is
`WARN`, with this owned Stage 3 crash still open; it is not a mission-critical
verification PASS.

**Stale-evidence recovery:** The authoritative producer, prerequisites, and
exact resume command for every report rejected by the 2026-08-11 baseline are
maintained in
`doc/08_tracking/bug/mission_critical_infra_hardening_v2_wave1_red_2026-08-11.md`.
The aggregate is rerun once only after all nine owners have produced current
passing evidence; timestamp edits and blocked hardware-row promotion are
prohibited.

**Current host-independent evidence (2026-08-11):** The authoritative storage
formal producer `sh scripts/check/check-simpleos-storage-formal-proofs.shs`
passes against the current DB-storage, FAT32, and NVFS Lean projects. Its report
is `doc/09_report/simpleos_storage_formal_proofs_2026-08-11.md` and its retained
log is
`build/evidence/mci-v2/formal-storage-20260811/storage_integrity_formal.log`.
Treat this as the formal-model row only; native/QEMU storage and the release
aggregate remain active.

## Acceptance rule

The aggregate result is PASS only when every selected-profile scenario below
executes once against exact-current artifacts, returns zero, and writes a
complete evidence manifest. A skipped, unavailable, timed-out, stale,
synthetic, unknown, source-inspection-only, cached-from-another-run, or missing
row is BLOCKED/FAIL, never PASS. Negative controls must fail for their intended
reason. Green gates are not rerun in the same session.

Every SSpec `it` block must contain a real built-in matcher assertion. Until a
real endpoint exists, its helper must call `fail("MCI endpoint not implemented:
<name>")`; `pass_todo`, empty helpers, synthetic success, and
`expect(true).to_equal(true)` are forbidden.

## Frozen scenario vocabulary

Displayed flows use only these manual steps:

1. `step("Prepare an isolated mission-critical evidence run")`
2. `step("Admit exact-current compiler and tooling artifacts")`
3. `step("Exercise the certified SimpleOS platform manifest")`
4. `step("Exercise packed rendering and backend provenance")`
5. `step("Exercise strict and relaxed allocation profiles")`
6. `step("Exercise bounded concurrency and process failure paths")`
7. `step("Verify freshness, bounds, isolation, and performance budgets")`
8. `step("Review the fail-closed aggregate evidence manifest")`

Frozen setup/checker helpers:

- `setup_mci_isolated_run(profile_id)`
- `setup_mci_negative_control(control_id)`
- `run_mci_compiler_admission(fixture_id)`
- `run_mci_tooling_admission(profile_id)`
- `run_mci_simpleos_cell(cell_id, fault_id)`
- `run_mci_render_profile(profile_id, fault_id)`
- `run_mci_allocation_profile(profile_id, fault_id)`
- `run_mci_process_profile(profile_id, fault_id)`
- `run_mci_stress_profile(profile_id, duration_seconds)`
- `check_mci_receipt(receipt, expected_code)`
- `check_mci_no_partial_publication(receipt)`
- `check_mci_evidence_integrity(manifest)`
- `check_mci_budget(manifest, metric_id)`
- `check_mci_traceability(manifest)`
- `check_mci_aggregate(manifest, expected_status)`

All runners return a typed receipt containing `run_id`, `profile_id`,
`generation_id`, binary/source/config hashes, host/guest identity where
applicable, UTC start/end timestamps, exact command, bounded timeout, exit
status, typed result/error code, and artifact paths.

## Functional requirement scenarios

| Requirement | Happy-path executable scenario | Edge scenario | Failure/negative-control scenario | Required evidence | One-run gate |
|---|---|---|---|---|---|
| REQ-MCI-001 | `MCI-COMP-001` admits an exact-current pure-Simple compiler and executes every discriminating emitted fixture | `MCI-COMP-002` distinguishes two otherwise valid compiler builds by source/config identity | `MCI-COMP-003` separately injects Rust-seed, hybrid, stale, unknown, missing-function, and non-executable artifacts; each is rejected with a typed code | provenance receipt, hashes, fixture stdout/status, lineage graph | `sh scripts/check/check-mci-v2-compiler-admission.shs --evidence build/evidence/mci-v2/compiler` |

The compiler producer derives current source/config manifests, requires an
authenticated pure-Simple parent chain and pinned live trust policy, then
compiles a fixed repository fixture and inspects its ELF/function evidence.
Live trust is deliberately `unprovisioned` until an operator pins the key.
Fixture mode uses ephemeral trust and records `CONTRACT_ONLY`. It runs two
isolated copies of the snapshotted source/config inputs, requires identical
artifact and fixture-capture hashes, and proves a byte-corrupted candidate is
rejected by identity. It emits only
`compiler.cross-host-comparison.unsigned.template`: the schema requires an
independently signed peer host/environment/artifact/capture receipt and remains
`BLOCKED_PENDING_INDEPENDENT_SIGNED_PEER`. These controls exercise the
COMP-002/003 and NFR-003/004 contract without claiming live or cross-host
evidence; all four scenarios remain blocked until that peer evidence exists.
The fixed fixture is snapshotted and digest-bound before compilation; its
`mci_admission_add` symbol and semantic stdout are checked in the emitted ELF.
The complete tracked compiler/app/lib input set is copied to a private
digest-verified snapshot, revalidated against the worktree after capture, and
the compiler consumes only that snapshot. This prevents a manifest/build
TOCTOU mismatch while concurrent worktree changes after capture remain
irrelevant to the admitted build.
The parent receipt has its own verified Ed25519 signature/key. Live mode blocks
on dirty or untracked build inputs, and COMP-001 alone remains aggregate-blocked.
| REQ-MCI-002 | `MCI-TOOL-001` executes compiler, lib, MCP, LSP, bootstrap tool, lint, duplication, whole-test, perf, runtime-contract, and direct-env checks into one tooling manifest | `MCI-TOOL-002` proves maximum output/capture and timeout boundaries without truncating identity metadata | `MCI-TOOL-003` forces one stale internal row, timeout, unavailable tool, nonzero exit, and oversized capture; the single tooling manifest remains blocked | one tooling-owner receipt, its complete internal row manifest, and bounded capture metadata | `sh scripts/check/check-mci-v2-tooling-admission.shs --evidence build/evidence/mci-v2` |
| REQ-MCI-003 | `MCI-OS-001` exercises every selected manifest cell through boot, mount, target listing, arbitrary FS program, lineage, identity, and run correlation | `MCI-OS-002` retains all 24 cells visibly while certifying only the selected subset | `MCI-OS-003` removes each required witness in turn and attempts an umbrella claim; both cell and umbrella claim fail closed | versioned manifest, guest logs, boot/mount/list/run transcripts, hashes, correlation IDs | `sh scripts/check/check-mci-v2-simpleos-manifest.shs --evidence build/evidence/mci-v2/simpleos` |
| REQ-MCI-004 | `MCI-OS-004` executes compiler/interpreter/loader payloads from canonical guest filesystem placements | `MCI-OS-005` verifies `/usr/bin`, `/bin`, `/sys/apps`, and `/SYS/SIMPLETOOL.SDN` identities agree across aliases/metadata | `MCI-OS-006` deletes, corrupts, substitutes, or makes each payload non-executable; admission fails before claim publication | guest filesystem inventory, payload hashes, invocation transcripts and exit codes | same SimpleOS manifest gate |
| REQ-MCI-005 | `MCI-REN-001` count-plans, admits, packs, seals, queues, consumes, and retires a DrawIR-v3 generation through semantic/layout owner to Engine2D | `MCI-REN-002` accepts exact-capacity command/glyph/image/queue/in-flight values with immutable active generation | `MCI-REN-003` exceeds every capacity by one and attempts grow/truncate/clamp/fallback/mutation; emission is rejected before publication | generation receipt, planned/used capacities, composition hash, queue history, owner chain | `sh scripts/check/check-mci-v2-rendering.shs --evidence build/evidence/mci-v2/rendering` |
| REQ-MCI-006 | `MCI-REN-004` proves generation and real backend/device provenance, semantic Draw IR, structured HTML interaction, and exact readback where profile claims it | `MCI-REN-005` validates a real RenderDoc artifact and proves transient font atlas/cache state is absent from Draw IR | `MCI-REN-006` injects synthetic handle, screenshot-only UI, mismatched readback/device, invalid RenderDoc, and atlas material in Draw IR; each fails | typed rejection receipts, UI access history, CPU/device readback, RenderDoc validation, Draw IR inspection | same rendering gate |
| REQ-MCI-007 | `MCI-ALLOC-001` proves zero post-ready allocation in strict contexts and sealed preallocated per-domain arena use in permitted relaxed contexts | `MCI-ALLOC-002` allocates the final permitted byte in a noncritical relaxed arena | `MCI-ALLOC-003` attempts relaxed allocation in kernel, ISR, storage-commit, ownership-publication, cross-domain, unsealed, and post-ready strict contexts | allocation trace, domain/context IDs, seal/quota/generation receipt | `sh scripts/check/check-mci-v2-allocation.shs --evidence build/evidence/mci-v2/allocation` |
| REQ-MCI-008 | `MCI-ALLOC-004` records quota/high-water/generation and deterministically rolls back an exhausted operation without partial publication | `MCI-ALLOC-005` exhausts at the exact quota and returns typed exhaustion in the provoking operation | `MCI-ALLOC-006` injects every allocation failure point and tries cross-domain corruption, committed-storage mutation, isolation bypass, and fallback; state hashes remain unchanged | allocation artifact/template own 004/005; distinct fault-injection artifact/template owns 006 and its ledger/hash evidence | same allocation gate, two aggregate rows |
| REQ-MCI-009 | `MCI-PROC-001` completes bounded parallel work and subprocess capture within fixed queue/in-flight limits | `MCI-PROC-002` cancels at admission, active execution, and completion boundaries deterministically | `MCI-PROC-003` injects timeout, capture overflow, queue overflow, and `pid` values `-1` and `0`; every kill/wait rejects invalid PID and no unrelated process is affected | pool/queue timeline, cancellation receipt, bounded output metadata, PID audit | `sh scripts/check/check-mci-v2-process-safety.shs --evidence build/evidence/mci-v2/process` |

The process producer additionally requires run/source/config/timestamp/key
arguments and an admitted exact-current pure-Simple runner. C-only output is
diagnostic and exits blocked. Passing output remains an unsigned release
candidate until the external producer-key operator signs the canonical receipt.
`test/01_unit/scripts/mci_v2_process_safety_contract_test.shs` distinguishes
those states without claiming that its local fixture is release evidence.
| REQ-MCI-010 | `MCI-AGG-001` validates the collector contract against complete fresh same-run fixtures; this is not a release PASS | `MCI-AGG-002` combines contract fixtures in different completion orders and produces the same deterministic aggregate | `MCI-AGG-003` injects every prohibited evidence class (stale, unavailable, skipped, unknown, synthetic, screenshot-only, source-only, cached); claim stays blocked | canonical shell contract: `test/01_unit/scripts/mci_v2_aggregate_contract_test.shs`; release report remains BLOCKED until real producers, including an independent reviewer, exist | `sh test/01_unit/scripts/mci_v2_aggregate_contract_test.shs` |
| REQ-MCI-011 | `MCI-DOC-001` maps all 20 requirements to executable scenario IDs and generates a zero-stub readable operator manual | `MCI-DOC-002` verifies every displayed helper is visible as a manual step or complete folded source | `MCI-DOC-003` injects an unmapped requirement, placeholder assertion, stale doc, and executable spec under `doc/06_spec`; quality gate fails | traceability matrix, docgen report, freshness report, layout audit | `sh scripts/check/check-mci-v2-traceability.shs --evidence build/evidence/mci-v2/docs` |

Current classification: only the negative traceability scenario has focused
executable contract evidence. The docgen happy and helper-visibility scenarios
remain blocked until real docgen creates the zero-stub manual and provenance
receipt; a traceability receipt must not list those blocked scenarios.

## NFR scenarios and budgets

Exact numeric rendering/runtime budgets are profile data frozen by architecture
and detail design, not literals hidden in the spec. Missing budget values fail
admission.

| NFR | Nominal/edge scenario | Failure/stress scenario | Required evidence | One-run gate |
|---|---|---|---|---|
| NFR-MCI-001 | `MCI-NFR-001` confirms zero skipped/unknown identities and zero stale reports at the freshness boundary | `MCI-NFR-002` supplies one just-expired report and one unknown identity; aggregate blocks | freshness calculation and identity inventory | aggregate gate |
| NFR-MCI-002 | `MCI-NFR-003` compares two clean-host compiler builds and executes every emitted fixture | `MCI-NFR-004` perturbs an unrecorded input and corrupts one emitted fixture; reproducibility fails | two environment manifests, artifact hashes, fixture receipts | compiler-admission gate |
| NFR-MCI-003 | `MCI-NFR-005` proves explicit timeout, bounded capture, and one bounded scan/index per gate | `MCI-NFR-006` hangs a child, floods output, and requests repeated hot-path tree scans; termination/admission is deterministic | timer/capture telemetry, scan counters, negative-control ledger | tooling and process gates |
| NFR-MCI-004 | `MCI-NFR-007` proves strict zero allocation and nominal relaxed high-water `<= 80%` | `MCI-NFR-008` drives quota exhaustion and observes typed return within that operation | allocation event trace and operation timestamps | allocation gate |
| NFR-MCI-005 | `MCI-NFR-009` enumerates the stable ID/name registry and injects every registered allocation failure point | `MCI-NFR-010` verifies canonical subject and independently committed-domain hashes remain unchanged and rollback restores the prior generation | one valid ledger row per registry entry; before/after SHA-256 hashes | distinct `fault-injection` aggregate row from the allocation producer + `test/01_unit/lib/nogc_sync_mut/mission_critical/domain_arena_v1_spec.spl` |
| NFR-MCI-006 | `MCI-NFR-011` records declared command/glyph/image/queue/in-flight/RSS/p95/p99/deadline budgets under nominal and exact-capacity loads | `MCI-NFR-012` exceeds each count and deadline independently; rejection precedes emission and no truncation occurs | raw samples, percentile calculation, capacity/rejection receipts | rendering gate |
| NFR-MCI-007 | `MCI-NFR-013` records warm CLI/MCP/LSP startup/request p95 and max RSS on pinned realistic fixtures | `MCI-NFR-014` injects a result beyond each configured regression budget; admission blocks | raw timing/RSS samples, fixture hashes, baseline comparison | tooling-admission gate |
| NFR-MCI-008 | `MCI-NFR-015` runs each certified cell for 24 hours with bounded resources and zero invariant violation | `MCI-NFR-016` marks an unavailable/interrupted cell blocked and proves it cannot support a broader claim | start/end timestamps, resource series, cell result and invariant counters | `sh scripts/check/check-mci-v2-stress.shs --duration 24h --evidence build/evidence/mci-v2/stress` |
| NFR-MCI-009 | `MCI-NFR-017` admits an ephemeral, separately keyed canonical reviewer decision binding identity/role/scope/run/source/config/time and the full content-addressed evidence graph | `MCI-NFR-018` rejects missing identity, producer-key/self-issued, stale, replayed candidate, valid A-to-B artifact/receipt/signature replacement under an old review, and unexpected-receipt add/remove | focused signed/hash-bound reviewer contract only; a real independently operated reviewer producer remains required | `sh test/01_unit/scripts/mci_v2_aggregate_contract_test.shs` |

## Execution order and single aggregate gate

The release-facing one-run entrypoint is:

```sh
sh scripts/check/check-mci-v2-release.shs \
  --profile mixed-criticality-high-assurance \
  --evidence build/evidence/mci-v2
```

It runs each subordinate gate at most once in dependency order: compiler,
tooling, SimpleOS, rendering, allocation, process safety, 24-hour stress,
traceability, then aggregate. It records commands and consumes their manifests;
it does not rerun green checks. The runner enforces an explicit per-gate timeout,
fixed capture ceiling, common `run_id`, exact artifact identities, and
`release_blockers=none`. The SSpec invokes this entrypoint only in the final
aggregate scenario; focused scenarios invoke their owning subordinate runner so
failure attribution remains executable and precise.

After the executable spec exists, run docgen exactly once after the final spec
edit:

```sh
bin/simple spipe-docgen \
  test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl \
  --output doc/06_spec --no-index
```

Acceptance requires `0 stubs`, all scenario IDs in the generated manual, and no
`*_spec.spl` anywhere under `doc/06_spec`.
