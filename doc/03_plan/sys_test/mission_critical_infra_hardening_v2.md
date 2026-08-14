# Mission-Critical Infrastructure Hardening V2 — System Test Plan

**Status:** implementation incomplete — WARN handoff
**Selection:** `C1 + O1 + R2 + M2 + N2`
**Executable spec target:** `test/03_system/infra/mission_critical_infra_hardening_v2_spec.spl`
**Generated operator manual:** `doc/06_spec/03_system/infra/mission_critical_infra_hardening_v2_spec.md`

## Authoritative current state (2026-08-14)

This is the canonical execution plan for the fresh detached `restart12-infra`
lane.  The lane owns the host-independent compiler, SimpleOS-manifest, packed
rendering, allocation, process, and aggregate-contract hardening needed before
the release-facing evidence producers may be trusted.

Current integrated baseline is `f26936914d9833a000044757f6475bc7fd6e62cb`,
reachable from `origin/main`. The phase is `impl-in-progress`; the last bounded
bootstrap attempt completed Stage 2 and its sanity check, then the exact fresh
Stage 2 binary segfaulted during Stage 3 self-hosting. This is an owned FAIL,
not an external-host warning and not a verification PASS.

### Completion audit — plan objective versus feature objective

Re-audited on synced `origin/main` at
`d5e954141053728639f36882e706a1ee041b4a87`.

The completed thread objective was narrowly and explicitly: run `$sp_dev` with
parallel plan/guide audits, merge their findings, obtain higher-capability
review, and complete this resumable plan document. Evidence for that objective:

- `/root/acceptance_audit` and `/root/guide_audit` completed read-only audits;
- `/root/higher_model_review` (`gpt-5.6-sol`, xhigh) ended PASS for truthful,
  resumable plan-document completeness after correction rounds;
- `test/01_unit/scripts/mci_v2_traceability_contract_test.shs` remains PASS on
  the synced head;
- executable-source/manual SHA identity, numbered-artifact, direct-env,
  rendering-source-coupling, and `doc/06_spec` layout guards remain PASS;
- plan-document commit `8350cbc8502859104ca1a3b0120560ffb3f84b3c` is reachable
  from `origin/main`.

That completion does **not** complete the mission-critical feature, verify
phase, or release. The umbrella feature remains `impl-in-progress` and BLOCKED
by the owned Stage 3 self-host failure, unexecuted current-head runtime gates,
missing per-scenario executable ownership/docgen provenance, external
QEMU/GPU/RenderDoc/Metal/24-hour evidence, the real independently signed
reviewer receipt, and a final aggregate with `release_blockers=none`. No agent
may use the completed plan-document goal status as evidence that any of those
rows passed.

### Restart12 owned acceptance ledger

| Item | Current classification | Exact source/evidence paths | Exact resume command | Owner | Final reviewer |
|---|---|---|---|---|---|
| R12-01 compiler receipt reconstruction | source implemented; current-head execution BLOCKED | `src/compiler/00.common/mission_critical/compiler_admission.spl`; `test/01_unit/compiler/mission_critical/compiler_admission_spec.spl` | `bin/simple test test/01_unit/compiler/mission_critical/compiler_admission_spec.spl --mode=interpreter` after Stage 4 admission | compiler lane | highest-capability Codex |
| R12-02 Draw IR admission lifecycle | source implemented; prior focused contract only; current-head BLOCKED | `src/lib/common/mission_critical/draw_ir_generation_arena_v3.spl`; `test/01_unit/lib/common/mission_critical/draw_ir_generation_arena_v3_spec.spl` | `bin/simple test test/01_unit/lib/common/mission_critical/draw_ir_generation_arena_v3_spec.spl --mode=interpreter` | rendering lane | highest-capability Codex |
| R12-03 allocation SHA-256 and rollback | source implemented; contract-only | `src/lib/nogc_sync_mut/mission_critical/domain_arena_v1.spl`; `test/01_unit/lib/nogc_sync_mut/mission_critical/domain_arena_v1_spec.spl` | `bin/simple test test/01_unit/lib/nogc_sync_mut/mission_critical/domain_arena_v1_spec.spl --mode=interpreter`, then Resume A1 below | memory lane | highest-capability Codex |
| R12-04 SimpleOS manifest identity | source implemented; contract-only | `src/os/sosix/mission_critical/certified_manifest.spl`; `test/01_unit/os/sosix/certified_manifest_spec.spl` | `bin/simple test test/01_unit/os/sosix/certified_manifest_spec.spl --mode=interpreter` then Resume O1 | SimpleOS lane | highest-capability Codex |
| R12-05 packed DrawIR/Engine2D handoff | source implemented; owner contract only; no device proof | `src/lib/common/mission_critical/draw_ir_packed_generation_store_v3.spl`; `src/lib/gc_async_mut/gpu/engine2d/draw_ir_packed_owner_v3.spl`; matching specs under `test/01_unit/lib/common/mission_critical/` and `test/01_unit/lib/gc_async_mut/gpu/engine2d/` | `bin/simple test test/01_unit/lib/common/mission_critical/draw_ir_packed_generation_store_v3_spec.spl --mode=interpreter` then `bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_packed_owner_v3_spec.spl --mode=interpreter` | rendering lane | highest-capability Codex |
| R12-06 guarded aggregate indexing | source implemented; collector contract only | `src/lib/nogc_sync_mut/mission_critical/mci_evidence_manifest_v1.spl`; `test/01_unit/lib/nogc_sync_mut/mission_critical/mci_evidence_manifest_v1_spec.spl`; `test/01_unit/scripts/mci_v2_aggregate_contract_test.shs` | `bin/simple test test/01_unit/lib/nogc_sync_mut/mission_critical/mci_evidence_manifest_v1_spec.spl --mode=interpreter` then `sh test/01_unit/scripts/mci_v2_aggregate_contract_test.shs` | aggregate merge owner | independent release reviewer |
| R12-07 final verification | static results were observed PASS but no hashed receipt was retained; treat as unretained and rerun once after final edits; runtime gates unexecuted | `scripts/audit/direct-env-runtime-guard.shs`; `scripts/audit/numbered-artifact-guard.shs`; `scripts/check/check-rendering-source-coupling.shs` | Resume V1 below after Stage 4 admission | merge owner | highest-capability Codex |

Contract implementation is not release evidence. REQ-MCI-001..011 and
NFR-MCI-001..009 remain BLOCKED unless their row has a fresh, signed, exact-run
producer receipt and executable scenario evidence. The current three broad
SSpec examples are umbrella contract checks; they do not prove all 20 planned
requirement/NFR scenarios individually.

Known release blockers outside this isolated implementation lane remain
fail-closed: independently signed peer compiler evidence, live trust-key
provisioning, current QEMU/hardware and browser/RenderDoc/Vulkan evidence, a
provenanced target-native SimpleOS compiler payload, platform-specific Metal
evidence, and the 24-hour stress run.  These prevent a mission-critical release
PASS and do not excuse failures in the host-independent contracts above. The
already-integrated restart12 implementation handoff is WARN because the owned
Stage 3 failure remains open; it is not a claim that only external rows remain.

### Bootstrap verification-once ledger

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
verification PASS. Retained evidence:

- Stage 2 binary:
  `build/restart12-bootstrap/stage2/x86_64-unknown-linux-gnu/simple`, SHA-256
  `7617c924d6848928f3f7495e3d6691d908505fb677d19b9f07f9697ebf9aaec5`.
- Cycle-3 progress log: `build/restart12-bootstrap/progress-cycle3.log`,
  SHA-256 `d59a1256be2afbe50476919803aca20993ca58e45e7e7a98ee3edd1e07707322`.
- Stage-3 child log is empty because the process died before diagnostic output;
  its empty SHA-256 is not affirmative evidence. Exit 139 was observed on the
  live driver console but no terminal receipt retained it, so the signal result
  is an unretained observation pending the next fresh reproduction.
- Tracking record:
  `doc/08_tracking/bug/stage3_selfhost_exit_139_2026-08-14.md`.
- Exact resume command, in a fresh session because this session exhausted the
  three-cycle cap:
  `sh scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple --full-cli --no-mcp --diagnostics=test --diagnostic-child-compiler=/mnt/data/worktrees/restart12-infra/build/restart12-bootstrap/stage2/x86_64-unknown-linux-gnu/simple --output=build/restart12-bootstrap --jobs=full --progress=build/restart12-bootstrap/progress-resume.log`.

### External host and authority blockers

| Row | Missing prerequisite | Exact resume command | Retained/canonical artifacts | Owner | Final reviewer |
|---|---|---|---|---|---|
| peer compiler + trust | pinned live key and independently signed peer build | Resume C1 below | `build/evidence/mci-v2/compiler/artifacts/compiler.evidence`; `build/evidence/mci-v2/compiler/receipts/compiler.cross-host-comparison.unsigned.template` | compiler operator | independent release reviewer |
| target-native SimpleOS | admitted compiler, bootable current image, QEMU/native host | Resume O1 below | `build/evidence/mci-v2/simpleos/artifacts/simpleos.evidence`; `build/evidence/mci-v2/simpleos/receipts/simpleos.receipt.unsigned.template`; collector artifacts named by the 24-row manifest | SimpleOS operator | independent release reviewer |
| browser/RenderDoc/Vulkan | prepared Vulkan/RenderDoc browser host and real RDOC captures | Resume G1 below | `build/evidence/mci-v2/rendering`, signed rendering manifest, and valid `.rdc` files | rendering operator | independent release reviewer |
| macOS Metal | prepared native macOS Metal host | Resume M1 below | `build/production_gui_web_renderer_parity_evidence_*` and dated parity report | macOS rendering operator | independent release reviewer |
| 24-hour stress | selected certified cells and uninterrupted bounded run | Resume S1 below | `build/evidence/mci-v2/stress/artifacts/stress.evidence`; `build/evidence/mci-v2/stress/receipts/stress.receipt.unsigned.template`; input campaign at `$STRESS_INPUT_DIR` | platform operators | independent release reviewer |
| real independent review | complete content-addressed producer graph and separate reviewer key | Resume R1 below | `build/evidence/mci-v2/reviewer-generation.current`; `build/evidence/mci-v2/reviewer-generations/$CANDIDATE/reviewer.receipt`; `reviewer.sig`; `complete.env` | independent reviewer | release authority |

The external resume commands use explicit operator-provisioned variables; an
unset variable is a visible prerequisite, not permission to invent evidence:

```sh
# Resume C1 — compiler producer
sh scripts/check/check-mci-v2-compiler-admission.shs --mode live \
  --evidence build/evidence/mci-v2/compiler --run-id "$RUN_ID" \
  --compiler "$COMPILER" --provenance "$PROVENANCE" \
  --provenance-signature "$PROVENANCE_SIGNATURE" --trust-key "$TRUST_KEY" \
  --parent-receipt "$PARENT_RECEIPT" --parent-signature "$PARENT_SIGNATURE" \
  --parent-trust-key "$PARENT_TRUST_KEY" --captured-at-utc-ns "$CAPTURED_NS" \
  --valid-until-utc-ns "$VALID_NS" --now-utc-ns "$NOW_NS"

# Resume O1 — SimpleOS producer
sh scripts/check/check-mci-v2-simpleos-manifest.shs \
  --evidence build/evidence/mci-v2/simpleos --manifest "$PLATFORM_MANIFEST" \
  --configuration-manifest "$CONFIG_MANIFEST" --run-id "$RUN_ID" \
  --source-hash "$SOURCE_HASH" --configuration-hash "$CONFIG_HASH" \
  --compiler-receipt-hash "$COMPILER_RECEIPT_HASH" \
  --captured-at-utc-ns "$CAPTURED_NS" --valid-until-utc-ns "$VALID_NS" \
  --now-utc-ns "$NOW_NS" --trusted-key-id "$TRUSTED_KEY_ID" \
  --collector-trust-key "$COLLECTOR_KEY" --collector-key-id "$COLLECTOR_KEY_ID"

# Resume A1 — allocation and fault-injection producer
sh scripts/check/check-mci-v2-allocation.shs \
  --evidence build/evidence/mci-v2 --run-id "$RUN_ID" \
  --source-hash "$SOURCE_HASH" --configuration-hash "$CONFIG_HASH" \
  --captured-at-utc-ns "$CAPTURED_NS" --valid-until-utc-ns "$VALID_NS" \
  --compiler-launcher "$COMPILER_LAUNCHER" \
  --compiler-launcher-receipt "$COMPILER_LAUNCHER_RECEIPT" \
  --compiler-launcher-signature "$COMPILER_LAUNCHER_SIGNATURE" \
  --launcher-trust-policy "$LAUNCHER_TRUST_POLICY" --simple-bin "$ADMITTED_STAGE4"

# Resume S1 — stress producer after a genuine 24-hour input campaign
sh scripts/check/check-mci-v2-stress.shs --evidence build/evidence/mci-v2/stress \
  --input-dir "$STRESS_INPUT_DIR" --run-id "$RUN_ID" \
  --source-hash "$SOURCE_HASH" --configuration-hash "$CONFIG_HASH" \
  --trusted-key "$TRUST_KEY" --trusted-key-id "$TRUSTED_KEY_ID"

# Resume G1 — capture live Simple/Chrome/Electron RDOC evidence, then admit it
sh scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc
sh scripts/check/check-mci-v2-rendering.shs \
  --evidence build/evidence/mci-v2 --manifest "$RENDER_MANIFEST" \
  --manifest-signature "$RENDER_SIGNATURE" --collector-key "$COLLECTOR_KEY" \
  --collector-key-id "$COLLECTOR_KEY_ID" --collector-trust-policy "$RENDER_POLICY" \
  --run-id "$RUN_ID" --source-hash "$SOURCE_HASH" \
  --configuration-hash "$CONFIG_HASH" --captured-at-utc-ns "$CAPTURED_NS" \
  --valid-until-utc-ns "$VALID_NS" --now-utc-ns "$NOW_NS"

# Resume M1 — native macOS Metal/readback production parity producer
SIMPLE_BIN="$ADMITTED_STAGE4" \
BUILD_ROOT="build/production_gui_web_renderer_parity_evidence_$(date -u +%Y%m%d)" \
REPORT_PATH="doc/09_report/production_gui_web_renderer_parity_evidence_$(date -u +%F).md" \
sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs

# Resume R1 — independently administered reviewer
sh scripts/check/check-mci-v2-independent-review.shs \
  --evidence build/evidence/mci-v2 --aggregate-report "$AGGREGATE_REPORT" \
  --candidate-graph "$CANDIDATE_GRAPH" --decision "$REVIEW_DECISION" \
  --decision-signature "$REVIEW_SIGNATURE" --reviewer-key "$REVIEWER_KEY" \
  --reviewer-key-id "$REVIEWER_KEY_ID" --reviewer-trust-policy "$REVIEW_POLICY" \
  --producer-key "$PRODUCER_KEY" --producer-key-id "$PRODUCER_KEY_ID" \
  --now-utc-ns "$NOW_NS"

# Resume V1 — final changed-file/static and compiler/core/MCP gates, once each
sh scripts/audit/numbered-artifact-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/check/check-rendering-source-coupling.shs
test "$(find doc/06_spec -name '*_spec.spl' | wc -l | tr -d ' ')" = 0
bin/simple check src/compiler
bin/simple check src/lib
bin/simple check src/app/mcp
bin/simple check src/app/simple_lsp_mcp
SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
sh scripts/audit/numbered-artifact-guard.shs --staged
sh scripts/audit/direct-env-runtime-guard.shs --staged
git diff --cached --check
```

### SPipe and documentation completion gap

The current manual is hand-maintained and has no current pure-Simple docgen
receipt. `MCI-DOC-001/002` remain BLOCKED until an admitted Stage 4 CLI runs
the canonical `bin/simple spipe-docgen ...` command below with `0 stubs`, after
the executable spec has one real scenario owner for every planned ID. The
internal parallel plan/guide audits completed on 2026-08-14; their findings are
merged here. Internal model review is process quality control and does not
replace the independently signed release-review receipt required by
NFR-MCI-009.

### Implementation handoff and resume order

1. Diagnose and fix the Stage 3 exit-139 owner path in a fresh capped session.
2. Produce and admit an exact-current Stage 4 full CLI; run the essential-tools
   smoke gate against that exact binary.
3. Run each focused compiler/rendering/allocation/SimpleOS/aggregate spec once.
4. Expand the SSpec from three umbrella examples to executable ownership for
   all planned scenario IDs, then run docgen once and review the manual.
5. Run live producer rows, external-host rows, the independent reviewer, and
   finally the release aggregate. Only `release_blockers=none` permits PASS.

**Stale-evidence recovery:** The authoritative baseline is
`/tmp/mci-v2-hardening-matrix-20260811.log`, SHA-256
`cd982a1142beb3cc1a51eb022d7a0d1eb4b849f265813c4a68d51b681280eb38`.
The authoritative producer, prerequisites, and
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
