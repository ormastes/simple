# RISC-V Gen2 HWIR Foundation — Parallel Plan

| Lane | Scope | Owner | Status |
| --- | --- | --- | --- |
| A0 | Freeze schema/result/config contracts and merge | `/root` | active; v1 stays frozen, v2 trap/retirement contract is versioned |
| A1 | HWIR source/test inventory | `gen2_code_tests`; merge owner `/root` | review complete and merged |
| A2 | Requirements/design/test artifact inventory | `gen2_artifacts` | complete |
| A3 | Worktree ownership audit | `worktree_ownership` | complete |
| A4 | Typed config, strict lowering/emitter, critical driver route and real-MIR Bool extraction | `/root` | v2 source-less trap product implemented; self-hosted CLI evidence blocked by absent deployed runtime |
| A5 | Shared compressed seed and RV32/RV64 adapter splice | `/root` | 25-row common-integer subset has explicit row evidence; full C/Zc remains pending |
| A6 | Hardware-safe compressed adapter review | `compressed_adapter_review` | complete |
| A7 | Declarative ISA capability seed / critical manifest linkage | `/root` | compressed subset truth remains non-advertising/non-release-claimable; scalar I/M/RV64-word schema seed exists, but provider/decoder/toolchain consumers remain pending |
| A8 | Composed-front-end equivalence | `/root` | typed migrating and trap one-entry compositions plus RV32/RV64 GHDL protocol scenarios are implemented; a prepared strict-HWIR host oracle exhausts all 65,536 parcels for each target-trap product, while independent RTL equivalence and the self-hosted receipt remain pending |
| A9 | Stateful HWIR and architectural effects | `/root` | bounded single-outstanding capture/dispatch/retire/effect plan is implemented; a verification-only reset-coupled loopback checks one-entry receipt transport, while a typed architectural commit/effect owner remains required before retirement integration or additional compressed-form admission |
| A10 | Release-toolchain evidence | `/root` (compiler/bootstrap recovery); final reviewer `/root` | blocked: repair the Stage-3 memory lifecycle, produce an admitted self-hosted runtime, execute writer deliberate reds and critical CLI/GHDL scenarios, then retain deterministic receipt hashes |
| A11 | Shared scalar semantic database | `/root` | first I/M/RV64-word/shift declarative schema, RV32/RV64 specialization, and concrete I/IM multiply/divide provider selection exist; complete scalar table, HWIR resource binding, generated decoder/toolchain metadata remain pending |
| A12 | Typed HWIR aspect packs | `/root` | hash-pinned manifest/application plan, typed exact-set lock contract, first fail-closed observational output graph weave, and Gen2 VHDL manifest lock provenance exist; lockfile discovery, proof execution, and all timing/state/provider advice remain pending |
| A13 | Typed VHDL sequential HWIR migration and evidence | `/root` | standalone/retirement plus parcel/trap emission now use the canonical sequential renderer/hash boundary; executable qualification and independent RTL receipt remain open |
| A14 | Qualification producer/composer alignment | `/root` (compiler evidence); final reviewer `/root` | v2 source and shell validator reds implemented; admitted composer execution, writer copy/publication reds, and a retained receipt remain open behind Stage-3 recovery |

## Restart-12 execution plan (2026-08-14)

All lanes share the frozen interfaces
`owned_file_list_sha256`, `owned_file_manifest_path`, and
`owned_file_manifest_sha256`. The owned-source ledger format is exactly
`64-lowercase-hex`, two spaces, repo-relative `.spl` path, newline. Agents do
not rename these fields, broaden their file ownership, write the shared
bootstrap cache, commit, rebase, or push. `/root` is the only merge/cache/SCM
owner.

| Order | Lane / exact owner | Current status | Retained evidence | Exact resume / stop condition |
| --- | --- | --- | --- | --- |
| 1 | B1 Stage-3 recovery / `/root` | **STOP/WARN**: durable HIR sink is source-green; the Python design and first C sampler/analyzer design were both rejected and reverted at their three-cycle caps; no current candidate | Prior Stage-3 logs, the current-source RSS bug, and admitted local output `build/restart12-stage3-admitted` (Stage2/admitted SHA `2ec71042dd69cf0001fc3f61640c28038a450048f34e416103988b1627431950`) | Do not start Stage 3 yet. In a fresh scoped session jointly freeze and implement the non-Python producer/analyzer schemas, distinct descriptor identities, identity-safe bounded zero-survivor cleanup (including adopted and `setsid` descendants), strict completion/correlation, atomic `simple-stage3-memory-evidence-v1`, and deliberate reds recorded in the bug; provenance v3 remains unchanged. After independent review passes, run `scripts/bootstrap/bootstrap-from-scratch.sh --resume-stage3-from-admitted=build/restart12-stage3-admitted --jobs=1` once. |
| 1 | B2 owned evidence / `inventory_arch`; merge owner `/root` | **source PASS** | Exact reviewed A13/A14 list, canonical ledger, initial/pre-compose no-follow validation, Linux/GNU contract; one-shot shell and diff checks accepted | No resume. Reopen only if an owned source or frozen ledger/schema field changes. |
| 1 | B3 receipt authority / `stage3_admission`; merge owner `/root` | **source PASS / executable WARN** | Composer exact-key parsing, ledger/path-list retention, source revalidation, destination rehash; deterministic LD_PRELOAD writer-red interposer and host-native write/rename/pass-through fixture PASS; runner now passes its exact private manifest directly to the writer-red harness after revalidation, validates a uniquely retained aggregate red receipt binding CLI/provenance/manifest plus every red command/log/hit, revalidates again, then permits exactly one positive composer; independent highest review | After B1/B1.1 produce admitted Stage 3/4, run the qualification once. That one runner execution owns both writer copy/publication reds and the focused positive composer; do not discover a manifest manually or invoke either separately. Keep the broad executable checkbox open until retained admitted evidence exists. |
| 1 | B1.1 Stage-4 full CLI and admission / `/root`; final reviewer `/root` | **blocked/open** behind B1 | No Stage-4 candidate or adjacent provenance | From the repo root, run `scripts/bootstrap/bootstrap-from-scratch.sh --output=OUTPUT --mode=dynload --full-cli --jobs=1`, with the same repo-relative `OUTPUT`. The canonical wrapper builds and internally admits `OUTPUT/full/<triple>/simple` and writes adjacent `simple.provenance.env`. Then run the one-shot post-bootstrap command from `doc/06_spec/03_system/check/post_bootstrap_stage4_acceptance_spec.md` with absolute canonical in-workspace candidate/provenance paths. Do not infer Stage 4 from Stage-3 admission. |
| 1 | B4 shell deliberate reds / `ast_contract`; merge owner `/root` | **source PASS** | Executable shell reds cover malformed ledger rows, missing/empty/symlink/mutated sources, parent-symlink escape, and outside-target preservation | No resume for the shell boundary. Writer copy/publication/cleanup reds remain B3/A14 work and cannot be inferred from this PASS. |
| 2 | B5 A13 executable / `/root`; final reviewer `/root` | **blocked/open** behind B1 | Source/static checks only; no admitted self-hosted execution | Set `STAGE4` to the absolute admitted Stage-4 CLI and use `"$STAGE4"`, never `bin/simple`, for the compiler/lib/MCP/LSP, lint, duplication, and maintenance commands recorded in the SPipe state exactly once. B6 owns the single coverage-bearing execution of the mixed-sequential, predecode/provenance, system, and receipt specs; B5 must not rerun that focused suite. |
| 2 | B6 RTL qualification / `/root`; final reviewer `/root` | **blocked/open** behind B1-B4 and B1.1 | Qualification source contract only; no claim-bearing receipt | Prerequisites: absolute canonical in-workspace executable admitted Stage-4 CLI, its adjacent absolute canonical in-workspace admitted provenance file, Linux with GHDL and GNU `timeout`/`sha256sum`, and a fresh absent direct child of `build/evidence/riscv_gen2_hwir_foundation`. Run once: `scripts/check/run-riscv-gen2-hwir-qualification.shs --stage4-cli /mnt/data/worktrees/restart12-vhdl/OUTPUT/full/TRIPLE/simple --stage4-provenance /mnt/data/worktrees/restart12-vhdl/OUTPUT/full/TRIPLE/simple.provenance.env --output-dir /mnt/data/worktrees/restart12-vhdl/build/evidence/riscv_gen2_hwir_foundation/RESTART12_RUN_ID`. Required output: immutable v2 `qualification_receipt.json` written last plus bound RV32/RV64 VHDL, manifests, testbenches, isolated GHDL commands/logs/exits, and measured >=8000-bp coverage. Any red retains staging diagnostics and no receipt claim. |
| 3 | B7 knowledge reconciliation / `/root`; highest-capability reviewer `/root/plan_truth_audit` | **reviewed/source WARN** | Canonical plan/state audit plus corrected historical and resume wording | Reopen after B5/B6 evidence lands; reconcile every unchecked executable item before any PASS claim. |
| 4 | B8 integration / `/root`; final reviewer `/root` | **PASS after final locked transaction** | The accepted memory sink/writer handoff and both rejected sampler/analyzer boundaries are committed in the final detached HEAD; its reachable hash and WARN status are recorded in `/tmp/restart12-vhdl.done` | No resume. The final transaction uses the required lock, fetch/rebase/push/refetch/reachability proof, never forces, and never creates a branch. |

Dependency graph: B1 gates B5/B6. B2+B3+B4 gate B6. B5+B6 gate any
executable acceptance checkmark. B7 gates commit. B8 is last and cannot convert
a WARN evidence state into PASS.

## Current replacement-lane acceptance (2026-08-14)

- [x] The canonical sequential module owns typed signals, constants, bit-vector
  constants, combinational operations, comparisons, selects, extracts, and
  fixed slices; it does not accept raw VHDL fragments.
- [x] Validation fails closed for unsupported operations, unreadable operands,
  width drift, duplicate names, and multiple datapath drivers before emission.
- [x] Strict VHDL renders the validated combinational datapath before guarded
  state/output logic and commits every datapath field into the structural hash.
- [x] The mixed sequential executable spec and generated/manual mirror agree and
  cover add, truncate, sign extension, comparison, selection, unsigned
  predicate lowering, LSU geometry, rejection paths, and graph-hash drift.
- [ ] Focused checks, compiler/core regression checks, artifact/runtime guards,
  and SPipe layout/quality gates pass once on the final implementation.
- [ ] An admitted self-hosted CLI runs the focused mixed sequential spec plus
  compiler/lib/MCP/LSP checks without ABI-probe failure, signal, or seed
  substitution.
- [ ] Generated VHDL is analyzed, elaborated, and behaviorally simulated with
  GHDL for datapath-before-state capture, reset, guard-false, and guard-true
  cycles; source-text assertions alone do not close this item.
- [x] Parcel/trap stateful products migrate from the plan-only private renderer
  to the canonical `HwSequentialModuleDef` boundary, or an accepted design
  explicitly proves why they remain a separate typed owner without duplicated
  sequential semantics.
- [x] A14's canonical contract is frozen: the wrapper produces staged evidence,
  the admitted Simple app composes a fresh immutable run, and only the composer
  writes `qualification_receipt.json` last.
- [x] The runner removes the unsupported producer/composer switches and emits
  an exact-key v2 manifest that hash-binds coverage command/report/changed
  files/exclusions plus each row's testbench and GHDL commands/logs/exits.
- [ ] Deliberate-red runner/composer tests prove phase ordering, immutable-path
  and symlink rejection, malformed/duplicate keys, low coverage, every command
  failure, artifact mutation, composer failure, and partial-receipt cleanup.
  The deterministic writer copy/publication failpoint and host-native fixture
  are source-green, but the runner does not yet invoke the harness or publish a
  unique staging-manifest path; admitted execution and the broader matrix stay
  open.
- [x] Source coverage instrumentation supplies a complete static/zero-count decision
  inventory for every changed branch-bearing `.spl` file; executed-probe rows
  alone cannot establish the denominator or the 80% claim.
  The accepted source uses constructor-defined tag-dispatched traversal,
  preserves parser/desugar spans, bounds and deduplicates rows, and aligns
  runtime/manifest keys. Highest-capability static review is green.
  User-authorized Stage-3 diagnostic on 2026-08-14 used
  `bootstrap/stage3/simple` (SHA-256
  `905ce03696a4726e41e410e0531d39f84df2d26d1588e2a23206ede3c177793b`):
  `native-build test/01_unit/compiler/frontend/flat_ast_child_ownership_spec.spl
  -o /tmp/restart12-flat-ast-ownership-stage3` exited 139 before diagnostics.
  The binary is byte-identical to tracked Stage 1/2 and has no provenance
  receipt, so this is a retained diagnostic blocker, not qualification.
  Its separate advertised SMF compile route also exited 139 once; neither
  failing command is repeated.
- [ ] An admitted compiler executes the focused ownership/inventory spec and
  native coverage flow, proving exactly one compiler marker, zero-count rows
  joined with runtime outcomes, and the measured >=8000-bp threshold.
  `flat_ast_child_ownership_spec.spl` is a unit-level compiler contract with no
  operator scenario, so a generated scenario manual is N/A; its behavior and
  resume command are documented in the architecture, guide, and blocker.
- [ ] Changed `.spl` files pass lint, HWIR token duplication, and the seven-part
  `sspec-maintain scan`; the qualification receipt records at least 80% branch
  coverage or leaves the coverage contract blocked.
- [ ] Existing selected requirements, architecture, detail design, system-test
  plan, SPipe state, guide, feature/layer expert knowledge, executable steps,
  and manual evidence describe the same bounded A13/A14 boundary. Recheck this
  after exact A14 command, inventory, and receipt-authority sources land; no new
  requirement option may be auto-selected.
- [x] All intentional changes are committed, rebased under the integration
  lock, pushed without force, reachable from `origin/main`, and leave a clean
  detached worktree.

Current blockers: qualification authority is still unavailable while the
deployed runtime identifies as a bootstrap seed; therefore this lane may earn
source-level and focused target evidence but must not claim the independent
self-hosted qualification receipt or full RTL equivalence.
The canonical wrapper currently fails its bounded test-ABI probe, while direct
use of the deployed self-hosted executable exits by signal 11 during both the
focused test and `check`; this blocks executable acceptance evidence without
authorizing a Rust-seed fallback.
The exact resume commands and owner are recorded in
`.spipe/riscv_gen2_hwir_foundation/state.md`; the tracked runtime blocker is
`doc/08_tracking/bug/riscv_gen2_sequential_hwir_selfhost_runtime_blocker_2026-08-14.md`.
The first current-source pure-Simple Stage-3 rebuild reached all 616 parsed
sources and failed closed in HIR lowering because verification-contract MIR
consumers had no canonical HIR contract model.  The typed model restoration is
tracked in
`doc/08_tracking/bug/stage3_hir_contract_model_partial_integration_2026-08-14.md`.
Its first retry cleared that diagnostic but was observed externally terminated;
the retained log proves only that no compiler diagnostic or candidate was
emitted, not its exit code or peak RSS.
At that historical cycle-2 frontier, one final non-contended retry remained
under the three-cycle cap. That retry was subsequently consumed and retained
signal 15, 12m52s, and 24,839,624 KiB max RSS
through GNU time, but not a reliable wrapper exit status; it emitted no
compiler diagnostic or candidate. The B1
three-cycle cap is exhausted. Resume only through the memory-lifecycle blocker
`doc/08_tracking/bug/stage3_current_source_hir_rss_termination_2026-08-14.md`;
B5/B6 remain unavailable and unchecked.
The qualification-contract mismatch is tracked separately in
`doc/08_tracking/bug/riscv_gen2_hwir_qualification_contract_mismatch_2026-08-14.md`;
its original producer/schema mismatch is superseded by v2 source alignment,
while executable writer reds and a retained receipt keep the record open.
The accepted A14 contract removes the fictitious composer producer modes,
keeps the final run directory absent during staging, and advances the receipt
to v2 so coverage command/files/exclusions plus each testbench and GHDL command
  are hash-bound. The source contract is implemented, but accepting it without
  executable deliberate-red coverage would be a shortcut, so A14 remains open.

2026-08-14 coverage-inventory review: the compiler now emits the canonical
zero-count decision manifest after complete parsing and aligns existing runtime
probe keys without adding runtime symbols. A14 remains open until an admitted
self-hosted end-to-end test proves never-executed decisions remain in the
denominator. Rust-seed-only
coverage is explicitly not qualification evidence. Resume after restoring the
admitted Stage-4 CLI with the A14 qualification command recorded in the tracked
runtime blocker; retain the resulting v2 receipt and GHDL artifacts.
The broad `base..HEAD` scope is now replaced by an exact reviewed source set,
with an independently hashed per-source ledger, parent-symlink rejection, and
pre-compose revalidation. Exact command grammar, duplicate-safe product JSON,
and destination rehash are implemented at source level. Resume still requires
an admitted execution of the Simple composer and its missing writer-level
copy/publication/cleanup deliberate reds; shell validator reds alone cannot
close that item.
This is an implementation handoff. It does not mark A10, independent RTL
equivalence, or the Gen2 umbrella complete.

Parallel completion review (2026-08-14): `hwir_code_audit` reviewed typed
ownership and found/fixed the signal-destination and unary resize validation
holes; `hwir_docs_spipe` identified stale SPipe/requirements/guide/wiki
artifacts; `hwir_high_review` accepted the corrected source/static
implementation handoff after adversarial port-direction, route-label, and
cross-namespace collision coverage. Merge owner and final acceptance owner:
`/root`.

The C.J/C.BEQZ/C.BNEZ control rows now have aggregate strict-MIR contracts and
explicit row-level target evidence. Their typed redirect fields and operand
dependency are proven; this remains narrower than complete Zca or release
closure.

The frozen branch prerequisite is `HwBranchPredecodeInterface`: it composes
the predecode ports with the concrete `rs1_index: Bits[5]`/
`rs1_value: Bits[XLEN]` architectural read pair. The branch-row implementation
owner must prove the decoded prime register matches that index before consuming
the value in a typed graph, and must not add a decoder-side register-file/
provider lookup or runtime XLEN dispatch.

The first C.BEQZ/C.BNEZ graph constructors and exact four-input real-MIR
intrinsic contracts now exist and are unit-validated for typed RV32/RV64
interfaces. Generated-VHDL target vectors cover taken/not-taken, `+2`, `-2`,
sign-sensitive `-256`, cross-row behavior, and a mismatched read-index
fail-closed case, so each row now has an explicit target-proof allowlist entry.

The v2 owned integration boundary is `HwTrapParcelFrontendDef`. It carries the
branch-predecode lineage plus an explicit C.EBREAK trap effect through one
capture/dispatch/retirement owner. `trap_valid` is gated by active dispatch and
cause/tval are zero outside that transaction. It is explicitly not a legacy-core
wrapper. A composed exhaustive oracle and a deployed self-hosted CLI are still
required before `target_rtl_equivalence_verified` can become true.

Dependency order: A0 → A8/A9; A4 + A8 → A10; A9 precedes all effectful or
XLEN-specific compressed forms. A5 must not widen the capability manifest until
A8 and A10 produce current evidence. Merge owner and final reviewer: `/root`.

Shared names: `CoreConfig`, `HwNodeId`, `HwOrigin`, `HwirStrictLowerInput`,
`HwirStrictLowerResult`, `HwirStrictVhdlResult`, `CompressedHardwareExpansion`,
`CompressedExpansion`, `RiscvIsaEntry`, `CompressedCriticalSubsetManifest`.
Any temporary test helper must fail explicitly, never no-op.
