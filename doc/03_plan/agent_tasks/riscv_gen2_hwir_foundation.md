# RISC-V Gen2 HWIR Foundation — Parallel Plan

| Lane | Scope | Owner | Status |
| --- | --- | --- | --- |
| A0 | Freeze schema/result/config contracts and merge | `/root` | active; v1 stays frozen, v2 trap/retirement contract is versioned |
| A1 | HWIR source/test inventory | `gen2_code_tests` | review complete/pending merge |
| A2 | Requirements/design/test artifact inventory | `gen2_artifacts` | complete |
| A3 | Worktree ownership audit | `worktree_ownership` | complete |
| A4 | Typed config, strict lowering/emitter, critical driver route and real-MIR Bool extraction | `/root` | v2 source-less trap product implemented; self-hosted CLI evidence blocked by absent deployed runtime |
| A5 | Shared compressed seed and RV32/RV64 adapter splice | `/root` | 25-row common-integer subset has explicit row evidence; full C/Zc remains pending |
| A6 | Hardware-safe compressed adapter review | `compressed_adapter_review` | complete |
| A7 | Declarative ISA capability seed / critical manifest linkage | `/root` | compressed subset truth remains non-advertising/non-release-claimable; scalar I/M/RV64-word schema seed exists, but provider/decoder/toolchain consumers remain pending |
| A8 | Composed-front-end equivalence | `/root` | typed migrating and trap one-entry compositions plus RV32/RV64 GHDL protocol scenarios are implemented; a prepared strict-HWIR host oracle exhausts all 65,536 parcels for each target-trap product, while independent RTL equivalence and the self-hosted receipt remain pending |
| A9 | Stateful HWIR and architectural effects | `/root` | bounded single-outstanding capture/dispatch/retire/effect plan is implemented; a verification-only reset-coupled loopback checks one-entry receipt transport, while a typed architectural commit/effect owner remains required before retirement integration or additional compressed-form admission |
| A10 | Release-toolchain evidence | compiler/bootstrap owner; final reviewer `/root` | blocked: deploy an admitted self-hosted runtime, align the qualification producer/composer contract, rerun critical CLI/GHDL product scenarios, then record deterministic manifest hashes |
| A11 | Shared scalar semantic database | `/root` | first I/M/RV64-word/shift declarative schema, RV32/RV64 specialization, and concrete I/IM multiply/divide provider selection exist; complete scalar table, HWIR resource binding, generated decoder/toolchain metadata remain pending |
| A12 | Typed HWIR aspect packs | `/root` | hash-pinned manifest/application plan, typed exact-set lock contract, first fail-closed observational output graph weave, and Gen2 VHDL manifest lock provenance exist; lockfile discovery, proof execution, and all timing/state/provider advice remain pending |
| A13 | Typed VHDL sequential HWIR migration and evidence | `/root` | standalone/retirement plus parcel/trap emission now use the canonical sequential renderer/hash boundary; executable qualification and independent RTL receipt remain open |
| A14 | Qualification producer/composer alignment | compiler evidence owner; final reviewer `/root` | v2 runner/composer source implemented; executable positive/deliberate-red acceptance and a retained admitted receipt remain blocked by the self-hosted runtime |

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
- [ ] Coverage instrumentation supplies a complete static/zero-count decision
  inventory for every changed branch-bearing `.spl` file; executed-probe rows
  alone cannot establish the denominator or the 80% claim.
- [ ] Changed `.spl` files pass lint, HWIR token duplication, and the seven-part
  `sspec-maintain scan`; the qualification receipt records at least 80% branch
  coverage or leaves the coverage contract blocked.
- [x] Existing selected requirements, architecture, detail design, system-test
  plan, SPipe state, guide, feature/layer expert knowledge, executable steps,
  and manual evidence describe the same bounded A13 boundary. No new
  requirement option was auto-selected.
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
The qualification-contract mismatch is tracked separately in
`doc/08_tracking/bug/riscv_gen2_hwir_qualification_contract_mismatch_2026-08-14.md`;
runtime deployment alone cannot make the current wrapper runnable.
The accepted A14 contract removes the fictitious composer producer modes,
keeps the final run directory absent during staging, and advances the receipt
to v2 so coverage command/files/exclusions plus each testbench and GHDL command
  are hash-bound. The source contract is implemented, but accepting it without
  executable deliberate-red coverage would be a shortcut, so A14 remains open.
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
