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
| A10 | Release-toolchain evidence | unassigned | deploy the self-hosted runtime, rerun critical CLI/GHDL product scenarios, then record deterministic manifest hashes |
| A11 | Shared scalar semantic database | `/root` | first I/M/RV64-word/shift declarative schema, RV32/RV64 specialization, and concrete I/IM multiply/divide provider selection exist; complete scalar table, HWIR resource binding, generated decoder/toolchain metadata remain pending |
| A12 | Typed HWIR aspect packs | `/root` | hash-pinned manifest/application plan, typed exact-set lock contract, first fail-closed observational output graph weave, and Gen2 VHDL manifest lock provenance exist; lockfile discovery, proof execution, and all timing/state/provider advice remain pending |
| A13 | Typed VHDL sequential HWIR migration and evidence | `/root` | active replacement lane: extend `HwSequentialModuleDef` with typed combinational datapath ownership, validate readable values/single drivers/widths, serialize the datapath before state, restore the executable mixed-datapath spec/manual pairing, and retain structural-hash evidence; qualification remains blocked on the admitted self-hosted CLI and independent RTL receipt |

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
- [ ] All intentional changes are committed, rebased under the integration
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
