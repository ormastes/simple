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
| A9 | Stateful HWIR and architectural effects | `/root` | bounded single-outstanding capture/dispatch/retire/effect plan is implemented; general channels/effects remain required before C.JAL, RV64 C.ADDIW, memory-width, Zcb or Zcmp admission |
| A10 | Release-toolchain evidence | unassigned | deploy the self-hosted runtime, rerun critical CLI/GHDL product scenarios, then record deterministic manifest hashes |
| A11 | Shared scalar semantic database | `/root` | first I/M/RV64-word/shift declarative schema, RV32/RV64 specialization, and concrete I/IM multiply/divide provider selection exist; complete scalar table, HWIR resource binding, generated decoder/toolchain metadata remain pending |
| A12 | Typed HWIR aspect packs | `/root` | hash-pinned manifest/application plan, typed exact-set lock contract, first fail-closed observational output graph weave, and Gen2 VHDL manifest lock provenance exist; lockfile discovery, proof execution, and all timing/state/provider advice remain pending |

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
