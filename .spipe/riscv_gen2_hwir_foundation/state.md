# Feature: riscv_gen2_hwir_foundation

## Raw Request

`$sp_dev impl the simple riscv ehnancement make up pherallel plan and go.`

## Task Type

feature

## Refined Goal

Deliver the first development-stage, ownership-safe Simple RISC-V Gen2
foundation by turning the existing HWIR scaffold into a typed, fail-closed
compiler slice with a concrete RISC-V configuration contract, while preserving
the planned aspect, compressed-front-end, PPA, MMU, debug, and advanced-core
waves. It becomes verified only after the self-hosted qualification receipts
named in this state file are recorded.

## Acceptance Criteria

- AC-1: The Gen2 scope, current-state boundary, staged delivery order, and
  parallel ownership plan are recorded in a durable plan and identify the
  merge owner and final reviewer.
- AC-2: The selected first HWIR slice has concrete typed inputs, validation,
  and deterministic lowering/emission behavior; unsupported/invalid input
  returns a diagnostic and never silently selects the legacy VHDL path.
- AC-3: A concrete `CoreConfig`/RISC-V specialization contract represents
  RV32/RV64 selection at elaboration time without a runtime XLEN selector, and
  focused tests prove valid RV32/RV64 choices and rejected invalid choices.
- AC-4: Focused executable tests cover the selected HWIR path's success,
  invalid-input, and no-fallback behavior with non-placeholder assertions;
  mirrored SPipe/manual evidence is added or explicitly shown N/A because the
  tested compiler contract is unit-level rather than scenario-oriented.
- AC-5: The self-hosted release gate requires modified `.spl` sources to pass
  focused test, lint, duplication, and modern-SSpec maintenance gates once
  each, including `SIMPLE_SAFETY_PROFILE=critical`; no modified source or test
  may contain a stub/no-op implementation. Bootstrap-seed activity is
  diagnostic only.
- AC-6: Knowledge artifacts are updated and mutually consistent: `doc/01_research/`,
  `doc/03_plan/`, `doc/04_architecture/`, and `doc/05_design/` for this slice;
  `doc/07_guide/` documents the operator-facing A14 runner and honest WARN
  boundary; `doc/00_llm_process/feature_expert/` and
  `doc/00_llm_process/layer_expert/` are updated or marked with the exact
  missing owner path; every found but unfixed gap receives a
  `doc/08_tracking/bug/` record with file:line and unblock condition.
- AC-7: The Gen2 umbrella remains open until subsequent scalar-core,
  compressed, PPA, privilege/MMU, debug/trace, and product-verification waves
  have their own implementation and evidence; this foundation is reported as
  an implementation increment, never as full RISC-V completion.
- AC-8: The strict helper route fails closed for invalid or unsupported input.
  The production VHDL driver snapshots typed assurance policy and, in critical
  mode, routes hardware-tagged Gen2 products through real MIR-to-HWIR lowering
  before direct VHDL emission; only the Bool-AND shape is supported today.

## Scope Exclusions

- Implementing the complete RV32/RV64 core, Zc family, Linux boot, Debug 1.0,
  E-Trace, PPA optimizer, or advanced issue-width/vector/OoO products in this
  increment.
- Direct edits to generated VHDL or files owned by another active lane.

## Cooperative Review

- Sidecars: `/root/gen2_artifacts` (artifact/acceptance audit),
  `/root/gen2_code_tests` (HWIR implementation/test inventory), and
  `/root/worktree_ownership` (active-lane ownership audit).
- Merge owner: `/root`.
- Final reviewer: `/root` after sidecar findings are reconciled.
- Shared interfaces to freeze for this increment: `HwNodeId`, `HwOrigin`,
  `HwModule`, `HwirLowerInput`, `CoreConfig`, `XlenConfig`, and the
  fail-closed emission result/diagnostic contract.
- Scenario helpers: `stateful_protocol_64_testbench` is the named RV32/RV64
  GHDL protocol helper; it is development-stage evidence until the self-hosted
  route records its receipt.
- Setup/checker helpers: focused HWIR test fixture and explicit no-fallback
  checker, named during design; any temporary helper fails with `fail(...)`
  rather than silently passing.
- Generated-manual review owner: N/A unless the chosen test path becomes
  scenario-oriented; the final reviewer confirms this decision from the test
  structure.

## Phase

implementation-handoff: source-level strict HWIR, stateful Gen2 product, and
bootstrap diagnostic tests are implemented. The plan remains active and is not
verified or release-ready until the self-hosted RV32/RV64 VHDL/GHDL, lint,
duplicate-check, and modern-SSpec maintenance gates recorded below complete.

## Log

- dev: Created initial feature state with 8 acceptance criteria (type:
  feature); user authorized parallel planning and implementation.
- impl: Added typed concrete HWIR/config/origin contracts, strict no-fallback
  lowering, strict typed VHDL emission, focused unit/system specs, and the
  mirrored manual/design artifacts.
- verify: Focused interpreter test and default/critical lint commands completed
  through `bin/simple`; the resolved binary identifies itself as a Rust
  bootstrap seed, so this is diagnostic evidence only. The required
  self-hosted duplicate-check and `sspec-maintain` commands are unavailable
  (`duplicate-check`/`sspec-maintain` are not commands in the deployed seed);
  tracked resume context:
  `doc/08_tracking/test/spec_missing_path_classification_2026-08-10.tsv`.
  Resume after a current self-hosted CLI deploy with:
  `bin/simple test test/01_unit/compiler/50.mir/hwir_foundation_spec.spl --mode=interpreter`,
  `bin/simple test test/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.spl --mode=interpreter`,
  `bin/simple duplicate-check src/compiler/50.mir/hwir --mode token --min-lines 5`,
  and `bin/simple sspec-maintain scan test/03_system/app/hardware/feature/riscv_gen2_hwir_foundation_spec.spl`.
- impl: Added real `MirFunction` Bool-AND extraction to strict HWIR. It is not
  yet selected by the production VHDL driver; critical routing remains a
  separately tested driver increment.
- verify: Added adversarial origin/direction/identifier tests and real-MIR
  extraction tests. Focused source check, focused unit specs, and critical lint
  completed through the bootstrap seed only; self-hosted evidence remains open.
- impl: Added typed-policy snapshot, explicit `riscv_gen2_target`, production
  critical route selection, fail-closed strict MIR module compilation, and
  strict route/node/config provenance in VHDL artifacts. `simple-vhdl` now
  accepts `--riscv-gen2-target rv32|rv64`; the broad compile facade remains a
  follow-up because its source-subset fast path is a distinct route.
- verify: Focused source check plus real-MIR HWIR and artifact-manifest specs
  completed through the bootstrap seed. A critical full-core driver probe was
  attempted but its seed output did not expose a usable result; do not treat it
  as route evidence.
- impl: Added a shared compressed Zca seed and spliced its common C.EBREAK,
  C.NOP/C.ADDI, and zero-reservation rows into both RV32C and RV64C adapters.
  Review found text diagnostics and XLEN selection unsafe in an `@hardware`
  caller; the final adapter contract is `CompressedHardwareExpansion` with
  fixed-width fields and numeric reason codes only. The host metadata wrapper
  retains diagnostics/XLEN classification outside emitted hardware.
- verify: Focused shared-seed, RV32 adapter, and RV64 adapter interpreter
  specs plus the source check completed through the bootstrap seed. Full Zca
  table parity, exhaustive 65,536 parcel classification, and target RTL/VHDL
  lowering evidence remain open Gen2 work.
- impl: Mission-critical compressed code now uses a separate fixed-width,
  no-config/no-text/no-legacy-fallback subset entrypoint. RV32/RV64 critical
  adapters preserve only its verified common rows and reject divergent or
  unimplemented rows; they are deliberately not wired into existing legacy
  product defaults.
- verify: Added a deterministic exhaustive 65,536-parcel classifier spec plus
  critical adapter rejection vectors. The bootstrap-seed run is diagnostic
  evidence only; target RTL/VHDL and full C/Zca certification remain open.
- impl: Added `CompressedCriticalSubsetManifest` as the capability-truth
  boundary. It deliberately forbids a full-Zca release/advertisement claim and
  records the remaining exhaustive-classification and target-RTL obligations.
- impl: Added the initial declarative `RiscvIsaEntry` table for 25 verified
  common-Zca rows and linked the critical-subset manifest's entry count to it.
  The table is host/elaboration metadata, not a runtime hardware provider.
- impl: Migrated the normal RV32 integer compressed adapter to the shared
  fixed-width RV32 specialization and deleted its duplicated local decoder and
  instruction-encoding helpers. The mission-critical entrypoint remains a
  separate fail-closed common-Zca subset; the normal RV32 path must not be
  advertised as target-RTL-verified or full C/Zca certification.
- verify: Focused RV32 adapter source checking and representative shared-row
  interpreter vectors completed through the bootstrap seed. Self-hosted and
  target RTL/VHDL evidence remain required before a critical product claim.
- impl: Migrated the normal RV64 integer compressed adapter to
  `riscv_zca_expand_rv64_hardware`. The shared fixed-width RV64 specialization
  owns LD/SD, ADDIW, six-bit shifts, SUBW/ADDW and LDSP/SDSP; it has no runtime
  XLEN or text diagnostic input. The obsolete local RV64 compressed decoder and
  format builders are deleted, leaving no alternate normal decoder route.
- verify: RV64 adapter source check, shared adapter vectors, compressed ISA
  unit specification, and ISA conformance probe completed through the bootstrap
  seed. Target HWIR/VHDL equivalence and full C/Zc certification remain open.
- impl: Replaced signed host-width compressed-immediate helper intermediates
  with fixed `u32` two's-complement values throughout the shared synthesizable
  decoder path. This keeps decode result assembly width-explicit before HWIR
  lowering.
- verify: The shared decoder source check, exhaustive critical-subset parcel
  classifier, and RV32/RV64 compressed adapter specs completed through the
  bootstrap seed after the fixed-width conversion.
- impl: The critical-subset manifest now distinguishes an already verified
  exhaustive 65,536-parcel classification from the still-false target-RTL
  equivalence evidence. Its release predicate checks both evidence states and
  remains permanently false for this non-advertising subset.
- verify: The full mission-critical compressed specification passed after the
  manifest truth-state change, including exhaustive deterministic parcel
  classification. The bootstrap seed result is diagnostic evidence only.
- impl: The VHDL tool facade now creates its fixed GHDL work directory before
  analysis, elaboration, simulation, or synthesis. The Gen2 system scenario
  writes strict RV32 HWIR output and requires successful GHDL VHDL-2008
  analysis rather than only string inspection.
- verify: Focused app-IO source check, Gen2 HWIR system specification with
  actual GHDL analysis, and the direct runtime-access guard completed through
  the bootstrap seed. This is target syntax evidence for the Bool-AND seed;
  compressed HWIR/VHDL lowering remains open.
- verify: An attempted direct critical `vhdl_compile_entry` CLI probe through
  the available bootstrap binaries exited without creating its requested VHDL
  or manifest artifact. It is explicitly not driver-route evidence. The
  release wrapper rejects its installed runtime as non-production and the
  underlying binary identifies as the same bootstrap seed; a current
  self-hosted runtime is required for the end-to-end critical route gate.
- impl: Extended the central declarative ISA table from the 25 common critical
  rows to all 33 implemented integer-Zca rows. Explicit RV32/RV64 elaboration
  views contain 26/32 rows respectively; this is host metadata only and does
  not add a runtime XLEN decoder input.
- verify: ISA-database source check and the shared compressed table/decoder
  unit specification completed through the bootstrap seed. The critical
  manifest remains bound to its 25-row common subset and cannot advertise full
  Zca.
- impl: Marked the normal RV64 compressed adapter entrypoint as `@hardware`,
  matching RV32 and making both shared adapter boundaries explicit candidates
  for typed HWIR lowering.
- verify: RV64 decoder source check and compressed decoder unit specification
  completed through the bootstrap seed after the metadata change.
- impl: Extended `CoreConfig` with validated ISA and compressed-decode profiles
  plus concrete RV32/RV64 integer-Zca and common-critical constructors. This
  records provider/capability selection at elaboration rather than in RTL.
- verify: Strict-HWIR source check and foundation configuration specification
  completed through the bootstrap seed. The current strict VHDL lowering still
  supports only the Bool-AND seed and therefore cannot claim compressed RTL.
- impl: Extended real-MIR strict HWIR lowering from only Bool BitAnd to matching
  Bool or `u32` BitAnd. The width derives from the typed MIR signature rather
  than `CoreConfig.xlen`, enabling an RV64 product to preserve a 32-bit parcel
  datapath.
- verify: Strict lowerer/emitter source check and real-MIR extraction
  specification completed through the bootstrap seed, including a 32-bit VHDL
  emission assertion under RV64 configuration.
- impl: Added strict fixed-width BitOr lowering and VHDL emission alongside
  BitAnd. This supplies the mask-and-merge primitive needed by compressed
  instruction assembly without widening the accepted MIR control-flow shape.
- verify: Strict HWIR source check and real-MIR BitAnd/BitOr extraction
  specification completed through the bootstrap seed.
- impl: Added typed HWIR constants and internal-signal slots, generalized
  combinational operands to declared values, and emitted numeric VHDL-2008
  constants through the strict emitter. This supports a typed 32-bit parcel
  mask graph without string-valued RTL operands.
- verify: Strict-HWIR source check, foundation unit specification, and Gen2
  system scenario completed through the bootstrap seed; GHDL successfully
  analyzed the generated parcel-mask VHDL. Full compressed MIR lowering is
  still not implemented.
- impl: Added real-MIR strict lowering for the typed `u32 -> u32` parcel-mask
  shape: one VHDL-safe `Const(Int)` followed by `BitAnd` and direct return.
  The result uses a typed HWIR constant and never falls back to legacy VHDL.
- verify: Strict lowerer/emitter source check and real-MIR extraction
  specification completed through the bootstrap seed for the parcel-mask
  graph. Broader constants, shifts, control, and structured decompressor
  output remain fail-closed.
- impl: Added real-MIR strict lowering and VHDL emission for a `u32` logical
  right shift with one typed constant amount constrained to 0..31. This models
  parcel-field extraction while rejecting variable/unsafe shift shapes.
- verify: Strict source/extraction checks and the Gen2 system scenario
  completed through the bootstrap seed; GHDL analyzed the generated typed
  parcel-shift VHDL successfully.
- impl: Added strict real-MIR lowering for the two-operation parcel field
  shape `(parcel >> constant) & constant`. HWIR now carries typed internal
  signals, validates a single combinational driver, and emits ordered
  combinational assignments.
- verify: Strict source/extraction checks and the Gen2 system scenario
  completed through the bootstrap seed; GHDL analyzed the generated two-stage
  parcel-field VHDL successfully. Decoder branches and full decompression
  remain fail-closed.
- impl: Hardened strict HWIR graph validation so every internal combinational
  signal and output has exactly one declared driver; duplicate and undriven
  values are rejected before VHDL emission.
- verify: Strict HWIR source check plus foundation and real-MIR extraction
  specifications completed through the bootstrap seed, including an adversarial
  multiple-driver graph.
- verify: The Gen2 HWIR system scenario now elaborates and simulates the
  generated two-stage parcel-field VHDL with GHDL. It checks
  `(0xA000 >> 13) & 7 == 5`; this is behavior evidence for the primitive, not
  full decompressor equivalence.
- impl: Added a no-input strict real-MIR `u32` constant-output shape and used
  it for the canonical C.EBREAK expansion leaf (`0x00100073`). It has no
  textual RTL literal or legacy fallback.
- verify: The Gen2 HWIR system scenario now elaborates and simulates the
  typed C.EBREAK leaf with GHDL. Parcel predicate/mux selection is explicitly
  not claimed until typed control operations are added.
- impl: Added typed HWIR equality and select operations. Validation requires a
  one-bit writable comparison result, a one-bit readable select condition,
  matching branch/result widths, and one driver for every internal/output
  value; the strict emitter lowers them to deterministic VHDL-2008.
- verify: Focused strict source check, foundation unit test, real-MIR
  extraction test, and system scenario completed through the bootstrap seed.
  GHDL analyzed and simulated a hand-constructed critical C.EBREAK decoder:
  `0x9002` maps to `0x00100073` and `0x0001` maps to zero. This is target
  behavior evidence for the typed graph only; real-MIR branch lowering and a
  current self-hosted critical driver run remain release-blocking work.
- impl: Added fail-closed real-MIR lowering for the audited frontend-style
  C.EBREAK conditional CFG: `Const(0x9002)`, Bool `Eq`, `If`, two
  Const/Copy arms, and a joined `Ret`. It lowers only this exact shape into the
  typed equality/select graph; it does not introduce generic CFG lowering.
- verify: The real-MIR extraction specification completed through the bootstrap
  seed. It asserts the generated typed compare/select values and mutates the
  miss edge, which receives a stable strict-CFG diagnostic with no legacy
  fallback. Target simulation remains covered by the equivalent typed HWIR
  graph until the current self-hosted driver can exercise the production route.
- impl: Extended critical `simple-vhdl` product selection with explicit
  `rv32-zca-critical` and `rv64-zca-critical` targets. The driver maps them to
  `CoreConfig` common-critical profiles during elaboration; the CLI validates
  the same closed target set.
- verify: Focused compile checks for compile-options, AOT VHDL driver, and CLI
  entry completed through the bootstrap seed. The direct environment-runtime
  guard passed. A self-hosted end-to-end critical compilation remains required
  before this route can be treated as release evidence.
- impl: Centralized the closed critical target mapping in `CoreConfig`; the
  driver resolves through it and the CLI validates through the same owner,
  preventing a target-admission drift between host entrypoints.
- verify: The HWIR foundation unit specification completed through the
  bootstrap seed for both positive common-critical target resolution and an
  unsupported-target rejection.
- impl: Refactored the exact C.EBREAK CFG lowerer into one terminal-match
  primitive and added an approved C.NOP leaf (`0x0001 → 0x00000013`). The
  dispatch is closed to those two literal triples and emits semantic predicate
  names without copying structural CFG validation.
- verify: Focused strict source and real-MIR extraction specifications
  completed through the bootstrap seed for both leaves and the existing
  malformed-branch mutation. Unknown terminal literals remain strict errors.
- impl: Gated strict terminal compressed lowering on the explicit
  `zca-common-critical` `CoreConfig` profile. Base RV32/RV64 and broader
  unproven integer-Zca configurations now reject before graph construction.
- verify: The real-MIR extraction specification completed through the bootstrap
  seed for the profile-gate rejection and confirmed no legacy fallback.
- impl: Added typed logical-left shift to HWIR validation, strict VHDL-2008
  emission, and the shared bounded real-MIR shift extractor. This is the
  field-placement primitive for canonical C.ADDI instruction assembly.
- verify: Focused strict source and real-MIR extraction specifications
  completed through the bootstrap seed for `Shl`, including the emitted
  `numeric_std.shift_left` expression.
- impl: Added a typed, hand-constructed common-Zca C.ADDI/C.NOP HWIR graph
  scenario using the critical RV32 configuration. It covers parcel masking,
  row classification, immediate sign extension, canonical field placement,
  and a zero-valued non-row result without a host text or XLEN selector.
- fix: Imported `std.spec.*` in the system scenario. The missing import—not a
  hardware or runner defect—caused the earlier `step` lookup failure.
- fix: The system scenario now uses the repository-standard tuple-return
  process façade rather than the capture-based `app.io.vhdl_ffi` wrapper,
  which misreports GHDL under the bootstrap interpreter.
- verify: The expanded system scenario passes through the current bootstrap
  launcher, including VHDL-2008 GHDL analysis, elaboration, and simulation of
  C.ADDI positive, negative-immediate, and non-row vectors. This remains
  diagnostic seed evidence until a current self-hosted rerun succeeds.
- verify: Extended the generated C.ADDI VHDL testbench to exhaust all 2,048
  Q1/funct3=000 C.ADDI/C.NOP encodings (32 `rd` values × 64 immediates). The
  bootstrap system scenario passes VHDL-2008 GHDL analysis, elaboration, and
  simulation. This closes target equivalence only for that row.
- impl: The capability manifest now reports two row-level target-equivalent
  entries (`zca.c.ebreak` and `zca.c.nop_addi`) separately from the still-false
  complete-subset target-equivalence flag.
- verify: The mission-critical compressed subset test passed after asserting
  the row-level target-evidence count alongside the exhaustive classifier.
- impl: Added a typed C.LI HWIR graph with an explicit `rs1=x0` canonical
  assembly and row predicate; it remains absent from non-row parcel outputs.
- verify: The generated VHDL exhaustively simulated all 2,048 C.LI encodings
  (32 `rd` values × 64 immediates) plus a non-row rejection case. The manifest
  now reports three target-proven table entries while full-subset equivalence
  stays false.
- impl: `HwModuleDef` now rejects any `zca.*` semantic origin unless the
  concrete `CoreConfig` selects `zca-common-critical`.
- verify: The HWIR foundation test passed its direct-construction mutation:
  a Zca origin under base RV32 receives a stable compressed-profile error
  before the VHDL serializer can run.
- impl: Moved the prevalidated C.LI typed graph definition into the compiler
  HWIR layer as `strict_zca_cli_row_hwir`, exported for a future exact-MIR
  extractor. It accepts only `zca-common-critical` and cannot select a legacy
  decoder or runtime XLEN provider.
- verify: The HWIR foundation test passed construction, validation, strict
  VHDL rendering, and base-profile rejection for the compiler-owned C.LI row.
- impl: Added strict real-MIR extraction for the compiler-reserved
  `__simple_riscv_zca_cli_row_v1` semantic intrinsic. It invokes the
  compiler-owned C.LI graph only after exact signature, local, operand,
  return, and one-block CFG validation.
- verify: The real-MIR extractor specification passed valid C.LI intrinsic
  lowering plus an empty-argument mutation rejection with no legacy fallback.
- impl: Added the compiler-owned C.ADDI/C.NOP typed-row constructor and the
  reserved `__simple_riscv_zca_caddi_row_v1` real-MIR semantic boundary. It
  selects only the concrete common-critical graph after exact signature, local,
  operand, direct-return, and one-block CFG validation.
- verify: The real-MIR extractor specification passed C.ADDI/C.NOP lowering
  and a non-semantic-return mutation rejection with no legacy fallback. This
  reuses row-level VHDL evidence already recorded for the typed C.ADDI graph;
  it is not whole-Zca or self-hosted release evidence.
- verify: Replaced the C.ADDI target scenario's hand-built graph with the
  compiler-owned row constructor, then re-ran its 2,048 parcel VHDL-2008 GHDL
  simulation through the bootstrap seed. The target evidence now exercises the
  strict-MIR-selected implementation; self-hosted execution remains required.
- verify: Replaced the C.LI target scenario's hand-built graph with its
  compiler-owned row constructor and re-ran the 2,048 parcel VHDL-2008 GHDL
  simulation through the bootstrap seed. The two migrated semantic rows now have
  constructor-to-target evidence; whole-Zca and self-hosted evidence remain
  open.
- impl: Added `strict_zca_cebreak_row_hwir` and changed the validated
  frontend-style C.EBREAK CFG extractor to select it. The generic terminal
  checker remains responsible for C.NOP, so no unapproved terminal literal can
  select a semantic row constructor.
- verify: Replaced the C.EBREAK target scenario's hand-built equality/select
  graph with the compiler-owned constructor. Focused real-MIR extraction and
  VHDL-2008 GHDL scenario checks completed through the bootstrap seed.
- impl: Changed the validated C.NOP terminal CFG route to select the shared
  `strict_zca_caddi_row_hwir` graph. C.NOP remains a distinct source-shape
  validation case but cannot create an alternate semantic circuit.
- verify: The focused real-MIR extractor specification passed the shared-row
  C.NOP assertions through the bootstrap seed; exhaustive C.ADDI/C.NOP target
  evidence continues to cover parcel `0x0001`.
- verify: Added and completed an end-to-end VHDL CLI route scenario: a real
  `@hardware` Boolean AND with critical policy and explicit RV32 target emits
  strict HWIR VHDL and a `.gen.json` manifest reporting `hwir-strict` and the
  concrete `rv32` configuration. This is bootstrap-seed route evidence only.
- verify: The same CLI route suite passes unsupported Boolean XOR under
  critical policy and asserts nonzero exit with neither VHDL nor `.gen.json`
  sidecar. This is direct evidence that the critical driver cannot emit legacy
  artifacts after strict HWIR rejection.
- impl: Added the compiler-owned `strict_zca_addi4spn_row_hwir` graph. It
  reconstructs the unsigned scrambled immediate, maps rd' to x8..x15, uses x2
  as rs1, and gates the reserved zero-immediate encoding before output.
- verify: The target scenario exhaustively simulated all 2,048 Q0/funct3=000
  parcels through GHDL, including zero-immediate rejection. The capability
  manifest now records four row-level target-proven entries; full-subset
  equivalence remains false.
- impl: Added the reserved `__simple_riscv_zca_addi4spn_row_v1` real-MIR
  semantic boundary. It validates the same one-input/direct-return shape as
  the other declarative rows and selects the constructor for concrete RV32 or
  RV64 critical configurations without runtime XLEN dispatch.
- verify: The real-MIR extraction specification completed C.ADDI4SPN lowering
  under RV64 with no legacy fallback; the target row proof remains the shared
  32-bit parcel graph evidence.
- impl: Added the compiler-owned C.LW graph and reserved
  `__simple_riscv_zca_lw_row_v1` strict real-MIR boundary. It reconstructs
  prime-register fields and the unsigned load offset without XLEN dispatch.
- verify: Foundation and real-MIR extractor specifications completed profile
  rejection and successful C.LW lowering. The generated VHDL then exhaustively
  simulated all 2,048 Q0/funct3=010 parcels plus non-row rejection through
  GHDL. The manifest records five row-level target-proven entries; full-subset
  equivalence and release advertisement remain false.
- impl: Added the compiler-owned C.SW graph and reserved
  `__simple_riscv_zca_sw_row_v1` strict real-MIR boundary. It preserves a
  concrete 32-bit parcel interface and reconstructs the canonical S-format
  split immediate with no runtime XLEN/provider dispatch.
- verify: Foundation, extractor, and generated VHDL evidence completed C.SW
  profile-gating plus all 2,048 Q0/funct3=110 parcel cases and non-row
  rejection. The manifest records six row-level target-proven entries; its
  full-subset equivalence and release advertisement flags remain false.
- impl: Added the compiler-owned C.LWSP graph and reserved
  `__simple_riscv_zca_lwsp_row_v1` strict real-MIR boundary. The typed graph
  reconstructs the stack-relative unsigned immediate and explicitly rejects
  the reserved `rd=x0` encoding without a legacy fallback.
- verify: Foundation, extractor, and generated VHDL evidence completed C.LWSP
  profile gating, all 4,096 Q2/funct3=010 parcels, reserved-register rejection,
  and a non-row case. The manifest records seven target-proven entries; full
  subset equivalence and release advertisement remain false.
- impl: Added the compiler-owned C.SWSP graph and reserved
  `__simple_riscv_zca_swsp_row_v1` strict real-MIR boundary. Focused HWIR
  construction/extraction checks pass; its capability count remains unchanged
  pending a separate exhaustive generated-VHDL row proof.
- verify: Generated VHDL exhaustively simulated all 2,048 C.SWSP row parcels
  and a non-row rejection. The manifest now records eight target-proven rows;
  full-subset equivalence and release advertisement remain false.
- verify: C.SLLI(low) exhaustive VHDL evidence covers all 1,024 five-bit
  shifts and rejects bit12-set high-shamt parcels. The manifest records nine
  target-proven rows; full-subset equivalence and release advertisement remain false.
- impl/verify: C.SRLI(low) now has an origin-tracked, profile-gated typed HWIR
  graph and real-MIR semantic-intrinsic route. Exhaustive VHDL evidence covers
  all 256 Q1/mode-00 five-bit shifts, rejects adjacent C.SRAI and bit12-set
  forms, and promotes the manifest to ten target-proven rows. Full-subset
  equivalence and release advertisement remain false.
- impl/verify: C.SRAI(low) now has a separate origin-tracked, profile-gated
  typed HWIR graph and real-MIR semantic-intrinsic route. Exhaustive VHDL
  evidence covers all 256 Q1/mode-01 five-bit shifts, rejects C.SRLI and
  bit12-set forms, and promotes the manifest to eleven target-proven rows.
  Full-subset equivalence and release advertisement remain false.
- fix/verify: The SRLI/SRAI classifier mask was corrected from `0xEC03` to
  `0xFC03`; the former did not constrain parcel bit12 despite the documented
  low-shamt contract. Unit tests assert the mask and target simulation now
  checks the actual adjacent and bit12-set parcels. No release claim was made
  while this defect existed.
- impl/verify: C.ANDI now has an origin-tracked, profile-gated typed HWIR graph
  and real-MIR semantic-intrinsic route. Exhaustive VHDL evidence covers all
  512 compact-register/signed-immediate parcels, validates negative sign
  extension, rejects adjacent modes, and promotes the manifest to twelve
  target-proven rows. Full-subset equivalence and release advertisement remain false.
- impl/verify: C.SUB now has an origin-tracked, profile-gated typed HWIR graph
  and real-MIR semantic-intrinsic route. Exhaustive VHDL evidence covers all
  64 compact-register pairs, rejects adjacent C.XOR and RV64-only C.SUBW forms,
  and promotes the manifest to thirteen target-proven rows. Full-subset
  equivalence and release advertisement remain false.
- refactor/impl/verify: C.SUB and C.XOR now bind a closed compiler-host
  compact-R elaborator rather than copied graph construction. C.XOR has its own
  origin-tracked, profile-gated real-MIR route and exhaustive 64-pair VHDL
  evidence; the manifest records fourteen target-proven rows. Full-subset
  equivalence and release advertisement remain false.
- impl/verify: C.OR now binds the same closed compact-R elaborator with an
  origin-tracked, profile-gated real-MIR route. Exhaustive VHDL evidence covers
  all 64 compact register pairs and rejects C.XOR/C.AND/high-bit forms; the
  manifest records fifteen target-proven rows. Full-subset equivalence and
  release advertisement remain false.
- impl/verify: C.AND completes the bit12=0 compact-R subset through the same
  closed elaborator, with an origin-tracked, profile-gated real-MIR route and
  exhaustive 64-pair VHDL evidence. It rejects C.OR/C.SUB/high-bit forms; the
  manifest records sixteen target-proven rows. Full-subset equivalence and
  release advertisement remain false.
- impl/verify: C.JR now has an origin-tracked, profile-gated typed HWIR graph
  and reserved real-MIR semantic-intrinsic route. The Q2 classifier fixes
  `funct3=100`, `bit12=0`, and `rs2=0`; an explicit second select rejects
  `rd=x0`. Generated VHDL exhaustively covers all 32 source-register fields and
  rejects C.MV and C.JALR neighbors. The manifest records seventeen target-proven
  rows; full-subset equivalence and release advertisement remain false.
- impl/verify: C.MV now has an origin-tracked, profile-gated typed HWIR graph
  and reserved real-MIR semantic-intrinsic route. Its Q2 classifier excludes
  C.JR/reserved `rs2=x0` encodings and bit12-set C.ADD; `rd=x0` is explicitly
  normalized to the architectural NOP hint. Generated VHDL exhaustively covers
  all 992 nonzero-`rs2` register combinations. The manifest records eighteen
  target-proven rows; full-subset equivalence and release advertisement remain false.
- impl/verify: C.JALR now has an origin-tracked, profile-gated typed HWIR graph
  and reserved real-MIR semantic-intrinsic route. Its Q2 classifier fixes
  `funct3=100`, `bit12=1`, and `rs2=0`, while excluding reserved `rd=x0` and
  adjacent C.JR/C.MV/C.ADD encodings. Generated VHDL exhaustively covers all
  32 source-register fields. The manifest records nineteen target-proven rows;
  full-subset equivalence and release advertisement remain false.
- impl/verify: C.ADD now has one typed elaborator that emits separate concrete
  RV32/RV64 graphs, never a runtime XLEN decision. Both reject `rs2=x0` and
  adjacent row encodings; the RV32 graph normalizes the x0 hint to NOP while the
  RV64 graph retains `ADD x0, x0, rs2`. Generated VHDL exhaustively covers all
  992 nonzero-`rs2` fields per product. The manifest records twenty target-proven
  rows; full-subset equivalence and release advertisement remain false.
- refactor/impl/verify: Strict-Zca row admission and target evidence now share a
  compiler-common contract catalog; reserved-looking uncontracted intrinsics
  fail before alternate strict lowering. C.ADDI16SP is the next proven row: its
  typed graph reconstructs the discontinuous signed stack-adjust immediate,
  gates `rd!=x2` and zero-immediate reserved encodings, and is selected by the
  exact real-MIR intrinsic. Generated VHDL exhaustively covers all 64 row
  encodings and excludes C.LUI/C.ADDI neighbors. The manifest records
  twenty-one target-proven rows; full-subset equivalence and release
  advertisement remain false.
- impl/verify: C.LUI is now independently admitted through the 21-contract
  canonical catalog and an RV32/RV64-specialized typed row constructor. Its
  Q1/funct3=011 graph rejects `rd=x0`, the `rd=x2` C.ADDI16SP overlap, and zero
  `NZIMM` before emission. Generated VHDL exhaustively covers all 2,048 row
  encodings and excludes the C.ADDI neighbor. The explicit target-proof
  allowlist now records twenty-two target-proven entries; full-subset
  equivalence and release advertisement remain false.
- impl/verify: The strict frontend now has a typed `HwPredecodeInterface`
  boundary. It materializes 16-bit parcel, 32-bit canonical instruction,
  two-bit length, one-bit legal/redirect flags, and product-specialized PA
  widths for fetch/next/redirect PCs. Non-critical profiles and malformed
  port direction or address width fail closed. This freezes the prerequisite
  interface for C.J/C.BEQZ/C.BNEZ without claiming their control semantics.
- impl/verify: C.J now consumes that contract in a typed strict-HWIR graph.
  It preserves the 16-bit parcel, derives the canonical JAL and sign-extended
  offset, and drives next-PC/redirect ports using concrete PA-width addition.
  Generated VHDL simulation covers positive and negative offsets plus a
  non-row fallthrough. Its aggregate `Bits[16], Bits[PA]` → six-field
  predecode-result real-MIR contract is fail-closed for RV32/RV64 and rejects
  scalar-PC substitutions. The explicit target-capability allowlist now records
  twenty-three advertised row-level entries; no full-Zca claim is made.
- impl/verify: `HwBranchPredecodeInterface` now freezes the conditional-row
  boundary: it adds explicit `rs1_index: Bits[5]` and product-specialized
  `rs1_value: Bits[XLEN]` inputs to the typed parcel/PC predecode contract.
- impl/verify: Typed C.BEQZ/C.BNEZ row constructors now reconstruct the CB
  immediate, canonical branch encoding, and selected-PC behavior using the
  explicit XLEN operand. Unit evidence validates the RV32/RV64 graph and
  strict VHDL rendering.
- impl: Exact aggregate C.BEQZ/C.BNEZ strict-MIR contracts now accept only
  `Bits[16]`, selected-PA `Bits`, `Bits[5]` register index, and selected-XLEN
  register value inputs with the six-field predecode result. Mismatched index/
  value binding fails closed without a legacy route.
- verify: RV32/RV64 generated-VHDL target vectors now prove C.BEQZ/C.BNEZ
  taken/not-taken, `+2`, `-2`, sign-sensitive `-256`, and cross-row fail-closed
  behavior. Their two explicit target-proof entries raise row-level evidence
  to twenty-five entries; full-Zca/release status remains false.
- impl: The subset manifest now distinguishes complete row evidence from the
  still-unproven composed frontend path: all 25 row proofs are present, while
  parcel/operand/redirect/retirement integration keeps release evidence false.
- impl/verify: `HwFrontendHandoffInterface` now freezes the Gen2
  frontend-to-dispatch boundary with the complete typed branch-predecode
  lineage plus one-bit `dispatch_accept` and `retire_valid` ownership signals.
  Its RV32/RV64 contract tests reject configuration drift and malformed
  ownership ports. It does not compose rows, own PC/retirement state, or claim
  protected-core equivalence.
- impl/verify: `strict_zca_control_predecode_hwir` now emits one flattened
  C.J/C.BEQZ/C.BNEZ control-predecode module for concrete RV32/RV64 products.
  Its GHDL vectors cover direct jump, both conditional predicates,
  mismatched-register-index fail-closed behavior, and unsupported parcel
  fallthrough. This is a stateless three-row slice only; full frontend and
  retirement claims remain false.
- impl/verify: driver VHDL target selection now rejects a nonempty
  `riscv_gen2_target` unless the snapshotted policy is critical, before stale
  artifact removal. A CLI scenario proves it cannot silently reach legacy VHDL.
- impl: Added the source-less compiler product route
  `riscv-gen2-zca-control-predecode-v1`. It accepts only critical concrete-Zca
  RV32/RV64 targets, rejects source/AOP contamination before cleanup, and
  writes an explicitly unqualified `hwir-gen2-product` artifact with empty
  user-source provenance rather than fabricating a source span.
- impl/verify: Added the first sequential strict-HWIR product:
  `HwParcelFrontendDef` captures one parcel/PC/branch-read tuple, blocks a new
  fetch until matching lineage retirement, preserves a stalled dispatch, and
  turns invalid retirement into a synchronous-reset-cleared sticky fault. Its
  renderer instantiates (rather than copies) the typed migrating decoder. RV32
  GHDL simulation covers capture/stall/release/fault/reset; RV64 VHDL analysis
  proves concrete 64-bit state specialization. This remains one-entry control
  integration, not full Zca or architectural retirement closure.
- impl/verify: The full-composition audit found that 22 non-control row graphs
  expose only zero-sentinel canonical output, so they cannot be safely muxed
  into a critical frontend. Added `strict_zca_addi4spn_outcome_hwir` as the
  first normalized adapter: explicit tag plus nonzero-immediate legality,
  canonical graph reuse, fixed fallthrough metadata, and generated-VHDL proof.
  The unsafe full-composition descriptor was removed before it could affect a
  product. Remaining rows are pending equivalent explicit-outcome migration.
- impl/verify: Added a private classifier-complete normal-row outcome adapter
  and public outcomes for C.LW, C.SW, C.SWSP, C.LI, C.ADDI/C.NOP, low-shamt
  shifts, C.ANDI, compact-R operations, C.MV, and C.ADD. Added the separate
  true-means-reserved chain for C.LWSP/C.LUI. Legality derives only from the
  frozen classifier/predicates, never its canonical word. C.LW/C.SW GHDL
  vectors prove matching/nonmatching behavior; the focused unit contract
  instantiates every admitted outcome and rejects the base configuration.
- impl/verify: Added `strict_zca_migrating_predecode_hwir`, a flattened
  deterministic composition of the three typed control rows and every admitted
  normal-row outcome. Every public predecode result is selected only through
  explicit `legal` signals; the canonical instruction is never a legality
  sentinel. The one-entry frontend now instantiates this decoder. Generated
  VHDL proves a C.LW selection and initially kept C.ADDI16SP illegal. This is
  partial-Zca evidence only and not a full decoder/core claim.
- impl/verify: Added the distinct source-less CLI/driver product
  `riscv-gen2-zca-migrating-predecode-v1`. It shares the critical target and
  no-source/no-AOP gates with the historical three-row product but records a
  different compiler-product identity, graph node, and concrete port manifest.
  Its end-to-end CLI scenario emits and GHDL-analyzes RV32 VHDL without any
  fabricated user-source provenance. The old control-product identity remains
  stable; neither product advertises full Zca or architectural retirement.
- impl/verify: C.ADDI16SP now has a normalized outcome that explicitly
  requires its Q1/funct3 classifier, `rd=x2`, and a nonzero stack-adjustment
  immediate. The migrating decoder admits that outcome and GHDL proves a
  positive parcel (`0x6105 → 0x02010113`) plus reserved-zero fallthrough.
  C.JR/C.JALR and C.EBREAK initially remained excluded pending typed indirect
  redirect and trap contracts.
- impl/verify: Added typed C.JR/C.JALR predecode wrappers around the existing
  canonical row graphs. Each wrapper binds the decoded source-register field to
  `rs1_index`/`rs1_value`, reduces only to concrete PA width, and clears the
  target low bit with shift operations. The migrating decoder now includes both;
  generated VHDL proves C.JR/C.JALR aligned redirects and index-mismatch
  fail-closed behavior. C.EBREAK remains excluded because the frozen predecode
  interface has no trap/effect output.
- impl: Added the versioned `HwTrapPredecodeInterface` and the compiler-owned
  C.EBREAK trap row. It carries a legal canonical EBREAK plus typed XLEN-wide
  breakpoint cause 3 and zero tval, while nonmatches emit no effect. The v1
  migrating product is intentionally unchanged until a stateful v2 trap/retire
  handoff exists.
- verify: Focused unit and system specifications completed through the bootstrap
  seed. The system scenario emits, analyzes, elaborates, and simulates the
  C.EBREAK v2 row with GHDL; this is target row evidence only, not product or
  protected-core trap-retirement evidence.
- impl: Added the versioned `HwTrapParcelFrontendDef` and source-less critical
  `riscv-gen2-zca-trap-single-outstanding-v2` product. It captures the typed
  C.EBREAK request, assigns one dispatch/retirement owner, gates `trap_valid`
  with active dispatch, zeroes cause/tval after acceptance, and records both
  generated VHDL entities in the no-source manifest. V1 remains unchanged.
- verify-blocked: The checked-in `bin/simple` is a bootstrap seed. Its direct
  CLI invocation reports diagnostics but does not produce the requested output
  artifact, while this checkout has no self-hosted `simple` executable under
  `bin/release/<triple>/`. Do not treat bootstrap-seed helper tests as release
  or critical product-route evidence. Rebuild/deploy the self-hosted runtime,
  then rerun the single v2 CLI emission/manifest/GHDL scenario.
- impl/verify: Published v1/v2 admitted Zca ID lists and added a contract test
  that closes v2 exactly over the declarative 25-entry critical subset while
  proving v1 omits only C.EBREAK. This prevents capability-table/composition
  drift but does not satisfy the pending generated-RTL equivalence obligation.
- impl/verify: Added the isolated RV32 C.JAL strict row by reusing the typed
  J-immediate graph with an explicit canonical x1 link field. RV64 rejects
  before elaboration to avoid conflating the same compressed class with
  C.ADDIW. GHDL vectors cover positive/negative redirects and C.J exclusion;
  the row remains outside all common-profile/product capability claims.
- impl: Restored the missing strict-HWIR schema definitions required by the
  untracked Gen2 rows/frontends/backend: concrete `CoreConfig`, node/origin,
  constant/compare/mux, state-register, and validated `HwModuleDef` records.
  Shape validation now rejects malformed configurations, count drift, invalid
  domains, unknown values, duplicate drivers, and undriven public outputs.
- impl: Restored the strict HWIR-to-VHDL serializer source after an audit found
  tests and product code referenced APIs absent from the backend. The emitter is
  finite and fail-closed; it emits typed combinational operations and bounded
  one-entry product renderers without legacy fallback. Source-driver critical
  routing remains absent, so this does not upgrade product status or evidence.
- impl: Restored the source-driven critical boundary: `CompileContext` captures
  typed assurance policy once, `CompileOptions` carries explicit Gen2 target
  data, and the VHDL driver selects strict real-MIR lowering before legacy
  emission. Strict route provenance records the concrete node/config and
  rejected strict builds clean no artifact. The bounded lowerer supports only
  non-generic combinational fixed-width bitwise/constant graphs; all other MIR
  remains fail-closed. Removed a duplicate generic `HwStateRegister` class so
  the stateful frontend is the single runtime owner of that name.
- impl: Extended real strict-MIR admission with shape-checked declarative Zca
  intrinsics. Each approved intrinsic maps directly to an existing typed row
  constructor; unknown/malformed names, signatures, operands, returns, and
  product profiles reject with `HWIR-E-*`. The terminal C.EBREAK/C.ADDI CFG is
  matched structurally, including its tag, branch edges, selected join value,
  and canonical instruction literal.
- impl: Hardened `HwModuleDef` validation for mission-critical emission:
  VHDL-safe stable identifiers, writable results, readable operands,
  serializer-compatible operation widths, self-cycle and multiple-driver
  rejection, constant fit checks, and origin/module identity separation.
  Canonical typed combinational graphs now carry a deterministic SHA-256 into
  strict-source and combinational compiler-product provenance.
- impl: Exposed all three implemented source-less Gen2 product IDs through
  the VHDL CLI and corrected stateful/trap provenance so the returned route,
  VHDL header, and manifest route agree. Stateful products retain explicit
  route provenance but are not misrepresented as fully serialized
  combinational graph hashes.
- verify-blocked: A `bin/release` wrapper exists, but it rejects the deployed
  runtime as non-production. Bootstrap checks parse and run focused specs but
  remain non-qualification evidence. Rebuild/deploy a production self-hosted
  runtime before treating CLI artifact or GHDL system scenarios as critical
  evidence.
- safety-correction: The stateful/trap source-less product routes were found to
  serialize a fixed VHDL register machine rather than lower typed sequential
  HWIR, and their artifacts had no canonical graph closure. Critical emission
  now rejects them with `HWIR-E-SEQUENTIAL-UNSUPPORTED` before artifact cleanup.
  Every compiler-owned HWIR artifact route now requires a graph SHA-256. The
  parcel/trap definitions remain frozen migration contracts until sequential
  nodes own emission, reset, and transition semantics.
- impl: Replaced the stateful frontend serializer's embedded state machine with
  `HwSequentialPlan`: typed state registers, priority guards, assignments,
  decoder pins, and output bindings now drive emitted VHDL. Stateful/trap
  products again require a 64-character decoder-closure graph hash and the v2
  driver records it in the compiler-product manifest. Qualification remains
  pending the self-hosted CLI and GHDL protocol scenarios.
- test: Added the RV32/RV64 generated-VHDL protocol scenario for the typed
  trap frontend. It proves C.EBREAK visibility, issued-entry backpressure,
  mismatched retirement, sticky fault containment, fetch refusal, stale-effect
  suppression, and synchronous reset recovery once the qualified runtime can
  execute the SSpec/GHDL lane.
- impl: Added deterministic sequential-HWIR node subtrees beneath each typed
  frontend (`register`, `decoder_pin`, `rule`, and `output`) and made the VHDL
  serializer emit those IDs as source-lineage comments. The plan identity is
  included in its closure hash, so a manifest cannot describe a graph whose
  emitted lineage anchors came from another state plan.
- verify: The focused HWIR foundation test completed through the bootstrap seed
  with its known warning-only limitation; `git diff --check` passed. This does
  not qualify the emitted VHDL or replace the pending self-hosted GHDL lane.
- safety-correction: Removed the obsolete artifact-layer quarantine of typed
  `hwir-gen2-stateful-product` and `hwir-gen2-trap-stateful-product` routes.
  The manifest validator now admits them only under the same nonempty module,
  profile, and 64-character closure-hash checks required by every strict HWIR
  product; unknown source-less route names still fail. The focused artifact
  contract test ran through the bootstrap seed only, so self-hosted product
  CLI and GHDL qualification remain open.
- safety-correction: Kept common-Zca target-capability truth conservative.
  The complete row catalog remains available for coverage and drift checks, but
  `row_target_evidence_complete` and its derived predicate remain false until
  the self-hosted generated-RV32/RV64 VHDL/GHDL scenarios execute. Static
  allowlist membership cannot turn unrun target tests into a critical claim.
- impl: Added a `riscv` capability block to production VHDL manifests. Compiler-
  owned Gen2 products now carry the concrete scalar ISA profile and bounded
  compressed decode profile, and validation rejects a source-less Gen2 product
  missing either value. Target evidence remains explicitly false pending the
  self-hosted GHDL receipt. Added a compact product-provenance system scenario
  and operator manual for closure-hash/header/lineage checks.
- recovery: The untracked sequential-HWIR source was found unexpectedly empty
  during the shared-worktree migration. Restored its full typed schema using
  `apply_patch`, made direct-imported classes explicitly public, and reran the
  focused compiler and HWIR contract gates through the bootstrap seed. The
  original large Gen2 system spec was also found concurrently truncated; it was
  preserved untouched and the new independent provenance scenario retains the
  newly added coverage until its owner restores the broader scenario content.
- impl: Added `riscv_common.retire.RiscvRetireRecord` as the first shared
  RV32/RV64 architectural retirement boundary. Existing RVFI snapshots now
  project through thin width-specific adapters into a common explicit-XLEN
  record with canonical/original instruction, length, PC, writeback, memory,
  trap, and interrupt fields. The record fails closed on invalid XLEN, length,
  x0 writes, and non-AMO simultaneous memory masks. This is host/formal/debug
  metadata; it does not add runtime XLEN selection to emitted hardware.
- impl: Migrated the concrete retire-chain theorem to consume
  `RiscvRetireRecord` directly. It rejects malformed valid records and mixed
  RV32/RV64 traces before non-vacuous monotonic-order/PC-chain checks, while
  intentionally ignoring non-retiring cycle samples. The focused unit lane
  completed only through the bootstrap seed; self-hosted formal/HDL evidence
  remains required for mission-critical qualification.
- recovery: The full foundation system scenario is present again. Its typed
  RV32/RV64 v2 trap-front-end vectors cover issued-entry backpressure,
  mismatched retirement, sticky-fault containment, fetch refusal, stale-effect
  suppression, and synchronous reset recovery. This is executable evidence
  awaiting the self-hosted compiler/GHDL receipt, not a release claim.
- safety-correction: Shared retire-chain checking now treats an interrupt as an
  architectural control-transfer exception to ordinary PC chaining, alongside
  synchronous traps. A regression record pair proves an interrupt redirect is
  accepted without weakening checks for normal retirements.
- impl: Added `riscv_common.isa.scalar_database` as the first shared scalar
  semantic seed. I/M and RV64-specific word/shift rows now declare exact
  masks, XLEN scope, semantic operation, effects and trap behavior; invalid
  entries and duplicate IDs fail closed. RV32/RV64 shift masks are separate so
  the sixth RV64 shamt bit cannot be silently rejected. The focused seed test
  passed only through the bootstrap runtime; execution-provider, decoder, and
  whole-toolchain generation remain future lanes.
- safety-correction: The scalar table now rejects ambiguous masked encodings
  per concrete XLEN before any decoder generator can assign accidental table
  priority. Corrected `FENCE` to the I extension while retaining `FENCE.I` as
  Zifencei. The new overlap regression awaits a self-hosted rerun.
- impl: Added deterministic host-side `riscv_scalar_lookup` over the validated
  concrete RV32/RV64 table. It returns one entry or stable invalid-XLEN/
  undeclared-instruction diagnostics; it is deliberately not an RTL selector
  and is the first planned consumer boundary for generated decoder/toolchain
  metadata. Its added regression awaits a self-hosted rerun.
- impl: Added profile-specialized scalar entry/lookup APIs. `rv32i`/`rv64i`
  views admit I rows only; explicit `rv32im`/`rv64im` views add M rows, while
  Zca suffixes remain delegated to compressed metadata. This is elaboration
  selection only and does not add a runtime extension selector.
- safety-correction: `CoreConfig` now rejects unsupported scalar profile IDs
  and RV32/RV64 profile/XLEN mismatches before HWIR lowering. The foundation
  spec adds both negative cases; the changed compiler module passes only the
  bootstrap syntax diagnostic pending a self-hosted run.
- impl: Added typed Gen2 HWIR aspect manifests and plans. They are compiler-host
  metadata applied to stable semantic node IDs, never text-level VHDL patches
  or runtime loaders. Validation rejects unsupported/textual advice, bad
  identity/hash/join-point/effect metadata, conflicts, duplicate applications,
  and required zero-match/zero-weave plans; the absent plan is structurally
  empty. Focused tests passed through the bootstrap runtime only. A typed graph
  weaver and build lockfile/provenance integration remain pending.
- impl: Added the first actual typed HWIR aspect transform: a matched,
  transparent, state-free observational manifest may add only its declared
  output/pass-through probes. The weaver validates semantic-node binding,
  resource count, source readability and port collisions; it derives origin
  IDs, recomputes the graph digest, and reruns the strict HWIR legality checks.
  Disabled plans reject probes and preserve the exact original graph. The
  focused interpreter result is bootstrap-seed diagnostic evidence only;
  state/timing/provider transforms, lockfiles, proof execution and artifact
  provenance integration remain unimplemented.
- verify: The focused aspect contract now also passes the woven graph directly
  to strict VHDL emission and checks the declared probe port and pass-through
  assignment while preserving the explicit no-legacy-fallback result. This
  execution used the bootstrap seed and is not critical qualification.
- safety-correction: Aspect effects now require their corresponding named proof
  obligation (`architectural_noninterference`, `cycle_equivalence`,
  `retirement_equivalence`, `differential_isa`, `fault_free_equivalence`, or
  `interface_refinement`) rather than accepting arbitrary proof metadata. The
  focused seven-example manifest/weaver/serializer specification passed only
  through the bootstrap seed.
- safety-correction: The module-level observational weaver now rejects a plan
  whose claimed weave count differs from its materialized typed probe count or
  whose match names another module. Focused adversarial regressions are added;
  they await the self-hosted runtime rather than another bootstrap rerun.
- impl: Added compiler-host scalar I/IM provider elaboration. A base-I profile
  must select `none`; an IM product must select exactly `iterative`,
  `pipelined`, or `dsp`, retaining the exact validated profile table and one
  fixed provider identity for each M row. It is not an RTL selector or runtime
  service lookup. Lookup rejects a forged row not structurally owned by that
  table. The focused seven-example scalar-ISA specification passed through the
  bootstrap seed only; HWIR resource binding remains pending.
- impl: Added typed `HwAspectLock` identity pinning. The locked observational
  weaver rejects any plan whose exact manifest ID/version/content-hash set is
  not present before graph mutation. The focused three-example lock contract
  passed through the bootstrap seed only; lockfile discovery remains pending.
- impl: Extended deterministic VHDL artifact provenance with a typed aspect
  lock digest and pinned identity list. Compiler-owned Gen2 products now carry
  the digest of the empty lock explicitly, and any later enabled aspect must
  serialize in canonical ID/version/hash order; the focused bootstrap-seed
  contract passed. Aspect identities have unique ID/version/content-hash
  provenance; self-hosted artifact execution remains the qualification gate.
- impl: Artifact validation now rebuilds the typed aspect lock from the pinned
  manifest entries and rejects any digest mismatch, including a forged digest
  with valid length. The expanded bootstrap run was warning-truncated, so this
  branch still requires one self-hosted focused receipt before qualification.
- impl: Added a typed migrating-Zca row-overlap accumulator. Any accidental
  multiple legal classifiers now force canonical zero, `legal=0`, fall-through
  `PC+2`, and no redirect instead of letting declared mux priority redefine an
  instruction. The focused bootstrap test was warning-truncated; a self-hosted
  strict-VHDL receipt remains required.
- impl: Added `rv32i_zmmul`/`rv64i_zmmul` scalar elaboration profiles. They
  derive the four common M multiply rows plus RV64 `MULW` and require one fixed
  multiply provider, while divide/remainder rows remain absent and illegal.
- impl: Added `HwirRiscvScalarBindingPlan`, which maps selected scalar
  multiply/divide ISA rows to concrete area/balanced/speed target binding
  identities. It is plan-only—resource instance lowering and latency-changing
  RTL remain separate, unqualified work.
- impl: Hardened scalar binding latency provenance: Gen2 plans use only
  `uncommitted` latency with `-1` cycles, while legacy optimizer heuristics are
  marked `estimated`. A timing estimate can no longer masquerade as a critical
  RTL latency contract.
- impl: Hardened scalar provider selection before binding planning: each
  selected entry now must equal the complete elaborated ISA row in canonical
  table order. Matching only an ISA ID cannot admit altered encoding, width,
  operation, or effect metadata.
- impl: Hardened the single-outstanding stateful frontend output boundary.
  Decoded parcel/PC/redirect metadata is now guarded by the internal active
  dispatch state and zeroes after issue, protocol fault, or reset; only lineage
  remains available for retirement matching. Sequential guards no longer read
  public outputs. The RV32/RV64 trap protocol scenario asserts this containment.
- impl: Extended the shared RV64 scalar ISA table with all W-shift forms
  (SLLIW/SRLIW/SRAIW/SLLW/SRLW/SRAW). Each is a 32-bit declarative operation
  with the shared sign-extend-to-XLEN writeback rule, avoiding a copied RV64
  execution implementation. Decoder/provider/toolchain lowering remains open.
- impl: Added the RV64-only memory rows LD/LWU/SD to the same scalar table.
  LWU records 32-bit zero extension, while LD/SD remain XLEN-width. This is
  semantic metadata only and does not yet imply an RV64 LSU implementation.
- safety-correction: Bare scalar I, IM, and Zmmul profiles no longer silently
  admit Zicsr/Zifencei rows. Those rows require the explicit combined profile
  suffix, so the profile table cannot over-advertise ISA capabilities merely
  because the shared seed database knows their encodings.
- impl: Added `RiscvScalarDecoderPlan`, a deterministic compiler-host consumer
  of the scalar database. It freezes and hashes the exact elaborated profile
  rows, fails closed for a forged row or undeclared instruction, and provides
  a future decoder/disassembler/coverage lowering boundary without runtime ISA
  selection or an RTL decoder claim.
- impl: Added `RiscvGen2ScalarElaboration`, one compiler-host aggregate for a
  concrete `CoreConfig`, scalar decoder plan, and selected provider plan. It
  rejects cross-object XLEN/profile drift and gives RV32/RV64 separate stable
  identities before HWIR lowering. Its node identity includes profile, XLEN,
  PA width, and register count so concrete valid configurations cannot alias
  provenance. It is not a runtime selector or scalar RTL completion claim. The
  bootstrap-seed combined check/test receipt was
  warning-truncated, so self-hosted execution remains required.
- impl: Added `RiscvGen2ScalarDispatchPlan`, the compiler-host bridge from one
  frozen product to one exact scalar ISA row and its fixed provider identity.
  It fails closed for rows absent from the product table or entries not
  structurally owned by the provider selection; it is a future execution-unit
  input, not a runtime decoder or completed scalar RTL claim.
- safety-correction: Strict real-MIR admission now validates binary operation
  type rules, Boolean branch conditions, and declared `If`/`Goto` targets before
  any specialized HWIR row extraction. Malformed MIR cannot be normalized into
  a trusted Gen2 hardware graph.
- safety-correction: Sequential-HWIR canonicalization now includes output
  guards. A change to ready/valid, redirect, fault, or trap visibility logic
  therefore changes the compiler-product graph SHA and cannot evade artifact
  provenance checks.
- safety-correction: VHDL artifact provenance now accepts only canonical
  lowercase hexadecimal SHA-256 values for compiler, source, HWIR graph, and
  typed aspect identities; matching length alone is not treated as evidence.
- safety-correction: Compiler-owned Gen2 artifacts now carry concrete port
  widths and fail closed unless their complete ordered port contract matches
  the selected typed HWIR product. This closes manifest-only interface drift.
- impl: Extended the shared `RiscvRetireRecord` rather than creating a Gen2
  duplicate. It now retains privilege and validates compressed original-parcel
  width plus canonical instruction shape, giving RV32/RV64 migration one
  precise architectural-retirement evidence boundary.
- safety-correction: The initial HWIR observational aspect transformer now
  admits only its implemented RTL `module.port` join point. Broader manifests
  cannot be recorded as woven until their own typed transforms exist.
- safety-correction: Compiler-owned Gen2 VHDL manifests now state that the
  emitted artifact is `frontend-predecode-only`, carry the exact selected
  compressed instruction IDs, and hash that capability closure. Validation
  reconstructs the list from the typed product, so an elaboration-time
  `rv32i`/`rv64i` profile cannot be misread as a complete processor claim.
- impl: Added a separate RV32-only C.JAL migrating frontend product. It uses a
  distinct concrete `rv32i_zca` profile, composes the existing typed C.JAL row
  with the common migrating graph, and emits an exact capability closure. The
  common and RV64 products continue to reject that parcel class.
- impl: Added the reciprocal RV64-only C.ADDIW migrating frontend product. It
  uses `riscv-gen2-rv64-zca-addiw-critical`/`rv64i_zca`, reconstructs the
  signed six-bit immediate, explicitly rejects `rd=x0`, and preserves a
  separate frontend-only capability closure. RV32 C.JAL and RV64 C.ADDIW are
  never selected by a runtime XLEN mux.
- impl: Bound the one-entry stateful parcel frontend to the same concrete
  decoder selection. C.JAL and C.ADDIW now instantiate dedicated stateful
  frontend entities with their decoder dependency present in the sequential
  graph hash; this extends typed dispatch/retire lineage but remains below a
  complete scalar-core boundary.
- impl: Exposed the RV32 C.JAL and RV64 C.ADDIW stateful frontends as separate
  compiler-owned CLI product IDs. Artifact validation now requires their exact
  profile, stateful entity, and decoder dependency rather than accepting a
  generic frontend manifest.
- safety-correction: Strict `CoreConfig` profiles now use a bounded safe-label
  grammar and strict HWIR identifiers reject VHDL reserved words. Free-form
  configuration or graph names therefore cannot inject raw VHDL through route
  provenance comments; focused rejection coverage was added.
- safety-correction: Combinational and sequential graph identities now use
  versioned length-prefixed canonical fields rather than delimiter-only text.
  Origin, port, plan, and decoder metadata with embedded delimiters cannot
  alias a distinct typed graph hash. This changes development-stage Gen2 graph
  hashes and requires new self-hosted product receipts.
- verify-blocked: The focused strict-HWIR unit rerun exceeded the bootstrap
  test daemon's 120-second worker budget. Treat this as bootstrap diagnostic
  infrastructure failure, not a passing or failing qualification result; rerun
  once with the required admitted self-hosted runtime.
- verify-blocked: The generic exported VHDL artifact render/write protocol can
  still pair a valid-looking Gen2 manifest with caller-supplied VHDL. The
  normal Gen2 driver recomputes identity before use, but a separate trusted
  Gen2-only writer is required before release; see
  `doc/08_tracking/bug/riscv_gen2_raw_artifact_writer_provenance_2026-08-12.md`.
- verify-blocked: The bounded stateful parcel frontend still lacks the
  architectural `RetireRecord` producer binding and an explicit 64-bit lineage
  wrap lifetime rule. Its local reset/fault behavior is development-stage only;
  see `doc/08_tracking/bug/riscv_gen2_stateful_retire_lineage_contract_2026-08-12.md`.
- safety-correction: The generic raw artifact writer now refuses all
  compiler-owned Gen2 routes before stale-artifact cleanup, while the Gen2
  product driver uses a revalidating writer. The writer is still exported with
  serializable inputs, so an opaque private emission receipt remains a release
  blocker; see `riscv_gen2_raw_artifact_writer_provenance_2026-08-12.md`.
- safety-correction: Terminal matching retirement at the 64-bit all-ones
  lineage now clears the outstanding entry and raises sticky fault instead of
  incrementing. This prevents wrap and token reuse before reset; the remaining
  blocker is reset-coupling to the real retirement producer, not a no-wrap
  lifetime assumption.
- safety-correction: The Gen2 writer no longer exports an artifact-module API
  that accepts serializable product input and raw VHDL. Product persistence now
  runs through a private driver receipt; Simple visibility remains advisory, so
  this narrows the supported boundary without claiming language-enforced
  non-forgeability.
- safety-correction: The bounded stateful frontend retirement guard now binds
  the outstanding transaction by the conjunction of 64-bit lineage, original
  16-bit parcel, canonical 32-bit instruction, and two-bit original-length
  encoding. A valid retirement with any mismatched identity field follows the
  sticky `protocol_fault` path and cannot release the entry as successful.
  This supersedes earlier lineage-only and missing-wrap-rule descriptions;
  architectural `RiscvRetireRecord` producer wiring and shared-reset closure
  remain open.
- safety-correction: Earlier statements that the v1 product or frontend
  "remains unchanged" apply only to the v1 decoder's ISA composition. The new
  retirement identity ports change the stateful frontend ABI, port sequence,
  and closure hash. Existing product/version labels are not qualification
  evidence and require an explicit versioning decision plus fresh receipts.
- verify-blocked: Available retirement-identity checks use the Rust bootstrap
  seed and one expanded run was warning-truncated. They are development
  diagnostics only, not proof that the generated reuse/reset fixture or its
  VHDL/GHDL behavior qualifies. Record one provenance-admitted self-hosted
  focused receipt before changing mission-critical qualification status.
- verify-blocked: Self-host qualification was re-audited on 2026-08-12. The
  deployed `bin/simple` has no adjacent Stage-4 provenance receipt; the only
  isolated candidates are Stage-2 products, while the current authority build
  ends `exit-1`. Active unrelated native builds mean no bootstrap may start in
  this shared checkout. The compiler/bootstrap owner must first produce an
  admitted non-vacuous Stage-3 and `pure-simple-full-cli` Stage-4, then run
  the exact RV32/RV64 foundation commands recorded here. See
  `doc/08_tracking/bug/self_hosted_runtime_authority_republish_path_2026-08-12.md`.
- impl: Added a prepared strict-HWIR host evaluator and an exhaustive composed
  target-trap oracle. The oracle executes all 65,536 parcels for each RV32
  C.JAL and RV64 C.ADDIW product through independently prepared typed graphs,
  checking full tuple determinism, closed legal/illegal/trap partitioning, and
  the sole C.EBREAK trap. This is a compiler-host composition check, not
  independent generated-RTL equivalence or a qualification receipt.
- impl: Added a verification-only one-entry, reset-coupled retirement receipt
  loopback model. It proves host-model tuple capture, one-cycle return, reset
  priority, and stale-receipt erasure. It has an explicit production rejection
  and no emitter/product API; it does not replace the real architectural commit
  owner or resolve the retirement-lineage tracking issue.
- impl (2026-08-14): Migrated standalone sequential VHDL emission to one typed
  mixed combinational/sequential HWIR owner. `HwSequentialModuleDef` now owns
  typed datapath values and operations, validates readable sources, widths,
  names, and exactly-one-driver semantics, renders the datapath before state,
  and commits it to the v3 structural hash. Added explicit `LsuConfig` product
  geometry and restored the five-case executable/manual pair.
- refactor (2026-08-14): Refreshed architecture, detail design, the RISC-V VHDL
  guide, executable step/requirement annotations, generated/manual companion,
  and canonical agent plan. Added the compiler-HWIR layer expert and linked the
  existing VHDL generator/hardware-RTL experts so the distinct backend owners
  are explicit; the private overlay wiki has no separate page for this slice.
- verify-blocked (2026-08-14): Static numbered-artifact and direct-runtime
  guards pass, the spec layout count is zero, and the changed files contain no
  placeholder assertions or stubs. The canonical wrapper rejects its deployed
  runtime ABI and direct self-hosted `check`/focused-test execution exits by
  signal 11. Resume exactly once after an admitted self-hosted CLI is deployed:
  `bin/simple test test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl --mode=interpreter`,
  `bin/simple check src/compiler`, `bin/simple check src/lib`,
  `bin/simple check src/app/mcp`, `bin/simple check src/app/simple_lsp_mcp`,
  `SIMPLE_LIB=src bin/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`,
  `bin/simple lint src/compiler/50.mir/hwir/riscv_lsu_config.spl src/compiler/50.mir/hwir/riscv_scalar_retirement_owner.spl src/compiler/50.mir/hwir/sequential.spl src/compiler/70.backend/backend/hwir_to_vhdl.spl test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl`,
  `bin/simple duplicate-check src/compiler/50.mir/hwir --mode token --min-lines 5`,
  and `bin/simple sspec-maintain scan test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl`.
  This is an implementation handoff, not verify PASS or Gen2 umbrella
  completion. Owner and final reviewer remain `/root`.
- review-blocked (2026-08-14): Independent highest-capability review found the
  qualification wrapper/composer contract is internally inconsistent before
  runtime execution: the wrapper requests unsupported `--emit-evidence` and
  `--compose-receipt` modes and validates a different schema/field layout from
  `src/app/test/riscv_gen2_qualification_receipt.spl`. This is tracked in
  `doc/08_tracking/bug/riscv_gen2_hwir_qualification_contract_mismatch_2026-08-14.md`.
  A deployed runtime alone does not unblock qualification.
- impl (2026-08-14, A13 follow-up): Parcel and trap product emission now adapts
  the already validated fixed frontend contract into `HwSequentialModuleDef`,
  binds the actual compiled decoder graph hash, and uses
  `render_strict_sequential_hwir`. The former private stateful renderer and
  hash schema were removed; decoder VHDL is prepended exactly once. The public
  hash recomputation helper remains as a compatibility API but constructs the
  canonical v3 typed graph, so drivers and manifests share one hash owner.
- design-frozen (2026-08-14, A14): The qualification runner is the phase-one
  command/evidence owner; the admitted Simple receipt app is the sole
  phase-two validator/copier and writes the receipt last. The final directory
  remains absent during staging. Schema v2 must hash-bind the coverage command,
  changed files, exclusions, testbench, and each GHDL command/log/exit. The
  current contradictory runner is not accepted and remains WARN-blocked until
  this contract and its deliberate-red tests execute on the repaired runtime.
- impl (2026-08-14, A14): Replaced the contradictory runner modes with a
  runner-owned private staging phase and an admitted-CLI invocation of the
  fixed Simple composer. Schema v2 exact-key binds measured coverage command
  and report, changed files, explicit exclusions, both product commands,
  generated VHDL/manifests/testbenches, separate GHDL commands/exits/logs, and
  source/config/graph identities. The composer rehashes and copies every bound
  file and writes the receipt last. Static shell/source checks are development
  evidence only; the positive and deliberate-red Simple suite plus a real
  admitted RV32/RV64 receipt remain blocked by the deployed runtime ABI/SIG11.
- review-blocked (2026-08-14, A14): Parallel adversarial review corrected the
  content-SHA/Git-revision mismatch, critical-policy omission, workspace-CLI
  child leakage, shared GHDL work library, missing reuse/identity vectors,
  partial-final cleanup, real `riscv32`/`riscv64` artifact target binding, and
  coverage scalar/list cross-checks. Remaining acceptance requires a complete
  executable compiler-inventory and writer-level deliberate reds
  for command grammar, duplicate-safe artifact parsing, destination rehash,
  canonical parents, mutation, and cleanup. Until then A14 is WARN, not PASS.
- review-history (2026-08-14, A14 coverage inventory): the rejected runtime-
  extern/wrapper-time draft was removed. The accepted source now emits from the
  compiler after complete parsing without expanding runtime ABI. Acceptance
  still requires an admitted self-hosted end-to-end receipt; a seed or crashing
  Stage-3 fixture is not evidence. Phase remains `implementation-handoff` / WARN.
- review-blocked (2026-08-14, A14 receipt authority): the runner's current
  `base..HEAD` scope includes unrelated later `.spl` changes. Exact command,
  duplicate-safe JSON, parent canonicality, and destination rehash are now
  implemented at source level, but executable runner/writer deliberate-reds
  remain absent. These are active resume items, not exclusions.
- impl (2026-08-14, A14 inventory continuation): added constructor-defined,
  tag-dispatched flat-AST ownership for declaration/statement/expression/arm
  overloads, including trait and CLI declaration bodies, dict/struct/lambda
  values, and ordinary versus assembler match arms. Parser and placeholder
  desugar now preserve source spans; compiler inventory emits bounded,
  deterministic, deduplicated zero-count rows with runtime-identical keys and
  escaping. Highest-capability static review is green. Executable acceptance
  remains WARN because the authorized Stage-3 command exits 139.
- verify-blocked (2026-08-14, user-authorized Stage 3): the only local candidate
  is `bootstrap/stage3/simple`, SHA-256 `905ce03696a4726e41e410e0531d39f84df2d26d1588e2a23206ede3c177793b`.
  It exposes only `compile`/`native-build`, is byte-identical to Stage 1/2, and
  has no adjacent provenance receipt. The exact focused ownership-spec
  `native-build` exited 139 before diagnostics; logs are retained at
  `/tmp/restart12-flat-ast-ownership-stage3-build.log`. This cannot satisfy
  AC-4/AC-5 or convert WARN to PASS.
  The distinct advertised `compile ... --format=smf` route was attempted once
  after the static-green source handoff and also exited 139; its log is
  `/tmp/restart12-flat-ast-ownership-stage3-smf.log`.
