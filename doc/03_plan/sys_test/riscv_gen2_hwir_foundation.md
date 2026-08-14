# RISC-V Gen2 HWIR Foundation — Test Plan

## Evidence status

The strict HWIR, compressed-row, provenance, and stateful frontend paths are
implemented with executable unit and SSpec coverage. The currently deployed
`bin/simple` identifies as a Rust bootstrap seed, so its test and GHDL activity
is diagnostic only. No row, stateful protocol, or compiler-product result is a
self-hosted qualification proof until the exact commands in **Current-host
evidence and resume** execute with a provenance-admitted self-hosted CLI.

The stateful product is deliberately development-stage: its 64-bit lineage
requires a reset-coupled retirement producer. A terminal matching retirement
now faults before increment, so it cannot wrap or reuse a token before reset.
Retirement acceptance additionally requires exact original parcel, canonical
instruction, and original-length matches. Independent same-lineage identity
mutants must enter sticky fault and must not release the outstanding entry.
It is not a complete processor frontend, core, or Zca claim.
Compiler-owned Gen2 artifacts use a Gen2-only persistence path; the generic
raw writer rejects those routes before cleanup. The product driver's private
receipt narrows the public boundary; language-enforced opaque receipt semantics
are still required before release and must not be treated as qualification
evidence.
The retirement composition renderer is likewise quarantined until it receives
a typed architectural producer emission receipt; metadata-bearing VHDL text is
not accepted as evidence of a child implementation.

Every GHDL “proves”, “covers”, or “simulates” row below is a required planned
qualification scenario until its self-hosted receipt is retained; bootstrap
diagnostics and source-level assertions do not satisfy a target-evidence row.

| Requirement | Implemented check or qualification receipt required |
| --- | --- |
| REQ-G2-001 | schema/origin construction and uniqueness unit tests |
| REQ-G2-002 | RV32/RV64 valid and invalid configuration tests |
| REQ-G2-003 | strict lowering success and diagnostic/no-fallback tests |
| REQ-G2-004 | non-empty deterministic VHDL, ports, assignment and IDs tests |
| REQ-G2-004 target syntax | strict RV32 HWIR VHDL written and analyzed with GHDL VHDL-2008 |
| REQ-G2-004 parcel mask | typed `u32` constant + AND graph written and analyzed with GHDL VHDL-2008 |
| REQ-G2-004 parcel shift | typed bounded `u32` right-shift graph written and analyzed with GHDL VHDL-2008 |
| REQ-G2-004 parcel field | typed two-stage shift/mask internal-signal graph written and analyzed with GHDL VHDL-2008 |
| REQ-G2-004 parcel field behavior | GHDL elaborates and simulates `0xA000 >> 13 & 7 == 5` |
| REQ-G2-004 C.EBREAK leaf | GHDL elaborates and simulates canonical `0x00100073` constant output |
| REQ-G2-004 C.EBREAK selection | GHDL elaborates and simulates typed equality/select for matched `0x9002` and unmatched `0x0001` parcels |
| REQ-G2-003 C.EBREAK real MIR | exact frontend-style four-block `Eq`/`If`/copy/join graph lowers; altered miss edge rejects without legacy fallback |
| REQ-G2-003 terminal leaf sharing | C.EBREAK and C.NOP use one closed terminal-lowering implementation; unknown literals reject |
| REQ-G2-003 C.NOP row sharing | validated C.NOP terminal CFG selects the C.ADDI/C.NOP constructor; no alternate semantic graph exists |
| NFR-G2-008 profile gate | terminal compressed lowering rejects a base/non-critical `CoreConfig` before HWIR construction |
| REQ-G2-004 canonical field shift | exact typed `u32` `Const` then `Shl` lowers and emits `numeric_std.shift_left` |
| REQ-G2-004 C.ADDI critical graph | typed common-Zca C.ADDI/C.NOP field assembly has positive, negative-immediate, and non-row GHDL vectors |
| REQ-G2-004 C.ADDI row equivalence | generated VHDL exhausts all 2,048 C.ADDI/C.NOP row encodings and checks canonical ADDI assembly |
| REQ-G2-003 C.ADDI16SP real MIR | the reserved one-input semantic intrinsic resolves only through the canonical strict contract and a concrete critical RV32/RV64 configuration |
| REQ-G2-004 C.ADDI16SP row equivalence | generated VHDL exhausts all 64 discontinuous-immediate encodings, rejects the reserved zero immediate, C.LUI, and C.ADDI neighbors |
| REQ-G2-003 C.LUI real MIR | the reserved one-input semantic intrinsic resolves only through the canonical strict contract and a concrete critical RV32/RV64 configuration |
| REQ-G2-004 C.LUI row equivalence | generated VHDL exhausts all 2,048 Q1/funct3=011 C.LUI encodings, rejects `rd=x0`, the `rd=x2` C.ADDI16SP overlap, zero `NZIMM`, and the C.ADDI neighbor |
| REQ-G2-003 predecode contract | selected RV32/RV64 critical products materialize fixed parcel/canonical/control widths; base profile and malformed direction/PA width reject before emission |
| REQ-G2-003/004 C.J redirect | implemented generated-VHDL scenario for a C.J positive offset, negative offset, and non-row fallthrough through typed `next_pc`/redirect ports; exact aggregate real-MIR admission is implemented, while row-level target evidence requires a self-hosted receipt |
| REQ-G2-003/004 control composition | one flattened RV32/RV64 C.J/C.BEQZ/C.BNEZ module target-simulates direct jump, both conditional branches, index mismatch, and unsupported-parcel fallthrough; this is a stateless control slice, not full Zca/frontend evidence |
| REQ-G2-011 normalized product partition | structural evidence counts 24 explicit common low-shamt selectors and 25 IDs in each XLEN-specialized closure; generated RV32/RV64 VHDL vectors distinguish C.JR `0x8082`, C.JALR `0x9082`, and non-trap C.EBREAK `0x9002`; overlap and reserved/default paths emit the illegal `PC+2` tuple; this is not complete-Zca evidence |
| REQ-G2-004 C.LI row equivalence | generated VHDL exhausts all 2,048 C.LI row encodings, checks canonical ADDI-with-x0 assembly, and rejects a non-row parcel |
| REQ-G2-005 | legacy bridge marker remains distinct from strict result test |
| NFR-G2-001..003,006 | repeat render, negative mutation tests, and critical-profile lint checks; HWIR ports carry only typed width/type metadata while VHDL type serialization remains in the backend owner |
| NFR-G2-004 | the executable typed parcel-mask scenario constructs only `HwConstant`/`HwCombOp` operands before rendering; focused source-ownership lint remains the global no-raw-VHDL-fragment gate |
| NFR-G2-005 | the executable strict-RV32 scenario proves a Gen2 result cannot select legacy fallback; the focused route/source review remains the boundary check that V1 stays explicit |
| Real-MIR increment | `Bool and Bool -> Bool` graph, origin, wrong-op, non-hardware and clocked rejection tests |
| REQ-G2-003 C.LI real MIR | reserved one-input C.LI semantic intrinsic lowers only with exact argument/local/return/CFG shape; malformed intrinsic fails without fallback |
| REQ-G2-003 C.ADDI real MIR | reserved one-input C.ADDI/C.NOP semantic intrinsic lowers only with exact argument/local/return/CFG shape; a non-semantic return fails without fallback |
| REQ-G2-003 C.ADDI4SPN real MIR | reserved one-input C.ADDI4SPN semantic intrinsic selects only the typed shared row under a concrete critical RV32/RV64 configuration |
| REQ-G2-004 C.ADDI4SPN row equivalence | generated VHDL exhausts all 2,048 Q0/funct3=000 parcels, including reserved zero-immediate rejection |
| REQ-G2-003 C.LW real MIR | reserved one-input C.LW semantic intrinsic selects only the typed common row; malformed shapes reject without fallback |
| REQ-G2-004 C.LW row equivalence | generated VHDL exhausts all 2,048 Q0/funct3=010 C.LW parcels, checks canonical LW assembly, and rejects a non-row parcel |
| REQ-G2-003 C.SW real MIR | reserved one-input C.SW semantic intrinsic selects only the typed common row; malformed shapes reject without fallback |
| REQ-G2-004 C.SW row equivalence | generated VHDL exhausts all 2,048 Q0/funct3=110 C.SW parcels, checks split S-immediate assembly, and rejects a non-row parcel |
| REQ-G2-003 C.LWSP real MIR | reserved one-input C.LWSP semantic intrinsic selects only the typed stack-relative row; malformed shapes reject without fallback |
| REQ-G2-004 C.LWSP row equivalence | generated VHDL exhausts all 4,096 Q2/funct3=010 parcels, rejects reserved `rd=x0`, and checks canonical LW assembly |
| REQ-G2-003 C.SWSP real MIR | reserved one-input C.SWSP semantic intrinsic selects only the typed stack-relative row; malformed shapes reject without fallback |
| REQ-G2-004 C.SWSP row equivalence | generated VHDL exhausts all 2,048 Q2/funct3=110 parcels, checks canonical SW assembly, and rejects a non-row parcel |
| REQ-G2-003 C.SLLI low real MIR | reserved one-input semantic intrinsic selects only the typed five-bit shift row; malformed shapes reject without fallback |
| REQ-G2-004 C.SLLI low row equivalence | generated VHDL exhausts all 1,024 `bit12=0` parcels, checks canonical SLLI assembly, and rejects a high-shamt parcel |
| REQ-G2-003 C.SRLI low real MIR | reserved one-input semantic intrinsic selects only the typed five-bit shift row; malformed shapes reject without fallback |
| REQ-G2-004 C.SRLI low row equivalence | generated VHDL exhausts all 256 Q1/mode-00/`bit12=0` parcels, checks canonical SRLI assembly, and rejects C.SRAI and high-shamt parcels |
| REQ-G2-003 C.SRAI low real MIR | reserved one-input semantic intrinsic selects only the typed five-bit arithmetic-shift row; malformed shapes reject without fallback |
| REQ-G2-004 C.SRAI low row equivalence | generated VHDL exhausts all 256 Q1/mode-01/`bit12=0` parcels, checks canonical SRAI assembly, and rejects C.SRLI and high-shamt parcels |
| REQ-G2-003 C.ANDI real MIR | reserved one-input semantic intrinsic selects only the typed signed-immediate row; malformed shapes reject without fallback |
| REQ-G2-004 C.ANDI row equivalence | generated VHDL exhausts all 512 Q1/mode-10 compact-register/immediate parcels, checks sign extension, and rejects neighboring modes |
| REQ-G2-003 C.SUB real MIR | reserved one-input semantic intrinsic selects only the typed compact register-register row; malformed shapes reject without fallback |
| REQ-G2-004 C.SUB row equivalence | generated VHDL exhausts all 64 compact register pairs, checks canonical SUB assembly, and rejects C.XOR and C.SUBW forms |
| REQ-G2-003 C.XOR real MIR | reserved one-input semantic intrinsic selects the closed compact-R elaborator with a fixed XOR row; malformed shapes reject without fallback |
| REQ-G2-004 C.XOR row equivalence | generated VHDL exhausts all 64 compact register pairs, checks canonical XOR assembly, and rejects C.SUB/C.OR/high-bit forms |
| REQ-G2-003 C.OR real MIR | reserved one-input semantic intrinsic selects the closed compact-R elaborator with a fixed OR row; malformed shapes reject without fallback |
| REQ-G2-004 C.OR row equivalence | generated VHDL exhausts all 64 compact register pairs, checks canonical OR assembly, and rejects C.XOR/C.AND/high-bit forms |
| REQ-G2-003 C.AND real MIR | reserved one-input semantic intrinsic selects the closed compact-R elaborator with a fixed AND row; malformed shapes reject without fallback |
| REQ-G2-004 C.AND row equivalence | generated VHDL exhausts all 64 compact register pairs, checks canonical AND assembly, and rejects C.OR/C.SUB/high-bit forms |
| REQ-G2-003 C.JR real MIR | reserved one-input semantic intrinsic selects only the typed Q2 control-transfer row; malformed shapes reject without fallback |
| REQ-G2-004 C.JR row equivalence | generated VHDL exhausts all 32 `rs1` fields, checks canonical JALR assembly, and rejects reserved `rd=x0`, C.MV, and C.JALR parcels |
| REQ-G2-003 C.MV real MIR | reserved one-input semantic intrinsic selects only the typed Q2 register-transfer row; malformed shapes reject without fallback |
| REQ-G2-004 C.MV row equivalence | generated VHDL exhausts 992 nonzero-`rs2` register combinations, checks the `rd=x0` hint normalization, and rejects C.JR, reserved, and C.ADD parcels |
| REQ-G2-003 C.JALR real MIR | reserved one-input semantic intrinsic selects only the typed Q2 return-link control row; malformed shapes reject without fallback |
| REQ-G2-004 C.JALR row equivalence | generated VHDL exhausts all 32 `rs1` fields, checks canonical `JALR x1`, and rejects reserved `rd=x0`, C.JR, C.MV, and C.ADD parcels |
| REQ-G2-003 C.ADD real MIR | reserved one-input semantic intrinsic selects a typed Q2 add row; RV32/RV64 hint policy is elaborated before strict RTL emission |
| REQ-G2-004 C.ADD row equivalence | generated VHDL exhausts 992 nonzero-`rs2` field combinations for both products, checks their deliberate x0-hint canonicalization difference, and rejects C.JALR/C.MV parcels |
| Critical driver increment | typed policy snapshot, explicit `rv32`/`rv64` target, strict route header/manifest fields, and no direct-builder fallback on rejection |
| Critical CLI route | real `@hardware` source under critical policy and explicit RV32 target emits `hwir-strict` VHDL provenance |
| Critical CLI rejection | unsupported `@hardware` XOR under critical policy fails with no VHDL or manifest sidecar, proving no legacy fallback |
| Critical target policy gate | noncritical `--riscv-gen2-target` rejects before stale-artifact removal and cannot silently select legacy VHDL |
| REQ-G2-009 compiler product route | source-less critical migrating-Zca product emits VHDL plus `hwir-gen2-product` manifest with its own compiler-product identity and an empty user source closure; source-plus-product parsing is mutually exclusive, and noncritical, wrong-target, requested-AOP, or woven-AOP admission failures preserve the complete prior VHDL/map/manifest bundle |
| REQ-G2-010 stateful parcel frontend | RV32/RV64 public APIs and the v2 trap CLI product emit only from `HwSequentialPlan`; require a recomputed closure over complete config, ports, ordered plan, decoder identity/digest, and origins, plus protocol scenarios and GHDL evidence |
| REQ-G2-009/010 target-specific provenance | `test/03_system/app/hardware/feature/riscv_gen2_product_provenance_spec.spl` renders the closed RV32 C.JAL and RV64 C.ADDIW v3 products and proves each emitted payload contains only its concrete critical profile and decoder closure. It is compiler provenance evidence only; self-hosted RV32/RV64 VHDL/GHDL receipts remain required. |
| REQ-G2-010 retirement receipt contract | `test/01_unit/compiler/50.mir/hwir_retirement_composition_spec.spl` proves the closed RV32/RV64 reset, dispatch, and receipt tuple; it rejects reset/width drift, rewired bindings, and a substituted child route before composition. This is elaboration-boundary evidence only: it neither emits a child nor proves architectural retirement. Its generated manual remains a self-hosted-docgen gate. |
| A13 / REQ-G2-004 mixed sequential datapath | `test/01_unit/compiler/50.mir/hwir_mixed_sequential_datapath_spec.spl` constructs typed add/truncate/sign-extension/compare/select/unsigned-predicate/bit-extract/fixed-slice HWIR, checks declaration/datapath/process order, and rejects unsupported, unreadable, wrong-destination, resize-direction, and multiple-driver shapes. Current assertions inspect emitted source; admitted self-hosted execution and GHDL cycle behavior remain required. |
| A13 / NFR-G2-001/003/011 structural and LSU closure | The mixed sequential spec mutates typed constants and checks graph-receipt drift, validates bit-vector material, and checks explicit compatible/incompatible LSU bus/mask geometry. Qualification additionally requires hash-drift coverage across every datapath collection and at least 80% measured branch coverage. |
| Stateful protocol recovery | The foundation scenario must contain RV32/RV64 vectors for two clean consecutive transactions with incrementing lineage, issued-entry backpressure, early/stale/repeated retirement, and independent same-lineage parcel/canonical/length mismatches. Each mismatch must assert sticky fault, refuse fetch, suppress stale effects, and recover only through synchronous reset including reset/retire priority. Bootstrap-seed execution is diagnostic and cannot qualify this receipt; qualification requires the admitted self-hosted runtime and recorded GHDL result. |
| REQ-G2-011 normalized outcome | C.ADDI4SPN target RTL proves reserved zero immediate remains explicitly illegal while a nonzero encoding produces legal canonical output; C.LW/C.SW prove classifier match/nonmatch, and C.LWSP proves reserved-register rejection, without a canonical sentinel |
| REQ-G2-011 migrating predecode | RV32/RV64 strict-HWIR shape preserves a single driver per public output; GHDL proves C.LW, positive C.ADDI16SP, C.JR/C.JALR aligned redirects, index-mismatch rejection, and reserved-zero C.ADDI16SP illegal fallthrough; the one-entry product selects this migrating decoder |
| Critical compressed product selection | CLI/driver accept explicit `rv32-zca-critical`/`rv64-zca-critical` and resolve only their concrete common-critical `CoreConfig` |
| Shared compressed seed | common integer Zca rows, text-free hardware payload, and RV32/RV64 adapter vectors |
| Mission-critical compressed subset | no fallback/config/text path; unsupported divergent rows reject; exhaustive 65,536-parcel deterministic classification |
| Critical capability truth | partial subset manifest records exhaustive classification as verified, cannot advertise Zca, and remains non-release-claimable even when future target-RTL evidence arrives |
| NFR-G2-008 origin/profile admission | any `zca.*` HWIR origin under a non-critical product profile fails before VHDL emission |
| NFR-G2-007 fixed-width compressed boundary | unit checks distinguish zero, reserved, and width-divergent reason codes without text-valued hardware payloads |
| NFR-G2-009 capability honesty | unit and manifest checks forbid full-Zca advertisement while generated-RTL equivalence remains incomplete |

Mutants: invalid XLEN, zero width, non-hardware tag, empty node ID, unknown
operation, missing operand, and an attempted legacy-fallback marker in strict
output. Each must fail its corresponding check.

## Current-host evidence and resume

The deployed `bin/simple` identifies as a Rust bootstrap seed. Focused test and
lint runs are diagnostic only, and its command surface lacks `duplicate-check`
and `sspec-maintain`. Do not claim this slice verified until a current
self-hosted CLI reruns the commands recorded in
`.spipe/riscv_gen2_hwir_foundation/state.md`.

## Qualification receipt-retention policy

No Gen2 qualification receipt is retained today. The planned qualification
writer is the provenance-admitted self-hosted CLI, after it executes the RV32
and RV64 generated-VHDL/GHDL routes. It must write one immutable run directory
under `build/evidence/riscv_gen2_hwir_foundation/<run-id>/`, headed by
`qualification_receipt.json`, with the exact CLI path/SHA-256, revision,
command lines and exits, generated-VHDL hashes, GHDL analyze/elaborate/run
logs, and the source/config/graph identities for both products. The receipt
must fail closed if any identity, log, or RV32/RV64 row is absent.

This is a tracked retention policy, not an artifact: this lane creates no
`build/` files and does not call a seed run, a scenario result, or a manually
edited document a receipt. Until that self-hosted writer exists and completes a
run, manuals must say “planned qualification receipt”, never “retained
receipt”.

## Critical-profile boundary

The production VHDL driver now snapshots a typed assurance policy and selects
the strict route for critical hardware designs. The current focused evidence is
unit/source-level plus a diagnostic seed probe; a current self-hosted CLI must
still run the direct `simple-vhdl` critical RV32/RV64 success cases and prove
that an unsupported full RV32 core leaves no VHDL or sidecars.

The compressed seed's RV32/RV64 adapter tests prove the shared rows in the
interpreter. A later target-RTL route must prove its `CompressedHardwareExpansion`
lowers as fixed-width hardware; host-facing `CompressedExpansion` text fields
are intentionally excluded from the adapter interface.

The qualified GHDL scenario is specified to prove that the typed emitter
produces valid VHDL-2008 for its supported Bool-AND seed. Until its
self-hosted receipt exists, it does not prove that the compressed decoder
lowers through HWIR.

The C.ADDI row scenario imports the standard SPipe surface and defines its
GHDL vectors. Rerun it with a current self-hosted runtime before recording the
result as release evidence; do not substitute the legacy textual decoder's
interpreter vectors.

The bootstrap capture-based SFFI wrapper misreports the GHDL helper result.
The scenario therefore specifies the repository's established tuple-return
process façade for the exact VHDL-2008 analyze, elaborate, and simulation
steps. A qualified self-hosted receipt must demonstrate those steps; fix the
generic wrapper only in its owning test-runtime lane.

The C.EBREAK target scenario and C.ADDI4SPN/C.LW/C.SW/C.LWSP/C.SWSP/C.SLLI-low/C.SRLI-low/C.SRAI-low/C.ANDI/C.SUB/C.XOR/C.OR/C.AND/C.JR/C.MV/C.JALR/C.ADD/C.ADDI/C.NOP/C.LI row
target-equivalence simulations invoke their compiler-owned row constructors.
They are implemented row-level proof scenarios awaiting self-hosted execution,
not replacements for target equivalence
for the remaining
critical-Zca rows or the full compressed frontend.

The capability manifest reports twenty-five row-level target-proven entries—C.EBREAK,
C.ADDI4SPN, C.LW, C.SW, C.LWSP, C.SWSP, C.SLLI-low, C.SRLI-low, C.SRAI-low, C.ANDI, C.SUB, C.XOR, C.OR, C.AND, C.JR, C.MV, C.JALR, C.ADD, the C.ADDI/C.NOP row,
and C.LI, plus C.ADDI16SP, C.LUI, C.J, C.BEQZ, and C.BNEZ—while retaining
`target_rtl_equivalence_verified=false` for the incomplete 25-entry subset.

`row_target_evidence_complete=true` may be set only by the self-hosted evidence
writer after every selected row has an individual receipt. It does not replace
composed frontend equivalence, which remains false pending one
parcel/operand/redirect/retirement target path. It is not established by the
implemented scenario catalog or bootstrap-seed activity.

The host-side `hwir_zca_target_trap_exhaustive_oracle_spec` now executes the
actual prepared RV32 C.JAL and RV64 C.ADDIW target-trap HWIR graphs for every
16-bit parcel, checking tuple determinism, the legal/illegal/trap partition,
and the sole C.EBREAK trap. This closes the composition-oracle design gap but
is not an independent generated-RTL/retirement equivalence receipt.

The 24 non-terminal strict-HWIR rows are resolved from a single
`RiscvZcaStrictContract` catalog shared by compiler lowering and target-evidence
metadata. Unit evidence verifies catalog identity and evidence provenance; target
advertisement is the explicit proof allowlist, so a lowerable catalog row has no
target-evidence entry until its generated VHDL proof completes. Unknown intrinsic
names and unproven subset rows have no strict contract.

The conditional-branch prerequisite is separately tested as
`HwBranchPredecodeInterface`: RV32 and RV64 must each expose an exact
`rs1_index: Bits[5]`/`rs1_value: Bits[XLEN]` read pair while retaining the
concrete PA widths of every predecode PC field. C.BEQZ/C.BNEZ now have
generated-VHDL proof for RV32 and RV64 taken/not-taken, `+2`, `-2`,
sign-sensitive `-256`, cross-row paths, and a mismatched-index fail-closed
case; their explicit target-proof entries remain row-level evidence only.

The frontend-handoff unit lane verifies RV32/RV64 concrete 12-port shape,
parcel/canonical/length/legal/PA lineage, and strict dispatch/retire ownership
ports. The required future system target scenario must additionally prove a
single Gen2 composition's parcel-buffer, branch-read binding, redirect,
canonical dispatch, and retirement propagation; the contract test does not
substitute for that evidence.

`riscv_zca_mission_critical_expand_hardware` is a distinct subset boundary:
unsupported rows—including RV32 C.JAL/RV64 C.ADDIW ambiguity—are illegal and
cannot invoke legacy decode. Its 65,536-parcel deterministic classifier is
verified, but the product remains unable to advertise Zca or claim release
readiness until target-RTL equivalence (and eventual full-table closure) exists.
## C.EBREAK v2 evidence

The system specification defines the stateless C.EBREAK row and the v2
single-outstanding trap product from the typed sequential plan, with a
versioned length-prefixed closure hash and per-state-node 64-bit transaction
lineage. Its RV32/RV64 GHDL vectors exercise two clean consecutive
transactions, issued-entry backpressure, mismatched retirement, sticky fault
containment, fetch refusal, stale-effect suppression, and synchronous reset
recovery/retirement priority when the self-hosted route executes them. The current runtime cannot
qualify that scenario: the deployed command is the bootstrap seed, not the
required self-hosted compiler. Qualification also requires a reset-coupled
retirement producer. This remains
bounded frontend evidence and does not claim protected-core integration, a full
trap controller, or Zca closure.
