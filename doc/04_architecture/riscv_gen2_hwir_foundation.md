<!-- codex-design -->
# RISC-V Gen2 HWIR Foundation Architecture

## Boundary

`CoreConfig -> strict lowering -> typed HwModule -> strict VHDL emitter` is the
only Gen2 route in this slice. The existing direct/text generator remains a
separate `legacy` route. The strict route cannot return its fallback type.

## Schema v1

`HwNodeId` is a deterministic text identity derived from module name and local
role. `HwOrigin` retains the source semantic name. `HwPort` has direction and a
concrete positive width. `HwCombOp` has an allowed opcode and references
declared values. `HwModule` owns concrete ports, operations, origin records and
the selected `CoreConfig`. `CoreConfig` records XLEN, physical address width,
register count and profile; it validates before lowering.

`lower_strict_mir_function_to_hwir` is the real extraction entry. It accepts
hardware-tagged, non-generic, unclocked fixed-width combinational MIR, plus a
closed table of declared Zca semantic intrinsics. Generic operations support
`and`, `or`, bounded shifts, constants, and direct return wiring; approved Zca
intrinsics are shape-checked then mapped to existing typed row constructors.
The four-block terminal C.EBREAK/C.ADDI form is recognized structurally, never
by function name. Unsupported MIR produces a stable `HWIR-E-*` diagnostic.
The synthetic summary lowerer remains a fixture API and is not evidence of
MIR lowering.

## Invariants

1. XLEN is 32 or 64; no runtime selector is introduced.
2. Every module/port/operation ID is non-empty and unique by construction.
3. Port and operation widths are positive and concrete.
4. Strict lowering rejects non-hardware inputs and malformed configuration.
5. Strict emission rejects invalid modules and unsupported operations before
   creating text.
6. Strict combinational operations are an explicit finite whitelist. Results
   must be writable signal/output values; operands must be readable values,
   widths must match the serializer contract, cycles and multiple drivers are
   rejected, and constants must fit their declared width.
7. The helper does not consult dynamic capability or environment state.
   `CompileContext` snapshots the sanctioned typed assurance policy once at
   construction. At the production `compile_to_vhdl` convergence point,
   critical hardware products require an explicit `riscv_gen2_target` of
   `rv32` or `rv64`, select strict real-MIR HWIR lowering, and fail before the
   direct VHDL serializer is reachable. Other profiles retain the legacy path.
8. Strict VHDL contains stable route evidence and its production manifest
   records `generation_route`, HWIR module node ID, concrete configuration,
   and the SHA-256 of a versioned, length-prefixed canonical typed
   combinational graph serialization.

The next schema revision introduces registers, memories, channels, clock/reset
domains, effects, aspect plans, and declarative ISA entries without changing
the strict-result/diagnostic boundary.

The current foundation now materializes the first strict schema in
`compiler.mir.hwir.types`: concrete `CoreConfig`, stable `HwNodeId`/`HwOrigin`,
typed constants/comparisons/muxes, state-register metadata, and `HwModuleDef`.
`shape_diagnostic()` fails closed on invalid product configuration, count drift,
missing/duplicate clock domains, unknown values, width-incompatible compares or
muxes, duplicate drivers, and undriven outputs. These are elaboration records,
not a runtime XLEN or provider-selection mechanism.

All strict-emitter profile labels use a bounded identifier grammar, and HWIR
names reject VHDL reserved words before serialization. This prevents free-form
configuration or graph metadata from becoming a VHDL-text injection path.

For the bounded stateful frontend, the versioned length-prefixed canonical graph
closure includes each
register, ordered rule, decoder pin, output binding, and every output guard.
Ready/valid, fault, redirect, and trap visibility conditions are functional
logic; a manifest hash must change if any of them changes.

Compiler-owned Gen2 manifests retain the concrete bit width of every port and
are checked against the elaborated HWIR port sequence. Entity identity, port
order, direction, type, and width must all match; an artifact cannot attest to
an interface that differs from its fixed compiler product.

The shared RV32/RV64 `RiscvRetireRecord` is the architectural retirement
boundary for Gen2 migration. It retains original versus canonical instruction
bits, instruction length, privilege, architectural writeback and memory effects,
and trap/interrupt context. A two-byte retirement must retain a 16-bit original
parcel; non-trapping records must carry a canonical 32-bit instruction.

The initial aspect transformer is intentionally narrower than the manifest
language: it realizes only a transparent, state-free observational attachment
at the RTL `module.port` join point. Any other stage or semantic selector is a
hard error until an explicit typed graph transform is implemented for it.

Before a real MIR function may select a specialized strict-HWIR row, an
admission preflight validates the closed typed graph: non-variadic signature,
one exact typed argument local per parameter, unique and resolvable locals,
instruction/return type preservation, Boolean comparisons and branch
conditions, and declared CFG targets. Invalid source MIR therefore fails with a
stable `HWIR-E-MIR-*` diagnostic before row extraction; it cannot be repaired
implicitly by replacing malformed source types with a known HWIR template.

## Frozen next interface: compressed predecode/redirect

Before any control-flow compressed row is claimable, freeze a typed record with
`original_parcel: Bits[16]`, `original_length_bytes: UInt[2]`,
`canonical_instruction: Bits[32]`, `legal: Bool`, `fetch_pc: Addr[PA_BITS]`,
`next_pc: Addr[PA_BITS]`, `redirect_valid: Bool`, and
`redirect_target: Addr[PA_BITS]`. Non-control rows set `redirect_valid=false`
and `next_pc=fetch_pc+2`; redirect rows must prove their target and preserve
the original parcel for traps/debug. It is elaboration-typed, never a
text-level VHDL convention or runtime XLEN/provider lookup.

The frozen schema is now materialized by
`compiler.mir.hwir.predecode.HwPredecodeInterface`. Its closed constructor
accepts only the `zca-common-critical` product profile and emits concrete
`HwPort` widths: 16 for the parcel, 32 for the canonical instruction, 2 for
length, 1 for each flag, and the selected physical-address width for all three
PC fields. It deliberately adds no inferred control behavior; the first C.J,
C.BEQZ, or C.BNEZ graph must consume this contract and prove both `next_pc` and
redirect outputs.

`strict_zca_cj_predecode_row_hwir` is the first consumer and has bounded
generated-VHDL simulation evidence for forward, backward, and non-row paths.
Its exact aggregate real-MIR semantic admission shape is also fail-closed and
tested, so it is eligible for row-level target capability advertisement; this
does not imply full-Zca or release closure.

## Frozen next interface: conditional compressed branches

`HwBranchPredecodeInterface` extends the predecode contract with an explicit
`rs1_index: Bits[5]`/`rs1_value: Bits[XLEN]` architectural read pair. C.BEQZ/
C.BNEZ must resolve their condition only after proving the decoded prime
register matches `rs1_index`; no decoder-side provider lookup is allowed.
The shared predecode fields retain PA-width fetch/redirect addresses. This
separates parcel decoding from architectural register-value dependency and
prevents an unconditional C.J model from being misapplied to conditional rows.

`strict_zca_cbeqz_predecode_row_hwir` and
`strict_zca_cbnez_predecode_row_hwir` now consume this interface. They match
only their own parcel tag, reconstruct the CB immediate, assemble a canonical
BEQ/BNE with the decoded prime register, and assert redirect only from the
explicit zero/nonzero operand condition and fail closed on a binding mismatch.
They are constructors, not semantic target claims: each has an exact four-input
aggregate strict-MIR intrinsic contract (`Bits[16]`, `Bits[PA]`, `Bits[5]`,
`Bits[XLEN]` to the six-field predecode result). Generated-VHDL simulation now
proves RV32/RV64 taken/not-taken, `+2`,
`-2`, sign-sensitive `-256`, and non-row behavior, so both have row-level
target-proof entries without implying full-Zca or release closure.

## First emitted control composition

`strict_zca_control_predecode_hwir` alpha-renames and flattens the existing
C.J/C.BEQZ/C.BNEZ typed graphs into one deterministic, combinational
`HwModuleDef`. It shares only the frozen `{original_parcel, fetch_pc,
rs1_index, rs1_value}` inputs and has one owner for each public predecode
output. The fallback is fixed: illegal canonical instruction, two-byte length
and fallthrough, no redirect, and `fetch_pc` as redirect target. It is a
length-predecoded control slice—not an instruction parcel queue, a full Zca
composition, or an architectural dispatch/retirement implementation.

The critical VHDL driver snapshots one typed assurance policy in
`CompileContext`. A hardware source under the `critical` policy must provide
`--riscv-gen2-target rv32|rv64`; that route resolves `CoreConfig`, lowers one
real MIR hardware function through strict HWIR, and records the node/config in
the VHDL provenance. A strict lower/emitter failure returns `HWIR-E-*` before
artifact cleanup, so it cannot silently select the legacy catalog compiler.
The legacy catalog route remains available only when no Gen2 target was
requested and the policy does not require strict hardware emission.

## Compiler-owned product route

`riscv-gen2-zca-control-predecode-v1` remains a source-less, compiler-owned
three-row control product. `riscv-gen2-zca-migrating-predecode-v1` is the
separate source-less product for the admitted normalized-row composition. Both
accept only the critical `rv32-zca-critical` or `rv64-zca-critical`
configuration, perform all policy/configuration/AOP checks before cleanup, and
call their strict typed emitters directly. Each artifact
has `generation_route=hwir-gen2-product`, an empty *user* source closure and a
`compiler_product_entity` source-map item with no source location. That is an
honest provenance boundary: it is not a synthetic Simple module and cannot
fall through to the source-driven legacy VHDL catalog. Both remain explicitly
unqualified and neither claims full Zca; the migrating product is only the
admitted row tranche. Its typed composition also accumulates row legality and
overlap: if more than one classifier ever matches, it emits the explicit
illegal/fall-through tuple (zero canonical word, `legal=0`, no redirect,
`PC+2`) rather than silently selecting by mux order.
The tranche contains 24 common low-shamt ISA IDs. RV32 C.JAL and RV64 C.ADDIW
are each appended only by their concrete product, yielding separate 25-ID
closures. These numbers are coverage boundaries, not complete-Zca claims;
high-shamt/XLEN-dependent rows and C.EBREAK trap composition remain distinct.
The 24 common selectors are independent—including C.J, C.BEQZ and C.BNEZ—so
no aggregate control selector can hide a classifier collision.

The stateful/trap product is a separate compiler-owned
route: it is admitted only when its typed sequential plan supplies a concrete
module node, profile, and 64-character frontend-plus-decoder closure hash.
The common artifact validator applies those same graph-binding requirements to
stateful routes; an empty source closure never bypasses provenance validation.

## First typed sequential Gen2 boundary

The standalone sequential boundary also owns an optional typed combinational
datapath. `HwSequentialModuleDef` carries signals, integer and bit-vector
constants, combinational operations, comparisons, selects, bit extracts, and
fixed slices beside its `HwSequentialPlan`. Validation resolves input,
register, child-output, signal, and constant widths, rejects public outputs as
readable sources, and requires exactly one driver for every datapath signal.
The VHDL backend serializes only that validated IR before output equations and
the clocked process; callers cannot inject raw VHDL. The module structural hash
commits the complete datapath and uses the versioned v3 schema so old
state-only receipts cannot alias mixed combinational/sequential products.

`HwParcelFrontendInterface` and `HwParcelFrontendDef` freeze the intended
clocked Gen2 contract without making the whole generic HWIR falsely appear
complete. The intended fixed product has one synchronous active-high reset domain and
exactly one outstanding fetched parcel. It captures parcel, PC, decoded-read
index/value and a 64-bit monotonically incrementing transaction lineage; it exposes the typed migrating
predecode result only from captured state. Dispatch stalls preserve that payload.
After dispatch, only one retirement whose 64-bit lineage, original 16-bit
parcel, canonical 32-bit instruction, and two-bit original-length encoding all
match the outstanding entry makes that entry available. An early, stale,
repeated, or identity-mismatched retirement asserts a sticky `protocol_fault`
until reset. The decoder remains an instance of the typed migrating-predecode
module, so no second legacy/core decoder or textual semantic copy is created.
The upstream retire producer must be reset-coupled: it may not present a
retirement from a pre-reset transaction after this frontend reset. The 64-bit
lineage is a bounded counter, not an unbounded proof token. A matching
retirement at the terminal value enters the sticky fault state without
incrementing, so the counter cannot wrap and no lineage value can be reused
before reset.
Its name is an explicit safety boundary: C.EBREAK remains illegal rather than
becoming an accidental full-Zca claim. `HwSequentialPlan` now owns the typed
register declarations, reset values, priority rules, guards, assignments,
decoder pins, and output bindings. The VHDL serializer consumes that plan and
records a structural closure hash with the selected decoder graph; it no longer
contains the frontend's register names, widths, or transitions as a parallel
semantic implementation. Each plan owns a stable `HwNodeId` subtree, and the
serializer writes those IDs beside every state declaration, decoder output,
rule, and output equation. This creates deterministic HWIR-to-VHDL lineage
anchors for source-level waves and first-divergence reporting. Decoded parcel
metadata is guarded by the same internal state predicates as `dispatch_valid`.
After dispatch acceptance, protocol fault, or reset, architectural dispatch
outputs are deterministically zeroed. Retirement matching still consumes the
outstanding entry's lineage together with its captured original parcel and
decoder-derived canonical instruction and length. These four identity fields
form one conjunction: matching lineage alone is never sufficient. Internal sequential guards may reference only
inputs, registers, and decoder outputs—not another public output.

## Shared retirement boundary

`riscv_common.retire.RiscvRetireRecord` is the first shared architectural
commit contract for the migration. The RV32 and RV64 RVFI adapters project
their existing concrete snapshots into this one record with an explicit XLEN,
original/canonical instruction, instruction length, register writeback, memory
effects, trap/interrupt state, and PC transition. This is host/formal/debug
metadata rather than an XLEN-runtime hardware representation: each producer
selects its fixed width before constructing the record. It gives later unified
scalar, RVFI, trace, lockstep, and first-divergence work one precise retirement
surface without forcing a rewrite of legacy cores.

The concrete retire-chain theorem consumes this record directly. It rejects an
invalid valid-retire record or a mixed-RV32/RV64 trace before checking monotonic
retire order and PC chaining. A synchronous trap or interrupt is an explicit
control-transfer exception to ordinary PC chaining; non-retiring samples are
ignored and fewer than two retired instructions remains a fail-closed vacuous
result. This removes the parallel-array boundary from the shared migration lane
without treating one simulation trace as a proof of all executions.

## Scalar semantic database seed

`riscv_common.isa.scalar_database` begins the shared scalar database with
declarative I, M, and first RV64 word/shift rows. Each row carries a stable ID,
extension, exact encoding mask/value, XLEN applicability, semantic operation,
execution class, operand width, writeback rule, memory effect, and trap
behavior. The database validates malformed encodings and duplicate IDs, then
rejects encoding overlaps per concrete XLEN before a decoder generator can use
table order as semantics. It materializes separate RV32 and RV64
host/elaboration views. In particular,
RV32 and RV64 immediate shifts use separate masks because RV64 admits the
sixth shamt bit; word operations declare 32-bit operands and one
sign-extension-to-XLEN writeback rule.

`riscv_scalar_lookup(instruction, xlen)` is the first consumer-facing host
boundary: it selects a validated concrete view and returns either exactly one
declared entry or a stable invalid-XLEN/undeclared-instruction diagnostic. It
does not lower into a runtime selector or grant a first-row-wins ambiguity
rule; future decoder, assembler, disassembler, coverage, and provider work
must consume this same validated entry identity.

`RiscvScalarDecoderPlan` is the first concrete generation-facing consumer: it
freezes one profile's exact ordered rows, validates them against the declarative
source, hashes its canonical representation, and resolves an instruction only
within that concrete table. It is a compiler-host plan for future decoder,
disassembler and coverage lowering—not a runtime extension/XLEN selector or a
claim that an RTL scalar decoder already exists.

`riscv_scalar_entries_for_isa_profile` and `riscv_scalar_lookup_profile` add
the corresponding extension gate. An `rv32i` product cannot resolve an M-row,
while an explicit `rv32im` product can. `rv32i_zmmul`/`rv64i_zmmul` derive
the four common multiply rows (and RV64 `MULW`) from that same M table, so divider/remainder
operations remain illegal without duplicating scalar semantics; Zca profile suffixes do not duplicate
scalar rows because compressed metadata remains separately owned. Likewise,
bare I/IM/Zmmul profiles do not silently include `Zicsr` or `Zifencei`; the
explicit `rv32i_zicsr_zifencei` and `rv64i_zicsr_zifencei` profile names are
the currently supported scalar metadata combinations that select those rows.
Provider
selection now has its first elaboration owner:
`riscv_scalar_elaborate_provider(isa_profile, muldiv_provider)` returns one
concrete `RiscvScalarProviderSelection`. Base-I profiles require `none`; IM
and Zmmul profiles require exactly one of `iterative`, `pipelined`, or `dsp`.
The result
retains the exact validated table and resolves every M row to that one provider
identity; provider lookup rejects a lookalike entry that is not structurally
owned by the selected table. Selection validation also compares the complete
declarative row at every table position—not merely its ID—before it can reach
binding planning. It is compiler-host metadata for later HWIR
resource binding, not a string checked on a datapath or a runtime provider
lookup. `HwirRiscvScalarBindingPlan` is the next typed boundary: it maps each
selected multiply/divide ISA-entry identity to an area/balanced/speed target
binding. Base-I plans are empty, Zmmul has multiply bindings only, and full M
has multiply plus divide/remainder bindings. It does not yet materialize
resource instances or latency-changing RTL. The Gen2 scalar plan records every
binding with `latency_contract=uncommitted` and `latency_cycles=-1`; the generic
optimizer's estimated latency is deliberately not admissible as a critical
product timing contract.

`RiscvGen2ScalarElaboration` is the compiler-host aggregate of one concrete
`CoreConfig`, its exact `RiscvScalarDecoderPlan`, and its validated provider
selection. It rejects an XLEN or ISA-profile disagreement across those three
objects and gives RV32 and RV64 separate stable product identities before HWIR
lowering. Its identity includes profile, XLEN, PA width, and register count, so
two valid concrete configurations cannot alias provenance merely by sharing a
profile label. It is deliberately an elaboration descriptor—not an RTL core, a
runtime extension selector, or evidence of scalar execution completion.

`RiscvGen2ScalarDispatchPlan` is the next compiler-host boundary. Given an
already elaborated product and one 32-bit instruction, it resolves exactly one
row from that product's frozen decoder table and binds the row to the already
selected provider. A copied row ID with altered semantics fails the provider's
structural ownership check; an RV64-only row on an RV32 product fails before
HWIR lowering. This is a typed future execution-unit input, not a generated
decoder or a runtime instruction-dispatch mechanism.

`CoreConfig` accepts only the currently supported scalar profile identifiers
and verifies the RV32/RV64 prefix agrees with its concrete XLEN before any
strict HWIR construction. This is an early cross-layer boundary check, not a
second decoder or semantic database: it prevents a malformed product manifest
from claiming an RV64 ISA on RV32 hardware.

This remains a schema and semantic-source migration. It does not yet generate a
complete decoder/assembler/disassembler or claim a complete scalar ISA; those
consumers and additional provider families must derive their metadata from the
same table rather than reintroduce width-specific semantic copies.

The current RV64 table also carries ADDIW/ADDW/SUBW and all six W-shift forms
(`SLLIW`, `SRLIW`, `SRAIW`, `SLLW`, `SRLW`, `SRAW`) as 32-bit operations with
one `sign_extend_to_xlen` writeback rule. This is metadata coverage only; it
does not yet materialize an ALU provider or advertise a complete RV64I core.
The same RV64-only family declares `LD`, `LWU`, and `SD`: `LWU` has explicit
32-bit zero-extension while the doubleword forms remain XLEN-width.

The declarative common-Zca table and row evidence catalog are coverage inputs,
not a target-qualification receipt. Until the self-hosted compiler executes the
generated RV32/RV64 VHDL/GHDL scenarios, the emitted critical-subset manifest
keeps `row_target_evidence_complete=false` and cannot advertise target-proof
completion from static allowlist membership.

<!-- codex-architecture -->
## Typed hardware aspect boundary

`compiler.mir.hwir.aspects` is the Gen2 compile-time aspect contract. A
manifest has a stable ID/version/SHA-256, fixed stage, typed advice/effect and
latency contracts, frozen semantic join-point selectors, declared resource
counts, capability/conflict metadata, and required proof obligations. An
application names stable `HwNodeId`s rather than generated VHDL signals.

The effect class selects a minimum named proof obligation: observational →
`architectural_noninterference`, timing-transparent → `cycle_equivalence`,
timing-changing → `retirement_equivalence`, architectural →
`differential_isa`, fault-model → `fault_free_equivalence`, and provider
replacement → `interface_refinement`. A plan with another arbitrary proof label
does not validate as an implementation-ready aspect declaration.

The plan fails closed for malformed hashes, unsupported stages/advice/effects,
textual-VHDL advice, unknown semantic join points, conflicts, duplicate
applications, and any required aspect that does not weave a matched node. The
absent plan is structurally empty, so it cannot contribute ports, state, logic,
or weave metadata. The first pre-legalization transform is now implemented:
only an applied, transparent, state-free observational `observe` manifest can
add a declared typed output/pass-through probe to an existing readable HWIR
value. The woven graph gets a derived `HwOrigin`, recomputed structural digest,
and must pass normal HWIR shape validation before strict VHDL serialization.
The serializer receives the woven `HwModuleDef` directly and retains its normal
no-legacy-fallback result contract. For this module-level transform, every
application match must name that exact module and its declared weave count must
equal the number of materialized typed probes. An absent plan
with a probe, an unplanned/mismatched node, a resource-count mismatch, or any
other advice kind is rejected. Discovery/lockfiles, proof execution, target
metadata, and timing/state-changing transforms remain later work. Existing MIR
AOP and legacy debug-tap string hooks are not implementation paths for it.

`HwAspectLock` is the first reproducibility boundary for certified callers. It
contains exactly one ID/version/content-SHA-256 entry for every planned
manifest. `weave_hwir_observational_ports_locked` checks that lock before any
graph mutation; a missing, additional, version-mismatched, or hash-mismatched
entry is a stable error. Compiler-owned Gen2 VHDL artifact manifests now record
the aspect-lock SHA-256 and typed aspect identities under `hwir_aspects`; even
the current aspect-free products record the deterministic empty-lock digest.
Manifest serialization sorts typed aspect identities by ID, version, and hash,
so equivalent plans cannot perturb the generated provenance merely by caller
ordering. Artifact validation reconstructs the typed lock from those entries
and requires its SHA-256 to equal the manifest lock digest; a well-formed but
forged digest is a hard error.
It is an in-memory typed lock contract today; loading a checked-in lockfile
remains later compiler-host integration work.

## Normalized non-control row outcomes

The original 22 non-control Zca row graphs expose only a canonical instruction
and use zero internally as a reject sentinel. That is insufficient evidence of
legality for a mission-critical composed decoder. `zca_outcomes` therefore
normalizes each admitted row behind the frozen predecode interface: it preserves
the original row graph, derives explicit `legal` from the row’s classifier and
all reserved-encoding predicates, and emits fixed fallthrough/no-redirect
metadata. C.ADDI4SPN is the first reserved-gated outcome; its zero immediate
remains illegal by an explicit typed gate. Classifier-complete C.LW, C.SW,
C.SWSP, C.LI, C.ADDI/C.NOP, low-shamt shifts, C.ANDI, compact-R rows, C.MV,
and C.ADD now use this boundary. C.LWSP and C.LUI use its explicit
true-means-reserved predicate chain. C.ADDI16SP uses a separate positive
`rd=x2` eligibility gate followed by its nonzero-immediate reservation gate.
C.JR/C.JALR use a distinct predecode wrapper: it binds the decoded `rs1` to
the typed register-read pair, clears the JALR target low bit and only then
redirects. C.EBREAK has a separate v2 trap contract and remains outside the
unchanged v1 migrating decoder; canonical-zero
inference is prohibited.

## Trap-effect extension (v2)

`HwTrapPredecodeInterface` is a versioned extension of the frozen v1 branch
predecode contract. It adds only explicit outputs: `trap_valid`, XLEN-wide
`trap_cause`, and XLEN-wide `trap_tval`. C.EBREAK (`0x9002`) is legal in this
contract, emits canonical `EBREAK`, requests breakpoint cause 3, and sets
`tval` to zero. A nonmatch emits no trap.

`HwTrapParcelFrontendDef` is an implemented development-stage stateful
consumer, not a release-qualified processor frontend. It captures the parcel
and register-read binding once, derives all trap signals from that captured
state, and has one dispatch/retirement owner. The v2 product gates
`trap_valid` with the same internal active-dispatch predicates and drives
cause/tval to zero outside that active transaction, so an accepted C.EBREAK
cannot leak a stale trap effect
while the frontend waits for retirement. Its source-less manifest names both
the compiler product entity and its decoder dependency; it never fabricates a
user source span. Its v2 product is enabled only through the typed sequential
plan and a nonempty graph closure hash. The frozen v1 decoder composition still
classifies C.EBREAK as unmigrated. This is not an ABI-stability claim for the
stateful frontend: adding parcel/canonical/length retirement identity inputs
changes its public port sequence and therefore its closure hash. Existing
stateful product IDs must remain unqualified until their version/ABI treatment
is explicit and the self-hosted qualification writer creates fresh manifests
and GHDL receipts. No such qualification receipt is retained at present.

`HwParcelRetirementComposition` freezes the next architectural boundary without
pretending that it already emits a processor. Its producer contract consumes
the accepted dispatch identity `(valid, lineage, original parcel, canonical
instruction, original length)`, shares the frontend's `clk` and synchronous
`rst`, and returns the same identity with the retirement receipt. The closed
wiring list rejects width changes, reset separation, and receipt rewiring at
elaboration. It is not target-legalized because strict HWIR has no generic
typed child-instance/effect lowering yet. RTL composition therefore remains a
later scalar-retirement owner task, not evidence supplied by this contract.
The current `HwirStrictVhdlResult` is mutable metadata plus emitted text, so it
is deliberately not accepted as a composition-child authority: comment markers
and port text are not a sealed proof of child behavior. The composition emitter
must fail closed until a typed architectural producer can provide an opaque
verified emission receipt and generated RTL/GHDL evidence.

The v1 and v2 compositions also publish their admitted declarative ISA IDs.
The contract test requires v1 to contain exactly the 24 non-trap entries and
v2 to contain each of the 25 `zca-common-integer-v1` entries exactly once. This
is an admission-closure guard against ISA-table drift; it is not a replacement
for generated-RTL equivalence over all parcels.

The target-specific effectful closure is a separate architectural boundary.
It admits the 24 common rows, exactly one XLEN-specific row (RV32 C.JAL or RV64
C.ADDIW), and C.EBREAK. The target graph owns all direct/indirect redirect and
JR/JALR read binding; the outer effect layer owns only partition uniqueness and
trap selection. Cross-partition overlap fails closed and cannot produce a
redirect or stale trap metadata. Product identity and the child decoder digest
remain part of the stateful graph closure.

Compiler-owned Gen2 manifests distinguish the scalar ISA profile used during
elaboration from the hardware behavior actually emitted. Every current product
declares `implementation_scope: frontend-predecode-only`, an ordered allowlist
of its implemented compressed instruction IDs, and a canonical capability-set
SHA-256. Artifact validation reconstructs that exact list from the selected
typed product before writing any sidecar. Consequently, `rv32i` or `rv64i` in
the configuration is not evidence that the artifact implements an integer core,
CSR state, memory system, traps, or retirement; those claims remain absent until
their typed implementation and proof closure exist.

RV32 C.JAL is additionally isolated behind the concrete
`riscv-gen2-rv32-zca-cjal-critical`/`rv32i_zca` product profile. Its product
extends the shared migrating graph with the C.JAL row but never widens the
shared RV32/RV64 capability set: the same parcel encoding is RV64 C.ADDIW.
Selection occurs at elaboration and the emitted module contains no XLEN mux or
runtime extension lookup.

The reciprocal RV64 C.ADDIW row is isolated behind
`riscv-gen2-rv64-zca-addiw-critical`/`rv64i_zca`. It recognizes the same parcel
class only in that concrete product, reconstructs the signed six-bit immediate,
and rejects the reserved `rd=x0` form before canonical dispatch. Both products
remain separate `frontend-predecode-only` artifacts with independent capability
closures; neither widens the common RV32/RV64 product claim.

The single-outstanding parcel frontend resolves its decoder identity from the
same concrete product configuration. Therefore the RV32 C.JAL and RV64 C.ADDIW
frontends instantiate their respective specialized migrating decoders, and the
selected dependency is included in the sequential graph hash. This is still a
bounded retire-lineage frontend, not a scalar core or profile-compliance claim.

`strict_zca_cjal_rv32_predecode_row_hwir` is an intentionally isolated RV32
row. It shares the J-immediate/redirect graph with C.J but emits canonical JAL
with `rd=x1`, and rejects RV64 before elaboration because that parcel class is
RV64 C.ADDIW. It is not part of `zca-common-critical`, the v1/v2 admission
lists, or any product manifest.

## Critical integration status (2026-08-11 correction)

The strict serializer is now real source code: it validates a `HwModuleDef`,
emits only its finite typed operation set, records node/profile provenance, and
returns `HWIR-E-*` for unsupported graphs. It does not invoke the legacy VHDL
builder. The one-entry product renderer likewise instantiates its typed decoder
and retains explicit protocol-fault behavior.

Stateful artifact provenance binds the complete concrete configuration, public
port contract, ordered sequential plan, decoder identity and digest, and
origins—not merely a route label or a hash-shaped string.

This must not be overstated. The self-hosted compiler executable is unavailable
in this checkout, so bootstrap-seed output does not establish artifact evidence.
Release qualification still requires self-hosted CLI plus GHDL evidence for the
strict source route. Until then this is development-stage source evidence only.

## Typed `commit.retire` observation boundary

The aspect engine can bind a locked Architecture-stage observational aspect to
the retirement composition's stable `commit.retire` node. Each attachment must
name an exact typed `retire_*` producer output and declare its width. The weaver
retains the composition and producer unchanged, adds no state or latency, and
derives an order-independent digest from the composition, lock, and attachment
set. An absent plan accepts no attachments and returns the original composition
with zero added ports. This is a pre-legalization contract, not RVFI or formal
noninterference qualification.

## Canonical parcel/trap sequential lowering (2026-08-14)

The fixed parcel and trap frontend contracts remain product validators and
typed port factories. After validation, emission constructs a child-bound
`HwSequentialModuleDef` with the fixed plan, selected decoder entity, and the
decoder's actual structural hash. The sole sequential serializer and graph
owner is `render_strict_sequential_hwir`; decoder VHDL is prepended exactly
once. The former stateful serializer/hash schema is not an alternate layer.

## Qualification evidence ownership

The POSIX runner owns only phase-one execution in a private staging directory:
admitted CLI checks, measured coverage, fixed product generation, testbench
binding, and isolated GHDL phases. The pure-Simple composer owns phase two. It
accepts an exact-key v2 manifest, rehashes and copies every command/artifact,
creates the previously absent final run, and writes the receipt last. Neither
component may infer PASS from source tokens, filenames, or a GHDL marker.
