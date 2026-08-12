# RISC-V Gen2 HWIR Foundation — Local Research

Date: 2026-08-11

## Finding

The current path is direct MIR-to-VHDL or a hardware-specific VHDL text
generator. `src/compiler/50.mir/hwir/types.spl` provides count-summary records;
`mir_to_hwir.spl` falls back for non-hardware input; and
`70.backend/backend/hwir_to_vhdl.spl` can preserve the legacy route or render
an empty smoke entity. No typed `CoreConfig`, strict route, concrete ports, or
source lineage contract exists. Existing `riscv_common/xlen.spl` supplies
RV32/RV64 constants, but is not an elaboration configuration boundary.

Reusable assets are the HWIR namespace, VHDL target/backend namespace,
`XlenConfig`, VHDL builder/templates, and optimizer-model package. The V1
textual generator remains a legacy evidence lane and must not be changed by
this foundation slice.

## First-slice decision

Build a deliberately small but real typed path: valid RV32/RV64 `CoreConfig`
selects a concrete hardware width; a strict lowering request validates it and
constructs one non-empty combinational pass-through/`and` module with stable
origin IDs; strict VHDL emission validates the module and renders ports and the
operation. Invalid configuration, non-hardware input, malformed module, or
unsupported operation returns a deterministic diagnostic. Strict routing never
returns the legacy fallback result.

The strict bridge is now selected at the production VHDL convergence point for
critical hardware designs. `CompileContext` snapshots the typed assurance
policy once; an explicit `riscv_gen2_target` selects RV32/RV64; unsupported
MIR fails before the direct VHDL builder; and the artifact records its strict
route, node ID, and configuration. Supported real-MIR shapes are deliberately
closed: primitive Boolean/`u32` datapaths, audited terminal parcels, and the
two compiler-reserved Zca semantic intrinsics described below.

The first shared compressed-ISA boundary is also present at
`riscv_common/isa/compressed/zca_seed.spl`. It owns common integer Zca parcel
classification, two-byte length, C.EBREAK, C.NOP/C.ADDI, C.ADDI4SPN, C.LW/SW,
C.LI, C.ADDI16SP/C.LUI, low-shamt shifts, logical/register forms, branches,
LWSP/SWSP and indirect-control forms. Its fixed-width
`CompressedHardwareExpansion` is now spliced into both legacy RV32/RV64
adapters. RV32's normal integer adapter has migrated completely to the shared
RV32 specialization, so it retains neither a copied instruction encoder nor a
legacy decoder fallback. RV64 now likewise selects a shared RV64 specialization
for its integer C tail (LD/SD, ADDIW, word operations and six-bit shifts),
while unsupported floating-point forms fail closed. Host metadata carries
diagnostic text and XLEN-specific
classification separately, so no runtime XLEN selector or text layout enters
`@hardware` calls. The shared synthesizable bit assembly uses only `u32`
two's-complement intermediates; signed host-width immediate values are not
part of the RTL path. Both RV32 and RV64 normal adapter entrypoints are now
explicit `@hardware` functions, providing an unambiguous typed lowering
boundary. `riscv_zca_mission_critical_expand_hardware` is the
separate fail-closed critical-subset boundary: it never falls back to either
legacy decoder. It is not an assertion of full C/Zca certification.

The declarative ISA table is now `riscv_common/isa/isa_database.spl`. It lists
all 33 implemented integer-Zca rows, including RV32 C.JAL and the RV64
LD/SD/word/stack-relative forms, and resolves exact RV32 (26-row) or RV64
(32-row) product metadata without creating a runtime decoder selector. Its
25 common-Zca rows alone drive the critical-subset manifest's verified-entry
count, so the table cannot inflate a partial critical capability claim.

The obsolete RV64 local compressed decoder and its format builders have been
deleted. The shared RV64 specialization is now the only normal compressed
integer decoder owner; target HWIR/VHDL equivalence is still a separate proof
obligation.

`CoreConfig` now records `isa_profile` and `compressed_decode_profile` as
elaboration data. It has explicit RV32/RV64 integer-Zca and common-critical
constructors and rejects an XLEN/profile mismatch before emission. The default
strict HWIR seed remains `none`, so its successful VHDL analysis cannot be
misread as compressed-product support.

The production critical VHDL selector and `simple-vhdl` CLI now accept explicit
`rv32-zca-critical` and `rv64-zca-critical` product targets as well as the
base RV32/RV64 choices. These target strings resolve only to the corresponding
concrete `CoreConfig`; they do not enable a runtime extension switch or claim
the incomplete critical subset as full Zca.

The real-MIR strict lowerer now supports both the original Bool AND seed and a
fixed `u32` AND datapath. A `u32` operation remains 32 bits even when the
selected product has XLEN=64; this is the required separation between parcel/
instruction widths and architectural XLEN before compressed decode lowering.
It also supports fixed-width OR, the complementary instruction-field merge
operation. All other compressed control, shifts, constants, and structured
results remain deliberately fail-closed until typed HWIR support exists.

Typed HWIR now also has fixed-width constants and internal-signal slots. A
32-bit `parcel & 0x0000_FFFF` graph renders a typed numeric VHDL constant and
passes GHDL analysis; this is the first target-checked primitive for parcel
extraction, not a claim that full decompression already lowers through HWIR.
The same graph now lowers from real MIR when it is expressed as typed
`Const(Int(65535), u32)` followed by `BitAnd`; it fails closed for every other
constant/control-flow shape.

Typed bounded logical-right shift is now available for `u32` parcel values via
`Const(Int(0..31), u32)` followed by `Shr`. It emits an `unsigned` VHDL shift
with a typed shift amount and passes GHDL analysis; variable shifts and all
multi-step decoder graphs remain fail-closed.

The first two-stage real-MIR extraction graph is now supported:
`(parcel >> 13) & 7`. It materializes an internal typed `shifted` signal,
enforces one combinational driver per result, and passes GHDL analysis. Branch
decode and general decompressor control remain fail-closed. A generated GHDL
testbench additionally simulates `0xA000` and checks the resulting field is
`5`, providing behavior—not only syntax—evidence for this primitive.

The canonical C.EBREAK expansion (`0x9002 → 0x00100073`) is now a typed
constant-output strict HWIR leaf with GHDL simulation evidence. Strict HWIR
also has typed equality and select nodes: equality produces only a writable
one-bit value, and select requires a readable one-bit condition plus matching
branch/result widths. A target-simulated C.EBREAK graph proves both the match
and non-match paths (`0x9002 → 0x00100073`, `0x0001 → 0`). This is a
hand-constructed HWIR target proof; real-MIR control-flow lowering remains
fail-closed except for the audited frontend-style C.EBREAK shape: a four-block
`Eq`/`If`/constant-copy/join-return graph lowers into the same typed equality
and select nodes. Extra blocks, altered edges, non-Bool predicates, different
literals, or non-joining branches are rejected before VHDL emission.

The terminal lowering is one shared implementation rather than a per-row
decoder fork. Its closed dispatch currently admits only C.EBREAK
(`0x9002 → 0x00100073`) and C.NOP (`0x0001 → 0x00000013`) triples, each with
an illegal-zero miss output. Other structurally identical control graphs and
parcel literals reject until they gain an explicit ISA-table-backed proof.
The primitive additionally requires `zca-common-critical`; base RV32/RV64 and
the broader integer-Zca profile cannot accidentally claim this targeted proof.

Typed HWIR now supports bounded logical-left shift alongside right shift. The
real-MIR strict lowerer accepts exactly a typed `Const(0..31)` followed by
`Shl` or `Shr`; VHDL emits `shift_left` or `shift_right` over unsigned bits.
This supplies the canonical instruction-field placement primitive required by
the next C.ADDI row graph without creating a width or signed-host-value path.

The first shared Zca C.ADDI/C.NOP row is now expressed as a hand-constructed
critical HWIR graph: it masks the 16-bit parcel, classifies the row, extracts
`rd` and the split immediate, sign-fills the 12-bit immediate, assembles the
three canonical I-format fields, and gates the result with the row predicate.
It uses only typed 32-bit constants, shifts, bitwise operations, equality, and
select. It is intentionally not yet a claim that arbitrary C.ADDI MIR CFGs
lower: that route remains closed until an ISA-table-backed MIR-shape proof is
implemented. The system scenario defines representative positive, negative,
and non-row emitted-VHDL/GHDL vectors. The current launcher still identifies
itself as a bootstrap seed, so a current self-hosted rerun remains required for
release evidence.

The capture-based VHDL wrapper reports false results under the bootstrap
interpreter even though `ghdl` is installed. This system scenario instead uses
the repository's established tuple-return process façade with the same
VHDL-2008 commands. It now passes analysis, elaboration, and simulation of the
exact emitted `strict_caddi_decode` DUT/testbench, completing at 7 ns with all
seven assertions passing. The bootstrap result is concrete target evidence for
the checked graph; a current self-hosted SPipe rerun still owns release-quality
harness evidence.

The C.ADDI graph additionally has bounded row-level target equivalence: its
generated VHDL testbench exhausts all 2,048 Q1/funct3=000 parcels (32
destination registers by 64 six-bit immediates) and checks the canonical ADDI
encoding on each cycle. This includes C.NOP as `rd=0, imm=0`, but is strictly
row-scoped rather than evidence for the other critical-Zca entries.

The subset manifest now reports twenty-five row-level target-proven entries:
`zca.c.ebreak`, `zca.c.addi4spn`, `zca.c.lw`, `zca.c.sw`, `zca.c.lwsp`,
`zca.c.swsp`, the five-bit `zca.c.slli.low`, `zca.c.srli.low`, and `zca.c.srai.low` rows, `zca.c.andi`, `zca.c.sub`, `zca.c.xor`, `zca.c.or`, `zca.c.and`, `zca.c.jr`, `zca.c.mv`, `zca.c.jalr`, `zca.c.add`, shared `zca.c.nop_addi` table row,
and `zca.c.li`, plus the 64-encoding `zca.c.addi16sp` row, the 2,048-encoding
`zca.c.lui` row, the typed redirect `zca.c.j` row, and the typed conditional
redirect `zca.c.beqz` and `zca.c.bnez` rows. This is intentionally distinct
from `target_rtl_equivalence_verified`: `row_target_evidence_complete` is true
because every selected row has its own proof, while composed frontend
equivalence stays false until one generated path proves parcel buffering,
register binding, redirect, and retirement together.

`HwFrontendHandoffInterface` now freezes that future path's boundary without
pretending it exists: it carries the branch-predecode contract and adds a
one-bit `dispatch_accept` input and `retire_valid` output. The contract forbids
configuration drift and duplicate ports, but does not instantiate rows, own PC
state, or establish legacy protected-core equivalence.

The current emitted integration is intentionally narrower than that future
stateful frontend: `strict_zca_control_predecode_hwir` flattens only the
already-proven direct C.J and C.BEQZ/C.BNEZ rows. RV32/RV64 GHDL tests prove
their mutually exclusive selection, concrete PA/XLEN specialization,
register-index binding, and unsupported-parcel fallthrough. It does not
advertise full Zca because indirect C.JR/C.JALR, trap ownership, a parcel queue,
and dispatch/retirement transport remain absent.

The strict lowerer and the target-evidence manifest now consume one
compiler-common, 24-contract `RiscvZcaStrictContract` catalog. A strict MIR
intrinsic must resolve through that catalog before its typed row constructor is
selected; the manifest derives the corresponding twenty-four non-terminal rows
from it plus the separately proven C.EBREAK terminal row. This eliminates
duplicated intrinsic-name/row-label dispatch without broadening the 25-entry
critical subset or its release claim.

Admission is fail-closed even for reserved-looking names: a one-argument
`__simple_riscv_zca_*` MIR intrinsic absent from that catalog receives the
stable `HWIR-E-MIR-INTRINSIC` diagnostic before any alternative strict shape or
legacy emitter can be considered. The real-MIR extraction suite covers this
mutation together with every cataloged non-terminal row.

Target capability evidence is intentionally a second, explicit allowlist. A
strict contract makes a row eligible for lowering; it does not make it proven
or advertise it. Only a row named in the target-evidence allowlist after its
generated VHDL analysis/simulation is allowed into the manifest, with ISA ID
and XLEN scope recovered from the corresponding contract to prevent metadata
drift.

`HwModuleDef` validation now binds that provenance to product selection: any
origin named `zca.*` must use `zca-common-critical`. A directly constructed
graph under a base RV32/RV64 configuration fails before target emission, so
semantic-origin metadata cannot bypass the critical capability boundary.

The C.LI and C.ADDI/C.NOP graphs are compiler-owned constructors in
`hwir/zca_rows.spl`, rather than existing solely as test graphs. Each accepts
only a named module and the concrete common-critical configuration, validates
the graph before return, and cannot choose a name-based, runtime-XLEN, or
legacy decoder shortcut.

The exact-MIR extractor is now implemented for the reserved C.LI and
C.ADDI/C.NOP semantic intrinsics, `__simple_riscv_zca_cli_row_v1` and
`__simple_riscv_zca_caddi_row_v1`. It validates the sole `u32` parcel
argument, sole result temporary, direct return, one-entry-block CFG, and exact
intrinsic spelling before invoking the corresponding graph constructor. This
is an internal semantic boundary intended for future ISA-table front-end
lowering; ordinary calls, extra state, malformed operands, and non-semantic
returns fail before HWIR/VHDL exists.

The C.EBREAK, C.ADDI/C.NOP, and C.LI target scenarios now invoke their
compiler-owned constructors directly before VHDL rendering. The two variable
immediate rows exhaust all 2,048 row encodings; C.EBREAK covers matched and
unmatched parcels. The target proofs therefore cover the same typed graphs
selected by strict semantic-MIR boundaries, rather than separately maintained
test fixtures.

The terminal C.NOP MIR shape is deliberately still validated as a four-block
conditional, but after validation it selects the shared C.ADDI/C.NOP row
constructor. Thus the architectural alias cannot acquire a separate critical
hardware implementation or an alternate timing/fallback path.

C.ADDI4SPN now follows the same route: its reserved
`__simple_riscv_zca_addi4spn_row_v1` semantic intrinsic accepts exactly one
`u32` parcel and direct `u32` return before selecting the compiler-owned row.
The graph is independent of XLEN, so RV32 and RV64 products share identical
concrete 32-bit parcel logic after elaboration.

C.LW likewise has a compiler-owned common row and reserved
`__simple_riscv_zca_lw_row_v1` semantic intrinsic. Its profile-gated,
origin-tracked graph reconstructs both prime registers and every unsigned
offset field. The generated VHDL exhaustively simulates all 2,048
Q0/funct3=010 row parcels plus a non-row rejection, so C.LW is now counted as
row-level target-proven. That bounded proof does not promote the incomplete
Zca subset to a release claim.

C.SW follows the same boundary with the reserved
`__simple_riscv_zca_sw_row_v1` semantic intrinsic. Its typed graph reconstructs
the split S-format immediate fields and both prime registers, then exhaustively
simulates all 2,048 Q0/funct3=110 parcels and a non-row rejection. It is
therefore target-proven at the row level only; no whole-extension claim follows.

C.LWSP is the first target-proven stack-relative load row. Its reserved
`__simple_riscv_zca_lwsp_row_v1` semantic intrinsic selects an origin-tracked,
profile-gated graph which rejects `rd=x0` before target output. The emitted
VHDL exhaustively covers all 4,096 Q2/funct3=010 encodings, including every
reserved register value, plus non-row rejection. This remains bounded evidence,
not a full-subset or release claim.

C.SWSP is likewise target-proven at row scope: its reserved semantic intrinsic
selects the common stack-relative-store graph, whose generated VHDL exhausts
all 2,048 Q2/funct3=110 encodings plus a non-row rejection. It remains one
bounded entry in a deliberately incomplete, non-advertised subset.

The C.SLLI proof deliberately covers only the common five-bit shift subset.
Its classifier includes parcel bit12, exhaustively proves all 1,024 low-shamt
encodings, and rejects a bit12-set high-shamt parcel. This prevents RV64-only
six-bit shifts from being silently accepted in a shared critical product.

The C.SRLI proof has the same deliberately narrow bound: it exhaustively covers
all 256 Q1/mode-00 five-bit-shift parcels, while rejecting both adjacent C.SRAI
and bit12-set high-shamt forms. Prime-register reconstruction is explicit in
the HWIR graph and preserves the canonical `x8..x15` operand range.

C.SRAI is emitted separately from C.SRLI, with a mode-01 classifier and a
visible arithmetic-shift immediate bit. Its target test exhausts all 256 legal
low-shamt parcels and rejects C.SRLI plus bit12-set high-shamt forms.

C.ANDI is separately classified as Q1/mode-10. Its classifier intentionally
leaves bit12 free because it is the signed-immediate high bit; exhaustive target
simulation covers all 512 compact-register/immediate combinations and validates
negative-immediate sign extension while rejecting neighboring shift and C.SUB modes.

C.SUB is the first compact register-register arithmetic row. Its fixed
classifier excludes C.XOR/C.OR/C.AND and bit12-set RV64-only C.SUBW; target
simulation exhausts all 64 compact operand pairs.

C.SUB and C.XOR now share one closed compiler-host compact-R elaborator. Each
public row wrapper fixes its ISA tag, predicate and canonical funct fields before
HWIR construction; there is no runtime hardware operation selection. C.XOR adds
its own exhaustive 64-pair target proof and rejection checks for neighboring modes.
C.OR is likewise a fixed wrapper over that elaborator and has independent
64-pair target evidence, including C.XOR/C.AND/high-bit rejection boundaries.
C.AND completes the bit12=0 compact-R subset using the same closed elaborator,
with a separate 64-pair target proof and C.OR/C.SUB/high-bit rejection checks.

C.JR is now a separately typed Q2 control-transfer row. Its classifier fixes
`funct3=100`, `bit12=0`, and `rs2=0`; a second typed select rejects the reserved
`rd=x0` encoding. Generated VHDL exhaustively covers all 32 `rs1` fields and
rejects the adjacent C.MV and C.JALR encodings. This is row-level evidence only:
the architecture still has no release-level Zca equivalence claim.

C.MV is now a separately typed Q2 register-transfer row. It fixes
`funct3=100` and `bit12=0`, rejects `rs2=x0` so C.JR and reserved encodings
remain outside the graph, and normalizes the architectural `rd=x0` hint to
canonical NOP. Generated VHDL exhaustively covers all 992 valid source/destination
combinations and rejects C.JR, reserved, and C.ADD neighbors. This remains
row-level target evidence only.

C.JALR is now a separately typed Q2 control-transfer row. It fixes
`funct3=100`, `bit12=1`, and `rs2=0`, rejects the reserved `rd=x0` encoding,
and emits canonical `JALR x1, rs1, 0`. Generated VHDL exhaustively covers all
32 source-register fields and rejects C.JR, C.MV, and C.ADD neighbors. This is
row-level target evidence only and does not enlarge the release claim.

C.J is the first direct-control row that uses the frozen typed predecode
interface rather than a canonical-instruction-only result. Its concrete graph
retains the original 16-bit parcel and length, reconstructs the signed
compressed offset, calculates `next_pc` and redirect target at the selected
physical-address width, and emits `JAL x0, offset`. Generated VHDL simulation
covers forward, backward, and non-row fallthrough behavior. Its aggregate
strict-MIR contract requires `Bits[16], Bits[PA]` input and a six-field typed
predecode result; invalid scalar-PC substitutions fail before emission. It is
therefore included in the row-level target-evidence allowlist, without changing
the incomplete-subset or release boundary.

C.ADD is now emitted as separate RV32 and RV64 concrete graphs. Both graphs
reject `rs2=x0` and non-C.ADD neighbors; RV32 normalizes the `rd=x0` hint to
NOP, while RV64 retains `ADD x0, x0, rs2`, matching the product-specific shared
decoder behavior. Exhaustive generated-VHDL simulation covers all 992 nonzero-
`rs2` field combinations for each product. The configuration decision is made
during elaboration, not by RTL XLEN selection.

The system evidence now also exercises the VHDL CLI/driver boundary: with the
typed critical policy transported to the compiler process and an explicit RV32
target, a real `@hardware` Boolean AND emits VHDL plus a provenance manifest
whose generation route is `hwir-strict`. This is route evidence for the
supported strict seed only. The same scenario suite feeds unsupported Boolean
XOR under critical policy and asserts nonzero exit with neither VHDL nor
manifest sidecar, proving that strict failure cannot fall through to legacy
emission.

## Independent exhaustive compressed-oracle lane (2026-08-12)

The repository contained row-local exhaustive VHDL testbenches but no pinned
Sail checkout, executable Sail/Spike/RISCOF tool, or independent 65,536-parcel
RV32/RV64 truth asset. Those row tests are valuable implementation evidence,
but their expected values are constructed beside the HWIR tests and therefore
cannot serve as an independent semantic oracle.

The new oracle lane is deliberately outside decoder source. It pins upstream
`riscv/sail-riscv` tag `0.10` at commit
`a33475aeb80090127433b5a8b30e717edaa19e71`, checks both a deterministic Git
archive SHA-256 and the Zca semantic source SHA-256, and defines two ordered TSV
tables covering parcels `0000` through `FFFF`. The validator refuses absent
tables, duplicate/missing/reordered parcels, malformed records, digest drift,
unpinned provenance, generator drift, and fixture-level qualification claims.
The checked-in manifest intentionally remains `status=absent` because this host
does not contain an independently reviewed Sail batch adapter. No qualification
flag is promoted by scaffolding or validator self-tests.
