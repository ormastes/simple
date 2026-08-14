# RISC-V Gen2 HWIR Foundation Architecture — TLDR

This slice makes critical RISC-V hardware compilation fail closed: typed,
concrete HWIR is the only critical route, while the direct VHDL generator stays
an explicit legacy route.

Current implementation boundary: a critical `@hardware` source with an explicit
RV32/RV64 Gen2 target is routed through strict MIR→HWIR→VHDL; unsupported MIR
fails closed. A deployed self-hosted wrapper currently rejects its runtime as
non-production, so bootstrap-seed output is not release evidence.

## Core Shape

- `CoreConfig -> strict MIR lowering -> HwModuleDef -> strict VHDL` fixes XLEN,
  address width, and compressed profile before target emission.
- Stable `HwNodeId`/`HwOrigin` values retain source lineage; malformed hardware
  produces stable `HWIR-E-*` diagnostics instead of legacy output. Strict
  manifests bind the canonical typed combinational graph with SHA-256.
- Real-MIR lowering supports a finite bitwise/constant subset and an approved,
  signature-checked Zca intrinsic table; terminal C.EBREAK/C.ADDI CFGs are
  matched structurally rather than by a source-name convention.
- `HwPredecodeInterface` now freezes parcel/decode/redirect ports for the next
  control-flow rows. It accepts only `zca-common-critical`, uses fixed 16/32/2/1
  bit fields, and specializes all PC fields to the selected PA width.
- `HwBranchPredecodeInterface` adds an explicit `rs1_value: Bits[XLEN]` input;
  conditional branch constructors cannot perform a decoder-side provider lookup
  or runtime width selection.
- `HwSequentialModuleDef` is the canonical mixed sequential boundary. It owns
  typed signals/constants, combinational operations, comparisons, selections,
  extracts/slices, state plan, child binding, and complete structural hash;
  strict VHDL renders declarations then datapath then process. Parcel and trap
  products now construct this same boundary while retaining their fixed
  product validators and prepending the decoder exactly once.
- The parcel frontend is a synchronous,
  one-entry parcel/PC/branch-read capture with a concrete 64-bit monotonically
  incrementing transaction lineage. It
  preserves payload under dispatch stall, waits for one matching 64-bit-lineage
  retirement before reuse, and makes early, stale, mismatched, or repeated
  retirement a sticky reset-cleared fault. The typed
  migrating decoder is instantiated rather than duplicated; it admits only
  normalized rows plus index-bound indirect redirects and leaves C.EBREAK
  illegal. Its `HwSequentialPlan` owns registers, reset values, priority rules,
  guards, assignments, decoder pins, and output bindings; emitted VHDL carries
  the resulting state-graph closure hash and stable per-register, rule, pin,
  and output `HwNodeId` anchors for VHDL-to-HWIR lineage.
- Source-less stateful/trap compiler products are development-stage only. Their
  provenance binds the concrete module ID, complete configuration, frontend
  port contract, ordered typed plan, decoder identity/digest, origins, and a
  64-character closure hash. Release qualification still requires self-hosted
  RV32/RV64 generated-VHDL and fault-protocol evidence plus a reset-coupled
  retirement producer. The terminal 64-bit lineage retirement faults before
  increment, preventing counter wrap and token reuse before reset.
- The common-Zca evidence catalog records declared row coverage only. It stays
  non-qualified until the self-hosted RV32/RV64 generated-VHDL/GHDL lane runs.
- `riscv_common.retire.RiscvRetireRecord` is the shared RV32/RV64 retirement
  boundary. Existing RVFI snapshots map into it with concrete XLEN, effects,
  trap/interrupt, and PC transition data; it is host/formal/debug metadata,
  not runtime-selectable hardware. The concrete chain checker consumes records
  directly and rejects invalid or mixed-XLEN valid-retire traces before its
  non-vacuous order/PC checks; traps and interrupts are explicit
  control-transfer exceptions to ordinary PC chaining.
- `riscv_common.isa.scalar_database` is the next declarative shared semantic
  seed: I, M, and first RV64 word/shift rows have exact encodings, XLEN scope,
  operation/effect metadata, and fail-closed duplicate/overlap validation. It is elaboration
  metadata, not a dynamic RTL decoder or a complete scalar-ISA claim.
  Its host lookup returns exactly one validated concrete entry or a stable
  diagnostic; it is the intended future decoder/toolchain metadata boundary.
  Profile lookup also excludes M rows unless a concrete `im` profile selects
  them. The associated scalar provider selection freezes `none` for I or a
  concrete iterative/pipelined/DSP M provider for IM before HWIR lowering;
  neither choice is a datapath selector.
- `CoreConfig` accepts only supported scalar profile identities and rejects an
  RV32/RV64 prefix that disagrees with concrete XLEN before HWIR construction.
- `rv32i_zmmul` and `rv64i_zmmul` elaborate the shared M multiply rows (plus
  RV64 `MULW`); division/remainder never enter those concrete product tables.
- `HwirRiscvScalarBindingPlan` connects a selected scalar provider to target
  resource identities. Its latency is explicitly `uncommitted` (`-1`) until
  RTL resource instances and verified latency contracts are implemented.
- Non-control rows first become typed outcomes with explicit classifier and
  reserved-encoding legality. The migrating composition uses only `legal` as
  its deterministic priority predicate; canonical-zero is never a predicate.
  A typed overlap accumulator makes any multiple match illegal rather than
  allowing priority order to silently select an instruction.
- `hwir.aspects` freezes compiler-host aspect manifests/plans: hash-pinned,
  semantic-node applications with capability/conflict/proof/latency metadata.
  Emitted artifact identities are canonically ordered, so plan ordering cannot
  alter a Gen2 provenance manifest; the manifest digest is recomputed from the
  same identities and a mismatch fails closed.
  Each effect class requires its named minimum proof obligation; free-form
  “proof” labels do not satisfy the critical declaration boundary.
  It rejects textual VHDL advice and required zero-match/zero-weave plans; an
  absent plan is structurally empty. Its first graph transform supports only
  a matched, transparent, state-free observational output probe; it appends a
  typed pass-through plus derived origin, revalidates the complete graph, and
  passes that graph directly to the strict no-fallback VHDL serializer.
  Per-module matches and declared weave counts must exactly equal materialized
  probe attachments.
  `HwAspectLock` pins the exact manifest ID/version/SHA-256 set before the
  locked weaver can mutate a graph. Gen2 artifact manifests record the lock
  digest and typed aspect identities; lockfile discovery remains pending.
  All stateful, timing-changing, provider, lockfile, and proof-execution work
  remains pending.

## Open Next

- Qualification v2 is source-level only. It separates command-producing
  staging from the Simple receipt composer, but PASS still requires
  executable proof of the compiler-time zero-count coverage inventory,
  exact/duplicate-safe evidence validation, writer deliberate reds, an admitted Stage-4 CLI, and independent
  RV32/RV64 GHDL receipts.
  The inventory source is implemented with canonical tag-dispatched flat-AST
  ownership and span-preserving parser/desugar keys; the available Stage-3
  bootstrap artifact exits 139 on both focused native and SMF compile probes.

- [Architecture](riscv_gen2_hwir_foundation.md)
- [Predecode interface](../../src/compiler/50.mir/hwir/predecode.spl)
- [Stateful frontend](../../src/compiler/50.mir/hwir/stateful_frontend.spl)
- [Predecode tests](../../test/01_unit/compiler/50.mir/hwir_predecode_contract_spec.spl)
- [Gen2 system test plan](../03_plan/sys_test/riscv_gen2_hwir_foundation.md)
## Trap-effect v2 boundary

`HwTrapPredecodeInterface` carries C.EBREAK as legal canonical EBREAK plus a
typed breakpoint-cause request. `HwTrapParcelFrontendDef` freezes the intended
single-outstanding dispatch/retirement boundary, but is not release-qualified
until its retirement-source contract and self-hosted evidence are complete.
Its v2 product is emitted only from that typed plan and full closure hash; v1
remains unchanged and does not claim C.EBREAK support.
