<!-- codex-design -->
# RISC-V Gen2 HWIR Foundation Detail Design

1. `CoreConfig.rv32()` and `.rv64()` construct valid configurations. Validation
   rejects any other XLEN, non-positive address width, or non-positive register
   count.
2. A strict lower request holds `HwirLowerInput` plus `CoreConfig`. It first
   validates configuration and hardware tagging, then creates `in_a`, `in_b`,
   and `out` concrete `Bits[XLEN]` ports, one `and` operation, and origin IDs.
3. A strict result is success-or-diagnostic only. It has no legacy fallback
   field and callers cannot treat a failed strict request as V1 compilation.
4. The emitter validates names, widths, operation operands, and supported
   operation kind; it renders a VHDL entity and concurrent assignment.
5. Tests cover RV32/RV64 output width, invalid configuration, non-hardware
   rejection, malformed module/unknown-op rejection, deterministic rendering,
   explicit legacy-route separation, and the same focused lint gate under the
   `critical` assurance profile.
6. Real-MIR extraction is a closed, fail-closed subset: fixed-width
   combinational constants/bitwise graphs plus shape-checked declarative
   common-Zca intrinsics and the exact terminal C.EBREAK/C.ADDI CFG. It
   validates non-variadic closed locals, types, entry/CFG shape and direct
   returns before mapping any approved form to typed HWIR. Generic, clocked,
   unapproved, or malformed graphs fail before emission.
7. `CompileContext` snapshots `ResolvedAssurancePolicyV1` once. Any nonempty
   `CompileOptions.riscv_gen2_target` requires critical strictness before stale
   artifact removal; otherwise the driver returns `HWIR-E-CRITICAL-POLICY` and
   cannot silently choose legacy VHDL. A critical hardware design resolves its
   target and calls `compile_strict_hwir_module`. A rejection returns `HWIR-E-*`;
   it does not call the legacy serializer. The strict artifact reports its route,
   node identity, XLEN, and configuration in the VHDL header and manifest.
8. `simple-vhdl` accepts `--riscv-gen2-target rv32|rv64` for the direct
   compiler-driver entry only under `SIMPLE_SAFETY_PROFILE=critical`; a target
   outside that policy is a hard error. The general compiler CLI integration
   remains a follow-up because its VHDL facade has a separate source-subset
   fast path.
9. `strict_riscv_predecode_interface` is the closed elaboration constructor for
   compressed fetch/decode boundaries. It accepts only a validated
   `zca-common-critical` `CoreConfig`, fixes parcel/canonical/length/flag ports
   to 16/32/2/1 bits, and specializes `fetch_pc`, `next_pc`, and
   `redirect_target` to `physical_address_bits`. The constructor validates
   directions, names, and widths before a control-row graph can be emitted;
   it has no runtime XLEN argument and does not infer redirect behavior.
10. `strict_zca_cj_predecode_row_hwir` uses that contract to preserve the
    original parcel, assemble the canonical `JAL x0, offset`, sign-extend the
    12-bit compressed offset to the selected PA width, and calculate
    `next_pc`/redirect target with typed modulo-address addition. A non-row
    parcel is illegal for this row wrapper, has `redirect_valid=false`, and
    falls through by two bytes. The row enters the strict-MIR catalog and target
    capability allowlist only after its exact source-shape admission exists; the
    aggregate `Bits[16], Bits[PA]`/six-field result contract now supplies that
    admission boundary.
11. `strict_riscv_branch_predecode_interface` is the prerequisite for
    C.BEQZ/C.BNEZ. It composes the frozen parcel/PC contract with a paired
    `rs1_index: Bits[5]`/`rs1_value: Bits[XLEN]` architectural read and
    validates all base-port widths and product-specialized operand width. A
    conditional row must prove the decoded prime-register index matches the
    supplied index before it uses the value in its equality/selection graph; no
    hidden register-file provider, runtime XLEN selector, or unconditional
    redirect is permitted.
12. The first C.BEQZ/C.BNEZ constructors use static elaboration arguments for
    their row tag, canonical branch funct3, and whether a zero operand is
    taken. They materialize those choices as fixed constants, compare the
    explicit XLEN-wide operand against a typed zero constant, and select both
    `next_pc` and `redirect_target` only when the matching row is taken and the
    read-index binding is valid. This admits only an exact four-input aggregate
    source intrinsic. Row-level generated-VHDL vectors exist, but composed
    frontend target equivalence remains a separate, false claim.
13. `strict_riscv_frontend_handoff_interface` freezes the only permitted Gen2
    boundary between compressed row composition and dispatch. It preserves the
    typed branch-predecode parcel/PC lineage and adds `dispatch_accept: Bits[1]`
    and `retire_valid: Bits[1]`. It deliberately does not create a second PC or
    retirement owner, compose row logic, or claim legacy-core equivalence.
14. `strict_zca_control_predecode_hwir` is the first emitted composition. It
    alpha-renames and flattens the typed C.J, C.BEQZ, and C.BNEZ row graphs into
    one module with concrete 16-bit parcel, PA-width PC, five-bit register
    index, and XLEN value inputs. Deterministic selection gives C.J then
    C.BEQZ then C.BNEZ priority, with an illegal instruction, two-byte
    fallthrough, deasserted redirect, and fetch-PC redirect target by default.
    It is explicitly limited to a length-predecoded parcel and has no channel,
    parcel-buffer, indirect-control, trap, or retirement semantics.
15. `compiler_driver_run_riscv_gen2_zca_control_predecode_product` is a
    distinct generated-product route. It has no user source/HIR/MIR input and
    requires `critical` policy, `rv32-zca-critical` or `rv64-zca-critical`, an
    explicit output, zero AOP requests/weaves, and the fixed product ID. It
    validates those conditions before cleanup, then checks that the emitter's
    node/profile equals the reconstructed typed product graph. Its artifact
    builder emits concrete flat HWIR ports and `compiler_product_entity` with
    `source:null`; catalog-based source provenance is intentionally not reused.
    The stateful product variant additionally binds complete `CoreConfig`, its
    public port contract, versioned length-prefixed ordered sequential-plan
    text, decoder entity/digest,
    and origins into its closure hash; a route label or hash-shaped value alone
    is not an admissible critical artifact.
    Profile labels and strict VHDL identifiers are validated before rendering:
    profiles are bounded alphanumeric/`_`/`-` labels and identifiers reject
    VHDL reserved words, so provenance fields cannot introduce raw VHDL text.
16. `HwParcelFrontendDef` is the initial sequential product form, bounded to
    one entry rather than a generic FIFO. Its eight explicit default-domain
    registers hold valid, issued, a 64-bit monotonically incrementing lineage,
    sticky-fault, parcel, PA-width PC,
    register index and XLEN register value. The renderer creates one
    `rising_edge(clk)` process with synchronous active-high reset and
    instantiates the typed migrating decoder. Its flattened predecode priority
    selects only explicit row `legal` signals and otherwise emits illegal,
    two-byte fallthrough metadata. The retirement input carries `retire_lineage`,
    `retire_original_parcel`, `retire_canonical_instruction`, and
    `retire_original_length_bytes`. The sequential logic prioritizes invalid
    retirement fault, one retirement matching all four identity fields,
    dispatch, then fetch,
    ensuring no fetch reuse before retirement and stable captured data while
    dispatch is stalled. Lineage equality cannot authorize a retirement whose
    parcel, canonical instruction, or length differs. Any early, stale,
    repeated, or identity-mismatched valid retirement is a sticky fault and
    reset is the only recovery path. This bounded product is
    development-stage source evidence, not a release-qualified core. Its retire
    producer must share reset ownership, so pre-reset transactions cannot be
    presented after a frontend reset. A matching retirement at the terminal
    64-bit lineage value enters the sticky fault state without incrementing;
    reset is therefore required before any lineage value could be reused.
    Because the three added retirement identity inputs alter the ordered public
    ports, this is an ABI and graph-closure change. Existing stateful product
    labels remain development-only until the owner makes an explicit product
    version decision and regenerates qualified manifests.
17. `HwParcelRetirementComposition` binds one `HwParcelFrontendInterface` to
    a future `HwRetireReceiptProducerInterface`. It has a fixed 15-binding
    topology: shared `clk`/`rst`, dispatch valid plus its 64/16/32/2-bit
    identity tuple to the producer, then producer acceptance and the same
    receipt tuple back. Shape validation rejects an omitted, reordered, or
    width-drifted binding. It is an elaboration-only contract until typed
    child instances and architectural effects have sequential HWIR lowering.
    A serializable strict-VHDL result cannot substitute for that lowering:
    its metadata and VHDL comments are inspectable but not an opaque producer
    capability, so composition emission is explicitly rejected for now.
18. `RiscvGen2ScalarElaboration` freezes one concrete `CoreConfig`, exact
    scalar decoder table, and provider selection. `RiscvGen2ScalarDispatchPlan`
    then resolves one 32-bit instruction from that fixed table and accepts its
    provider only through the selection's structural ownership check. This is
    compiler-host preparation for a shared execution-unit lowerer: it does not
    emit an RTL decoder, make a runtime profile decision, or claim scalar-core
    execution coverage.
19. `strict_zca_addi4spn_outcome_hwir` is the first reserved normal-row adapter. It
    zero-extends the frozen 16-bit parcel into the established 32-bit row
    graph, alpha-renames that graph, and derives output `legal` from both
    `is_c_addi4spn` and the explicit nonzero-immediate gate. It never infers
    legality from `canonical_instruction`. The private
    `strict_zca_tagged_data_outcome_hwir` applies that form only to
    classifier-complete rows. `strict_zca_reserved_data_outcome_hwir` is the
    separate private chain for explicit true-means-reserved predicates (C.LWSP
    and C.LUI). Neither helper admits positive-eligibility, register-read/
    redirect, or trap rows.
20. `strict_zca_target_trap_migrating_predecode_hwir` is the global effectful
    product composition. Elaboration selects either the RV32 common+C.JAL graph
    or the RV64 common+C.ADDIW graph, then composes C.EBREAK through one outer
    uniqueness guard. The layer does not decode JR/JALR or read a register a
    second time. On ambiguity it emits the bounded illegal `PC+2` tuple and
    zero trap metadata; otherwise it preserves the selected canonical word,
    original length, redirect tuple, and explicit breakpoint cause/tval.
21. A locked `Architecture`/`observe`/`commit.retire` aspect may attach typed
    outputs to the exact stable retirement-composition node. Validation rejects
    foreign nodes, non-receipt producer fields, width mismatches, duplicate
    output names, resource/accounting mismatches, state, and nontransparent
    latency. The disabled path returns the composition verbatim. The weave hash
    sorts attachment identities, so discovery order cannot change provenance.
22. A standalone or child-bound `HwSequentialModuleDef` may include a typed
    combinational datapath that feeds guards, assignments, or outputs. Its
    value namespace includes input ports, registers, child output pins,
    declared signals, and typed constants; output ports are write-only. Every
    signal has one driver, operand/result widths are checked per operation, and
    unsupported operations fail before rendering. The backend emits constants
    and signals in the architecture declaration area, then typed datapath
    assignments before sequential output/process logic. `LsuConfig` keeps bus
    and byte-mask geometry explicit product data rather than deriving it from
    XLEN. The focused mixed-datapath specification covers positive lowering,
    unsigned predicates, invalid sources/operations/drivers, LSU geometry, and
    graph-hash drift.
23. Parcel/trap compilation validates its fixed interface, decoder, pins,
    registers, origins, and plan before adapting them into a child-bound
    `HwSequentialModuleDef`. The compiled decoder digest becomes
    `child_graph_sha256`; the generic renderer emits the parent and its v3
    structural digest, and the product helper prepends the decoder once. The
    compatibility hash helper constructs that same canonical module.
24. Qualification is a two-phase transaction. The runner stages admitted CLI,
    coverage, testbench, and GHDL command evidence while the final path is
    absent. The Simple composer validates a v2 exact-key manifest, copies
    hash-bound artifacts into a fresh run, and writes its receipt last.
