# RTL Backend Unification Plan (2026-07-21)

**Reference:** BUG-RTL-001 from RISC-V RTL audit  
**Status:** PLAN ONLY — No implementation this pass  
**Scope:** `src/compiler/70.backend/backend/`, `src/compiler/80.driver/`

---

## Problem Statement

### Current State
The compiler has **two separate VHDL emission paths** and **no SystemVerilog backend**:

1. **Full MIR→VHDL Path:** `VhdlBackend` (`src/compiler/70.backend/backend/vhdl_backend.spl`)
   - Implements `Codegen` trait
   - Implements `HardwareCodegen` trait with `compile_entity`, `compile_package`, `compile_process`
   - 30+ supporting VHDL modules in `src/compiler/70.backend/backend/vhdl/`
   - Handles scheduling, state representation, width semantics, clock domains, resets

2. **VHDL Source-Subset Emitter:** `driver_compile_vhdl_codegen.spl`
   - Direct source→VHDL text transformation (bypasses MIR)
   - **COMPILER-002 risk:** Can skip AOP weaving (partially mitigated by decorator rejection)
   - Limited to simple entity/port/expression patterns

3. **No SystemVerilog Support:**
   - `BackendKind` enum lacks `SystemVerilog` variant
   - No `SystemVerilogBackend` class exists
   - No unified RTL IR to feed multiple HDL backends

### Issues
- **Semantic lowering not unified** — VHDL-specific scheduling/state logic embedded in backend
- **No backend-neutral RTL IR** — each HDL would require separate full implementation
- **AOP bypass risk** — source-subset path can't support full AOP semantics
- **Maintenance burden** — HDL-specific semantics duplicated across backends

---

## Target Architecture

### RTL IR Layer (New)

**Location:** `src/compiler/70.backend/backend/rtl/`  
**Purpose:** Backend-neutral hardware description IR

#### RTL IR Structure

```simple
# RTL IR Core Types

struct RtlModule:
    name: text
    entities: [RtlEntity]
    packages: [RtlPackage]
    metadata: RtlMetadata

struct RtlEntity:
    name: text
    ports: [RtlPort]
    generics: [RtlGeneric]
    architecture: RtlArchitecture
    process_schedule: RtlSchedule  # NEW: Scheduling semantics
    clock_domains: [RtlClockDomain]
    reset_semantics: RtlResetSemantics

struct RtlPort:
    name: text
    direction: RtlDirection  # In, Out, InOut
    type: RtlType
    clock_domain: text?      # Optional: associate with clock domain

struct RtlType:
    kind: RtlTypeKind
    width: RtlWidth         # NEW: Explicit width semantics
    signed: bool
    encoding: RtlEncoding  # Unsigned, Signed, TwosComplement

enum RtlWidth:
    Scalar                  # Single bit
    Fixed(width: i64)       # Fixed width (e.g., 32 bits)
    Parametric(param: text) # Generic parameter (e.g., XLEN)
    Vector(len: i64, elem: RtlWidth) # Array width

struct RtlClockDomain:
    name: text
    edge: RtlEdge           # Rising, Falling
    associated_resets: [text]

struct RtlResetSemantics:
    polarity: RtlPolarity  # ActiveHigh, ActiveLow
    sync: bool             # Synchronous vs asynchronous
    priority: i64          # Reset priority (multiple resets)

struct RtlArchitecture:
    body: RtlBody
    state_elements: [RtlStateElement]  # NEW: Explicit state representation
    processes: [RtlProcess]
    concurrent_assignments: [RtlConcurrent]

struct RtlStateElement:
    name: text
    type: RtlType
    kind: RtlStateKind     # Register, Latch, Memory, Port
    clock_domain: text?
    reset_value: RtlLiteral?
    init_value: RtlLiteral?

enum RtlProcessKind:
    Combinational
    Clocked(clock: text, edge: RtlEdge)
    AsyncReset(clock: text, edge: RtlEdge, reset: text)
    SyncReset(clock: text, edge: RtlEdge, reset: text)

struct RtlSchedule:
    """NEW: Scheduling information for processes"""
    process_order: [text]           # Topological process order
    sensitivity_lists: Dict<text, [RtlSignal]>  # Per-process sensitivity
    priority_levels: Dict<text, i64> # Process priority
    combinational_loops: [[text]]    # Detected combinational loops
```

#### RTL IR Operations

```simple
# RTL IR Operations (backend-neutral)

enum RtlOp:
    # Bit/vector operations
    BitAnd
    BitOr
    BitXor
    BitNot
    ShiftLeft
    ShiftRight
    RotateLeft
    RotateRight
    Concat([RtlType])              # Concatenation with width info
    Slice(index: i64, width: i64)   # Bit slicing
    
    # Arithmetic operations
    Add
    Sub
    Mul
    DivSigned
    DivUnsigned
    ModSigned
    ModUnsigned
    
    # Comparisons
    EqSigned
    EqUnsigned
    LtSigned
    LtUnsigned
    # ... (other comparisons)
    
    # Multiplexing
    Mux(sel: RtlExpr, true_branch: RtlExpr, false_branch: RtlExpr)
    
    # Memory operations
    Load(address: RtlExpr)
    Store(data: RtlExpr, address: RtlExpr)
    
    # State operations
    RegWrite(reg: text, value: RtlExpr, clock_domain: text?)
    RegRead(reg: text)
```

### Backend Interface (Enhanced)

**Location:** `src/compiler/70.backend/backend/hardware_codegen_types.spl`

```simple
# Enhanced HardwareCodegen trait

trait HardwareCodegen:
    """Interface for hardware description generation backends."""
    
    # Core compilation (existing)
    fn compile_entity(func_name: text, body: MirBody) -> Result<text, CompileError>
    fn compile_package(module: MirModule) -> Result<text, CompileError>
    fn compile_process(kind: VhdlProcessKind, body_block: MirBlock) -> Result<text, CompileError>
    
    # NEW: RTL IR compilation (backend-neutral)
    fn compile_rtl_module(rtl_module: RtlModule) -> Result<text, CompileError>
    fn compile_rtl_entity(entity: RtlEntity) -> Result<text, CompileError>
    fn compile_rtl_process(process: RtlProcess) -> Result<text, CompileError>
    
    # Backend capabilities
    fn supported_features() -> HardwareFeatures
    fn target_dialect() -> HardwareDialect

struct HardwareFeatures:
    supports_parametric_width: bool
    supports_multi_dimensional_arrays: bool
    supports_enum_types: bool
    supports_record_types: bool
    supports_system_verilog_types: bool  # structs, unions, enums
    supports_interfaces: bool
    max_process_depth: i64

enum HardwareDialect:
    Vhdl2008
    SystemVerilog2012
    SystemVerilog2017
    Verilog2005
```

### Backend Implementations

#### VhdlBackend (Refactored)

**Location:** `src/compiler/70.backend/backend/vhdl_backend.spl`

```simple
class VhdlBackend:
    """VHDL backend now consumes RTL IR instead of MIR."""
    
    # NEW: Primary compilation path
    fn compile_rtl_module(rtl_module: RtlModule) -> Result<text, CompileError>:
        """Compile RTL IR to VHDL-2008."""
        val builder = VhdlBuilder.create(rtl_module.name)
        
        # Emit library headers
        builder.emit_library_header()
        
        # Compile packages (types, constants, functions)
        for pkg in rtl_module.packages:
            val pkg_vhdl = self.compile_rtl_package(pkg)
            builder.emit_raw(pkg_vhdl)
        
        # Compile entities
        for entity in rtl_module.entities:
            val entity_vhdl = self.compile_rtl_entity(entity)
            builder.emit_raw(entity_vhdl)
        
        Ok(builder.build())
    
    # Legacy support (delegates to RTL IR path)
    impl Codegen for VhdlBackend:
        fn compile_module(module: MirModule) -> Result<CodegenOutput, CompileError>:
            # MIR → RTL IR lowering
            val rtl_module = self.mir_to_rtl_lowering(module)
            # RTL IR → VHDL
            self.compile_rtl_module(rtl_module)
```

#### SystemVerilogBackend (New)

**Location:** `src/compiler/70.backend/backend/systemverilog_backend.spl`

```simple
class SystemVerilogBackend:
    """SystemVerilog backend consuming same RTL IR as VHDL."""
    
    type_mapper: SystemVerilogTypeMapper
    options: CompileOptions
    
    static fn create(target: CodegenTarget, options: CompileOptions) -> SystemVerilogBackend:
        SystemVerilogBackend(
            type_mapper: systemverilog_type_mapper_create(),
            options: options
        )
    
    fn compile_rtl_module(rtl_module: RtlModule) -> Result<text, CompileError>:
        """Compile RTL IR to SystemVerilog-2017."""
        val builder = SystemVerilogBuilder.create(rtl_module.name)
        
        # Emit module header
        builder.emit_module_header(rtl_module.name)
        
        # Emit packages (typedefs, structs, enums)
        for pkg in rtl_module.packages:
            val pkg_sv = self.compile_rtl_package_sv(pkg)
            builder.emit_raw(pkg_sv)
        
        # Emit module ports
        builder.emit_ports(rtl_module.entities[0].ports)
        
        # Emit logic
        for entity in rtl_module.entities:
            val entity_sv = self.compile_rtl_entity_sv(entity)
            builder.emit_raw(entity_sv)
        
        Ok(builder.build())
    
    impl Codegen for SystemVerilogBackend:
        fn backend_kind() -> BackendKind: BackendKind.SystemVerilog
        fn backend_name() -> text: "systemverilog"
        fn compile_module(module: MirModule) -> Result<CodegenOutput, CompileError>:
            # MIR → RTL IR lowering (shared with VHDL)
            val rtl_module = self.mir_to_rtl_lowering(module)
            # RTL IR → SystemVerilog
            self.compile_rtl_module(rtl_module)

impl HardwareCodegen for SystemVerilogBackend:
    fn compile_entity(func_name: text, body: MirBody) -> Result<text, CompileError>:
        # Delegate to RTL IR path
        val rtl_entity = self.mir_body_to_rtl_entity(func_name, body)
        self.compile_rtl_entity(rtl_entity)
```

---

## Migration Sequence

### Phase 1: RTL IR Foundation (Weeks 1-4)

**Goal:** Establish RTL IR types and lowering pipeline

1. **Create RTL IR types** (`src/compiler/70.backend/backend/rtl/`)
   - `rtl_types.spl`: Core RTL IR types (RtlModule, RtlEntity, RtlType, RtlWidth)
   - `rtl_operations.spl`: RTL IR operations (RtlOp, RtlExpr)
   - `rtl_state.spl`: State representation (RtlStateElement)
   - `rtl_schedule.spl`: Scheduling semantics (RtlSchedule, RtlProcessKind)
   - `rtl_metadata.spl`: Provenance metadata (hashes, source mapping)

2. **MIR → RTL IR Lowering** (`src/compiler/70.backend/backend/lowering/mir_to_rtl.spl`)
   - Extract scheduling information from MIR
   - Lower MIR types to RTL width semantics
   - Extract clock domains from `@clocked` decorators
   - Extract reset semantics from reset attributes
   - Build process sensitivity lists

3. **RTL IR Validation** (`src/compiler/70.backend/backend/rtl/rtl_validation.spl`)
   - Width consistency checking
   - Clock domain validity
   - Combinational loop detection
   - Reset priority validation
   - Parametric width constraint checking

**Deliverables:**
- RTL IR type system complete
- MIR → RTL IR lowering functional for basic modules
- Validation catches common hardware errors
- Test suite covers: types, widths, clocks, resets

### Phase 2: VhdlBackend Refactoring (Weeks 5-8)

**Goal:** Refactor VhdlBackend to consume RTL IR

1. **Extract VHDL-specific semantics from current backend**
   - Move scheduling logic to RTL IR layer
   - Move state representation to RTL IR layer
   - Move width semantics to RTL IR layer
   - Keep VHDL-specific syntax/emission in backend

2. **Create RTL IR → VHDL lowering**
   - `src/compiler/70.backend/backend/vhdl/rtl_to_vhdl.spl`
   - Lower RtlModule to VHDL library/package structure
   - Lower RtlEntity to VHDL entity/architecture
   - Lower RtlProcess to VHDL process
   - Lower RtlState to VHDL signals/variables

3. **Update VhdlBackend**
   - Change `compile()` to call `mir_to_rtl_lowering()` first
   - Implement `compile_rtl_module()` as primary compilation path
   - Keep legacy `Codegen` implementation for compatibility

4. **VHDL-specific features**
   - Implement VHDL-2008 type system mapping
   - Handle VHDL record/array emission
   - Handle VHDL package emission
   - Handle VHDL testbench generation

**Deliverables:**
- VhdlBackend refactored to RTL IR path
- All existing VHDL tests pass via RTL IR
- VHDL-specific emission isolated in vhdl/ modules
- No VHDL semantics leak into RTL IR

### Phase 3: SystemVerilogBackend Implementation (Weeks 9-12)

**Goal:** Implement SystemVerilog backend using same RTL IR

1. **Create SystemVerilogBackend class**
   - `src/compiler/70.backend/backend/systemverilog_backend.spl`
   - Implement `Codegen` trait
   - Implement `HardwareCodegen` trait
   - Add `SystemVerilog` to `BackendKind` enum

2. **RTL IR → SystemVerilog lowering**
   - `src/compiler/70.backend/backend/systemverilog/rtl_to_systemverilog.spl`
   - Lower RtlModule to SystemVerilog module/package
   - Lower RtlEntity to SystemVerilog module
   - Lower RtlProcess to SystemVerilog always_comb/always_ff
   - Lower RtlState to SystemVerilog logic/variables

3. **SystemVerilog-specific features**
   - Implement SystemVerilog-2017 type system
   - Handle SystemVerilog structs/enums/unions
   - Handle SystemVerilog interfaces
   - Handle SystemVerilog packages
   - Handle SystemVerilog arrays and queues

4. **Type mapping**
   - `src/compiler/70.backend/backend/systemverilog/systemverilog_type_mapper.spl`
   - Map RTL width to SystemVerilog bit widths
   - Map RTL parametric types to SystemVerilog parameters
   - Handle SystemVerilog signed/unsigned semantics

**Deliverables:**
- SystemVerilogBackend complete
- RTL IR → SystemVerilog emission functional
- SystemVerilog tests match VHDL tests
- SystemVerilog-specific features documented

### Phase 4: AOP Integration & Source-Subset Path Removal (Weeks 13-14)

**Goal:** Integrate AOP with RTL IR and remove COMPILER-002 risk

1. **AOP weaving at RTL IR level**
   - Weave AOP advice after MIR → RTL IR lowering
   - Support AOP for RtlProcess, RtlState, RtlConcurrent
   - Provide AOP hooks for clock domains, resets, state

2. **Deprecate source-subset emitter**
   - Mark `driver_compile_vhdl_codegen.spl` functions as deprecated
   - Update documentation to recommend full pipeline
   - Add warnings when source-subset path is used
   - Provide migration guide for users

3. **AOP validation**
   - Verify AOP weaves correctly on both backends
   - Test AOP with scheduling/state/width semantics
   - Ensure AOP doesn't break cross-backend equivalence

**Deliverables:**
- AOP fully integrated with RTL IR
- Source-subset path deprecated with clear migration path
- AOP tests pass on both VHDL and SystemVerilog
- COMPILER-002 risk eliminated

### Phase 5: Cross-Backend Equivalence Testing (Weeks 15-16)

**Goal:** Establish equivalence testing between VHDL and SystemVerilog

1. **Verilator integration**
   - `test/compiler/rtl_backend/verilator_equivalence.spl`
   - Compile SystemVerilog output with Verilator
   - Run simulation tests
   - Compare against VHDL simulation results

2. **Equivalence test suite**
   - `test/compiler/rtl_backend/equivalence/`
   - Basic logic tests (gates, muxes, arithmetic)
   - State element tests (registers, latches, memories)
   - Clock domain tests (single/multi-clock)
   - Reset tests (sync/async, polarity)
   - Width tests (parametric, fixed)
   - Scheduling tests (process ordering, combinational loops)

3. **Test automation**
   - Emit both VHDL and SystemVerilog for each test
   - Run VHDL simulation (GHDL or commercial simulator)
   - Run SystemVerilog simulation (Verilator or commercial simulator)
   - Compare outputs for equivalence
   - Report mismatches with diagnostics

4. **Continuous integration**
   - Add equivalence tests to CI
   - Fail PR if VHDL/SystemVerilog outputs differ
   - Track equivalence coverage metrics
   - Automate Verilator regression testing

**Deliverables:**
- Verilator integrated into test pipeline
- Comprehensive equivalence test suite
- CI enforces cross-backend equivalence
- Equivalence failures caught before merge

---

## Verification Strategy

### Cross-Backend Equivalence Tests

**Purpose:** Ensure VHDL and SystemVerilog backends produce functionally equivalent hardware

#### Test Structure

```simple
# Equivalence test framework

struct EquivalenceTest:
    name: text
    source_mir: MirModule
    expected_behavior: TestBehavior
    vhdl_output: text
    systemverilog_output: text
    simulation_results: SimulationResults

enum TestBehavior:
    CombinationalTruthTable(inputs: [TestVector], outputs: [TestVector])
    SequentialStateSequence(cycles: [TestCycle])
    ClockDomainTransition(clocks: [ClockEdge])
    ResetBehavior(reset_cycles: [ResetCycle])
```

#### Test Categories

1. **Type/Width Equivalence**
   - Parametric widths (XLEN, generics)
   - Fixed widths (8, 16, 32, 64 bits)
   - Signed/unsigned variants
   - Array/record widths

2. **Combinational Logic**
   - Basic gates (AND, OR, XOR, NOT)
   - Arithmetic (ADD, SUB, MUL, DIV)
   - Comparisons (LT, EQ, GT)
   - Multiplexers (2-way, N-way)
   - Truth table verification

3. **Sequential Logic**
   - Registers (DFF, JKFF, TFF)
   - Latches
   - Register files
   - State machines
   - Cycle-accurate behavior

4. **Clock Domains**
   - Single-clock designs
   - Multi-clock designs
   - Clock crossing
   - Clock gating
   - Rising/falling edge

5. **Reset Semantics**
   - Synchronous reset
   - Asynchronous reset
   - Active-high reset
   - Active-low reset
   - Reset priority

6. **Scheduling**
   - Process ordering
   - Concurrent assignments
   - Combinational loops (detection)
   - Priority levels

#### Verilator-Oriented Verification

```simple
# Verilator verification pipeline

fn verilator_equivalence_test(test: EquivalenceTest) -> bool:
    """Run Verilator on SystemVerilog output and compare to VHDL."""
    
    # 1. Emit SystemVerilog
    val sv_backend = SystemVerilogBackend.create()
    val sv_result = sv_backend.compile_rtl_module(test.source_rtl)
    if sv_result.is_err():
        return false
    
    # 2. Run Verilator
    val verilator_cmd = "verilator --binary -cc {sv_output} --top {module_name}"
    val sim_result = run_command(verilator_cmd)
    if sim_result.rc != 0:
        return false
    
    # 3. Run simulation
    val sim_output = run_command("./V{module_name}")
    
    # 4. Compare to VHDL reference
    val vhdl_sim_result = run_ghdl_simulation(test.vhdl_output)
    return sim_output == vhdl_sim_result
```

#### Simulation Comparison

```simple
# VHDL simulation (GHDL or commercial)

fn run_ghdl_simulation(vhdl_code: text, test_vectors: [TestVector]) -> SimulationResults:
    """Run GHDL simulation and capture outputs."""
    # ... GHDL execution ...
    # ... capture waveform/state ...

# SystemVerilog simulation (Verilator)

fn run_verilator_simulation(sv_code: text, test_vectors: [TestVector]) -> SimulationResults:
    """Run Verilator simulation and capture outputs."""
    # ... Verilator compilation ...
    # ... testbench execution ...
    # ... capture waveform/state ...

# Equivalence check

fn compare_simulation_results(vhdl: SimulationResults, sv: SimulationResults) -> EquivalenceReport:
    """Compare simulation results for equivalence."""
    var mismatches: [Mismatch] = []
    
    # Compare final state
    for signal in vhdl.final_state.keys():
        if vhdl.final_state[signal] != sv.final_state[signal]:
            mismatches = mismatches.push(Mismatch(
                signal: signal,
                vhdl_value: vhdl.final_state[signal],
                sv_value: sv.final_state[signal],
                kind: MismatchKind.StateMismatch
            ))
    
    # Compare timing
    if vhdl.cycle_count != sv.cycle_count:
        mismatches = mismatches.push(Mismatch(
            signal: "cycle_count",
            vhdl_value: vhdl.cycle_count.to_text(),
            sv_value: sv.cycle_count.to_text(),
            kind: MismatchKind.TimingMismatch
        ))
    
    EquivalenceReport(is_equivalent: mismatches.len() == 0, mismatches: mismatches)
```

### Regression Testing

**Purpose:** Catch backend bugs and divergences early

1. **Nightly Equivalence Runs**
   - Full test suite on both backends
   - Report any new failures
   - Track equivalence coverage

2. **Per-Commit Validation**
   - Quick smoke tests on each commit
   - Catch basic syntax/type errors
   - Fast feedback for developers

3. **Release Gates**
   - Full equivalence verification before release
   - Verilator regression suite
   - Commercial simulator verification (if available)

---

## Impact Assessment

### Files Modified/Created

#### Modified (Existing)
- `src/compiler/70.backend/backend/backend_types.spl` — Add `SystemVerilog` to `BackendKind`
- `src/compiler/70.backend/backend/hardware_codegen_types.spl` — Enhance `HardwareCodegen` trait
- `src/compiler/70.backend/backend/vhdl_backend.spl` — Refactor to RTL IR
- `src/compiler/70.backend/backend/vhdl/*.spl` — Adapt to RTL IR input
- `src/compiler/80.driver/driver_compile_vhdl_codegen.spl` — Deprecate source-subset path

#### Created (New)

**RTL IR Layer:**
- `src/compiler/70.backend/backend/rtl/rtl_types.spl`
- `src/compiler/70.backend/backend/rtl/rtl_operations.spl`
- `src/compiler/70.backend/backend/rtl/rtl_state.spl`
- `src/compiler/70.backend/backend/rtl/rtl_schedule.spl`
- `src/compiler/70.backend/backend/rtl/rtl_metadata.spl`
- `src/compiler/70.backend/backend/rtl/rtl_validation.spl`

**Lowering:**
- `src/compiler/70.backend/backend/lowering/mir_to_rtl.spl`

**SystemVerilog Backend:**
- `src/compiler/70.backend/backend/systemverilog_backend.spl`
- `src/compiler/70.backend/backend/systemverilog/rtl_to_systemverilog.spl`
- `src/compiler/70.backend/backend/systemverilog/systemverilog_type_mapper.spl`
- `src/compiler/70.backend/backend/systemverilog/systemverilog_builder.spl`
- `src/compiler/70.backend/backend/systemverilog/systemverilog_validation.spl`

**VHDL Refactoring:**
- `src/compiler/70.backend/backend/vhdl/rtl_to_vhdl.spl`

**Testing:**
- `test/compiler/rtl_backend/equivalence/basic_logic.spl`
- `test/compiler/rtl_backend/equivalence/state_elements.spl`
- `test/compiler/rtl_backend/equivalence/clock_domains.spl`
- `test/compiler/rtl_backend/equivalence/resets.spl`
- `test/compiler/rtl_backend/equivalence/widths.spl`
- `test/compiler/rtl_backend/equivalence/scheduling.spl`
- `test/compiler/rtl_backend/verilator_equivalence.spl`

### Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| RTL IR design insufficient for complex hardware | High | Prototyping with RISC-V cores early, iterative refinement |
| VHDL backend performance degrades | Medium | Benchmark current performance, optimize RTL IR lowering |
| SystemVerilog backend incomplete/delayed | Medium | Incremental rollout, feature flags, gradual migration |
| AOP integration breaks existing workflows | High | Extensive AOP testing, gradual deprecation of source-subset path |
| Verilator integration fails in CI | Low | Docker container with Verilator, fallback to simulation-only tests |
| Cross-backend equivalence too strict | Medium | Allow documented differences (e.g., X propagation), equivalence guidelines |

### Success Criteria

1. **RTL IR Layer:**
   - ✅ All MIR features lower to RTL IR
   - ✅ Validation catches hardware errors before backend emission
   - ✅ Scheduling/state/width semantics properly represented

2. **VHDL Backend:**
   - ✅ All existing VHDL tests pass via RTL IR
   - ✅ No regression in emitted VHDL quality
   - ✅ VHDL-specific features fully supported

3. **SystemVerilog Backend:**
   - ✅ SystemVerilog-2017 emission functional
   - ✅ All basic RTL IR constructs supported
   - ✅ SystemVerilog-specific features documented

4. **Cross-Backend Equivalence:**
   - ✅ 95%+ test equivalence between VHDL and SystemVerilog
   - ✅ Verilator integrated into CI
   - ✅ Equivalence failures block PRs

5. **AOP Integration:**
   - ✅ AOP weaves correctly on both backends
   - ✅ Source-subset path deprecated
   - ✅ COMPILER-002 risk eliminated

---

## Open Questions

1. **RTL IR Granularity:**
   - Should RTL IR be at the entity level or module level?
   - How to handle hierarchical module instantiation?
   - Should interfaces be first-class in RTL IR?

2. **Scheduling Semantics:**
   - How much scheduling information should be in RTL IR?
   - Should we support user-defined process priorities?
   - How to represent don't-care/X state in scheduling?

3. **Parametric Widths:**
   - How to validate parametric widths before backend emission?
   - Should RTL IR support width constraints?
   - How to represent dependent parameters?

4. **Testing:**
   - What's the minimum Verilator version required?
   - Should we support commercial simulators for verification?
   - How to handle simulator-specific pragmas/directives?

5. **Migration:**
   - Should users migrate to SystemVerilog gradually or all-at-once?
   - How to handle VHDL-specific code that has no SystemVerilog equivalent?
   - Should we provide VHDL→SystemVerilog translation tools?

---

## Next Steps (After Plan Approval)

1. **Prototyping:** Implement basic RTL IR types and MIR→RTL lowering for a simple module
2. **VHDL Refactoring:** Refactor VhdlBackend to use RTL IR for basic modules
3. **SystemVerilog Proof-of-Concept:** Implement basic SystemVerilog emission
4. **Equivalence Testing:** Set up Verilator and run first equivalence tests
5. **Iteration:** Refine RTL IR based on real-world usage with RISC-V cores

---

## References

- BUG-RTL-001: RISC-V RTL audit finding
- COMPILER-002: AOP bypass in VHDL source-subset path
- Current VHDL backend: `src/compiler/70.backend/backend/vhdl_backend.spl`
- Current VHDL source-subset emitter: `src/compiler/80.driver/driver_compile_vhdl_codegen.spl`
- Backend interface: `src/compiler/70.backend/backend/hardware_codegen_types.spl`
- Backend types: `src/compiler/70.backend/backend/backend_types.spl`
- Verilator documentation: https://verilator.org/guide/latest/
- SystemVerilog standard: IEEE Std 1800-2017
- VHDL standard: IEEE Std 1076-2008

---

**Plan Status:** DRAFT — Awaiting review and approval  
**Estimated Timeline:** 16 weeks (4 months)  
**Priority:** P1 (per BUG-RTL-001 audit)  
**Blockers:** None identified  
**Dependencies:** None (can proceed in parallel with other work)
