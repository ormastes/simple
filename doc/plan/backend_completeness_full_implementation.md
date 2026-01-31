# Backend Instruction Completeness - Full Implementation Plan (All Phases)

**Date:** 2026-01-31
**Status:** Planning
**Scope:** Complete implementation of all 4 phases with intensive SSpec verification
**Strategy:** Simple-first implementation, Rust FFI integration where needed

---

## Executive Summary

This plan implements comprehensive backend instruction completeness verification across all 4 phases:
- **Phase 1:** Compile-time safety via exhaustive pattern matching (Rust)
- **Phase 2:** Runtime safety net via automated testing (SSpec)
- **Phase 3:** Documentation and capability tracking (Simple + auto-generation)
- **Phase 4:** DSL-based code generation (Simple DSL, generates Rust)

**Key Innovation:** Simple-first approach with intensive SSpec verification ensures correctness at language level, not just compiler level.

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│ Phase 4: DSL Layer (Simple)                                 │
│ - Instruction definitions in Simple                         │
│ - Generates Rust code for all backends                      │
└─────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────┐
│ Phase 3: Capability Tracking (Simple)                       │
│ - Backend feature matrix                                    │
│ - Auto-generated documentation                              │
└─────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────┐
│ Phase 2: Testing Infrastructure (SSpec)                     │
│ - Instruction coverage specs                                │
│ - Differential testing specs                                │
│ - Backend equivalence verification                          │
└─────────────────────────────────────────────────────────────┘
                           ↓
┌─────────────────────────────────────────────────────────────┐
│ Phase 1: Exhaustive Matching (Rust - Manual)                │
│ - Remove catch-all patterns                                 │
│ - Explicit error handling                                   │
│ - Compile-time enforcement                                  │
└─────────────────────────────────────────────────────────────┘
```

---

## Phase 1: Compile-Time Safety (Rust, ~8 hours)

### Goal
Make missing instruction implementations a **compile error**, not a runtime error.

### Implementation Files

#### Rust Files (Core Implementation)
1. `rust/compiler/src/codegen/llvm/functions.rs` - Remove catch-all at line 393
2. `rust/compiler/src/codegen/vulkan/spirv_instructions.rs` - Remove catch-all at line 154
3. `rust/compiler/src/codegen/llvm/mod.rs` - Add exhaustiveness lints
4. `rust/compiler/src/codegen/vulkan/mod.rs` - Add exhaustiveness lints

#### Simple Files (High-level orchestration)
5. `src/compiler/backend/completeness_checker.spl` - NEW
   - Validates backend implementations
   - Reports missing implementations
   - Generates error messages

### Tasks

#### Task 1.1: Audit Current State
**File:** `scripts/audit_backend_catchalls.spl` (NEW)
```simple
# Backend catch-all pattern auditor
fn audit_catchalls() -> AuditReport:
    val files = [
        "rust/compiler/src/codegen/llvm/functions.rs",
        "rust/compiler/src/codegen/vulkan/spirv_instructions.rs"
    ]

    val patterns = []
    for file in files:
        val content = File.read(file)
        val matches = Regex.find_all(r'_ =>', content)
        patterns.extend(matches.map(\m: (file, m.line, m.column)))

    AuditReport(
        total_catchalls: patterns.len,
        locations: patterns,
        severity: if patterns.len > 0: "CRITICAL" else: "OK"
    )
```

**Deliverable:** `doc/audit/catchall_audit_2026-01-31.txt`

#### Task 1.2: Remove LLVM Catch-Alls
**File:** `rust/compiler/src/codegen/llvm/functions.rs`

**Change:**
```rust
// BEFORE (line 393-395):
_ => {
    // Other instructions not yet implemented
}

// AFTER: Exhaustive listing
MirInst::VecShuffle { .. } | MirInst::VecBlend { .. } | MirInst::VecSelect { .. }
| MirInst::VecLoad { .. } | MirInst::VecStore { .. } | MirInst::VecGather { .. }
| MirInst::VecScatter { .. } | MirInst::VecFma { .. } | MirInst::VecRecip { .. }
| MirInst::VecMaskedLoad { .. } | MirInst::VecMaskedStore { .. }
| MirInst::VecMinVec { .. } | MirInst::VecMaxVec { .. } | MirInst::VecClamp { .. }
| MirInst::NeighborLoad { .. }
=> {
    Err(CompileError::unsupported(format!(
        "LLVM backend does not support SIMD instruction: {:?}. Use Cranelift backend for SIMD.",
        inst
    )))
}

MirInst::ActorSpawn { .. } | MirInst::ActorSend { .. } | MirInst::ActorRecv { .. }
| MirInst::ActorJoin { .. } | MirInst::ActorReply { .. }
| MirInst::GeneratorCreate { .. } | MirInst::Yield { .. } | MirInst::GeneratorNext { .. }
| MirInst::FutureCreate { .. } | MirInst::Await { .. }
=> {
    Err(CompileError::unsupported(format!(
        "LLVM backend does not support concurrency instruction: {:?}. Use interpreter or Cranelift.",
        inst
    )))
}

// ... list ALL remaining unsupported instructions with clear categories
```

#### Task 1.3: Remove Vulkan Catch-Alls
**File:** `rust/compiler/src/codegen/vulkan/spirv_instructions.rs`

**Change:**
```rust
// AFTER: Exhaustive listing with clear categories
// CPU-only instructions (not supported in GPU kernels)
MirInst::Call { .. } | MirInst::InterpCall { .. }
| MirInst::GcAlloc { .. } | MirInst::Wait { .. }
| MirInst::ActorSpawn { .. } | MirInst::ActorSend { .. }
// ... (all CPU-only instructions)
=> {
    Err(CompileError::unsupported(format!(
        "Vulkan GPU kernels do not support CPU-only instruction: {:?}",
        inst
    )))
}

// I/O instructions (not supported in GPU kernels)
MirInst::ConstString { .. } | MirInst::FStringFormat { .. }
| MirInst::DictLit { .. } | MirInst::ArrayLit { .. }
// ... (all I/O instructions)
=> {
    Err(CompileError::unsupported(format!(
        "Vulkan GPU kernels do not support I/O instruction: {:?}",
        inst
    )))
}
```

#### Task 1.4: Add Exhaustiveness Lints
**Files:**
- `rust/compiler/src/codegen/llvm/mod.rs`
- `rust/compiler/src/codegen/vulkan/mod.rs`

**Add to top of each:**
```rust
#![deny(unreachable_patterns)]
#![warn(clippy::wildcard_enum_match_arm)]
```

#### Task 1.5: Simple Validation Tool
**File:** `src/compiler/backend/exhaustiveness_validator.spl` (NEW)
```simple
# Validates that all backends have exhaustive pattern matching
class ExhaustivenessValidator:
    backend_files: Dict<text, text>

    static fn new() -> ExhaustivenessValidator:
        ExhaustivenessValidator(
            backend_files: {
                "cranelift": "rust/compiler/src/codegen/instr/mod.rs",
                "llvm": "rust/compiler/src/codegen/llvm/functions.rs",
                "vulkan": "rust/compiler/src/codegen/vulkan/spirv_instructions.rs"
            }
        )

    fn validate_all() -> ValidationReport:
        val results = {}
        for (backend, file) in self.backend_files:
            results[backend] = self.validate_backend(file)

        ValidationReport(
            backends: results,
            all_exhaustive: results.values.all(\r: r.is_exhaustive)
        )

    fn validate_backend(file: text) -> BackendValidation:
        val content = File.read(file)
        val has_catchall = content.contains("_ =>")
        val has_lint = content.contains("#![deny(unreachable_patterns)]")

        BackendValidation(
            is_exhaustive: not has_catchall and has_lint,
            has_catchall: has_catchall,
            has_lint: has_lint,
            file: file
        )
```

**SSpec Test:** `test/compiler/backend/exhaustiveness_validator_spec.spl` (NEW)
```simple
describe "ExhaustivenessValidator":
    it "detects catch-all patterns in LLVM backend":
        val validator = ExhaustivenessValidator.new()
        val before_fix = validator.validate_backend(
            "rust/compiler/src/codegen/llvm/functions.rs"
        )

        # This test will FAIL until Phase 1 is complete
        expect(before_fix.has_catchall).to_be(false)
        expect(before_fix.has_lint).to_be(true)

    it "validates all backends are exhaustive":
        val validator = ExhaustivenessValidator.new()
        val report = validator.validate_all()

        expect(report.all_exhaustive).to_be(true)
        for (backend, validation) in report.backends:
            expect(validation.is_exhaustive).to_be(true)
                .with_message("Backend {backend} must be exhaustive")
```

### Success Criteria (Phase 1)
- [ ] Zero `_ => {}` patterns in LLVM backend instruction lowering
- [ ] Zero `_ => {}` patterns in Vulkan backend instruction lowering
- [ ] Exhaustiveness lints added and enabled
- [ ] All unsupported instructions return explicit `CompileError::unsupported`
- [ ] SSpec test `exhaustiveness_validator_spec.spl` passes
- [ ] Adding new `MirInst` variant causes compilation to fail

---

## Phase 2: Runtime Safety Net (SSpec, ~24 hours)

### Goal
Comprehensive testing to catch semantic bugs and missing implementations at runtime.

### Implementation Strategy

**Simple-First:** All testing infrastructure in Simple with SSpec framework.

### Files to Create

#### Simple Test Infrastructure
1. `test/compiler/backend/instruction_coverage_spec.spl` - Coverage tests
2. `test/compiler/backend/differential_testing_spec.spl` - Backend equivalence
3. `test/compiler/backend/cranelift_coverage_spec.spl` - Cranelift reference
4. `test/compiler/backend/llvm_coverage_spec.spl` - LLVM coverage
5. `test/compiler/backend/vulkan_coverage_spec.spl` - Vulkan coverage
6. `src/compiler/backend/test_generator.spl` - Test case generator
7. `src/compiler/backend/mir_test_builder.spl` - MIR test utilities

### Task 2.1: MIR Test Builder (Simple)
**File:** `src/compiler/backend/mir_test_builder.spl` (NEW)
```simple
# Programmatically build MIR test cases for backend testing
class MirTestBuilder:
    instructions: [MirInst]

    static fn new() -> MirTestBuilder:
        MirTestBuilder(instructions: [])

    me add_const_int(dest: i32, value: i64) -> MirTestBuilder:
        self.instructions.push(MirInst.ConstInt(dest: VReg(dest), value: value))
        self

    me add_binop(dest: i32, op: BinOp, left: i32, right: i32) -> MirTestBuilder:
        self.instructions.push(MirInst.BinOp(
            dest: VReg(dest),
            op: op,
            left: VReg(left),
            right: VReg(right)
        ))
        self

    fn build() -> MirFunction:
        MirFunction(
            name: "test_function",
            params: [],
            return_type: TypeId.I64,
            blocks: [
                MirBlock(
                    id: BlockId(0),
                    instructions: self.instructions,
                    terminator: Terminator.Return(VReg(0))
                )
            ]
        )

    # Generate test case for EVERY MirInst variant
    static fn all_instruction_tests() -> [MirFunction]:
        [
            # Constants
            MirTestBuilder.new()
                .add_const_int(0, 42)
                .build(),

            MirTestBuilder.new()
                .add_const_float(0, 3.14)
                .build(),

            # Arithmetic
            MirTestBuilder.new()
                .add_const_int(1, 10)
                .add_const_int(2, 20)
                .add_binop(0, BinOp.Add, 1, 2)
                .build(),

            # ... generate test for ALL 80+ instruction types
        ]
```

### Task 2.2: Instruction Coverage Tests (SSpec)
**File:** `test/compiler/backend/instruction_coverage_spec.spl` (NEW)
```simple
describe "Backend Instruction Coverage":
    describe "Cranelift backend (reference implementation)":
        it "handles all MirInst variants":
            val test_cases = MirTestBuilder.all_instruction_tests()
            val backend = Backend.cranelift()

            for test in test_cases:
                val result = backend.compile(test)
                expect(result.is_ok).to_be(true)
                    .with_message("Cranelift must support: {test.name}")

    describe "LLVM backend":
        it "handles supported instructions":
            val supported_tests = MirTestBuilder.llvm_supported_tests()
            val backend = Backend.llvm()

            for test in supported_tests:
                val result = backend.compile(test)
                expect(result.is_ok).to_be(true)
                    .with_message("LLVM should support: {test.name}")

        it "rejects unsupported instructions with clear errors":
            val unsupported_tests = MirTestBuilder.llvm_unsupported_tests()
            val backend = Backend.llvm()

            for test in unsupported_tests:
                val result = backend.compile(test)
                expect(result.is_err).to_be(true)
                expect(result.err.unwrap.is_unsupported).to_be(true)
                    .with_message("LLVM must reject: {test.name}")

        it "provides helpful error messages for unsupported features":
            val test = MirTestBuilder.new()
                .add_gpu_barrier()
                .build()

            val result = Backend.llvm().compile(test)
            expect(result.is_err).to_be(true)

            val error_msg = result.err.unwrap.message
            expect(error_msg).to_contain("GPU")
            expect(error_msg).to_contain("not supported")
            expect(error_msg).to_contain("Cranelift")  # Suggests alternative

    describe "Vulkan backend":
        it "handles GPU-specific instructions":
            val gpu_tests = MirTestBuilder.vulkan_supported_tests()
            val backend = Backend.vulkan()

            for test in gpu_tests:
                val result = backend.compile(test)
                expect(result.is_ok).to_be(true)
                    .with_message("Vulkan must support: {test.name}")

        it "rejects CPU-only instructions":
            val cpu_tests = MirTestBuilder.vulkan_unsupported_tests()
            val backend = Backend.vulkan()

            for test in cpu_tests:
                val result = backend.compile(test)
                expect(result.is_err).to_be(true)
                expect(result.err.unwrap.message).to_contain("GPU kernel")
```

### Task 2.3: Differential Testing (SSpec)
**File:** `test/compiler/backend/differential_testing_spec.spl` (NEW)
```simple
describe "Backend Differential Testing":
    describe "Cranelift vs LLVM equivalence":
        it "produces equivalent output for arithmetic operations":
            val program = MirTestBuilder.new()
                .add_const_int(1, 10)
                .add_const_int(2, 20)
                .add_binop(3, BinOp.Add, 1, 2)
                .add_binop(0, BinOp.Mul, 3, VReg.constant(2))
                .build()

            val cranelift_result = Backend.cranelift().compile_and_run(program, [])
            val llvm_result = Backend.llvm().compile_and_run(program, [])

            expect(cranelift_result).to_equal(llvm_result)
                .with_message("Cranelift and LLVM must produce same result")

        slow_it "handles complex control flow identically":
            val program = MirTestBuilder.build_fibonacci(20)

            val cranelift_result = Backend.cranelift().compile_and_run(program, [20])
            val llvm_result = Backend.llvm().compile_and_run(program, [20])

            expect(cranelift_result).to_equal(llvm_result)
            expect(cranelift_result).to_equal(6765)  # fib(20)

    describe "Backend performance characteristics":
        slow_it "Cranelift compiles faster than LLVM":
            val program = MirTestBuilder.build_large_program(1000)

            val cranelift_time = measure_time:
                Backend.cranelift().compile(program)

            val llvm_time = measure_time:
                Backend.llvm().compile(program)

            expect(cranelift_time).to_be_less_than(llvm_time)
                .with_message("Cranelift should compile faster")

        slow_it "LLVM produces faster runtime code":
            val program = MirTestBuilder.build_compute_intensive()

            val cranelift_runtime = measure_runtime:
                Backend.cranelift().compile_and_run(program, [])

            val llvm_runtime = measure_runtime:
                Backend.llvm().compile_and_run(program, [])

            # LLVM typically produces faster code (but may not always)
            # This is informational, not a strict requirement
            print("Cranelift runtime: {cranelift_runtime}ms")
            print("LLVM runtime: {llvm_runtime}ms")
```

### Task 2.4: Backend Test Generator (Simple)
**File:** `src/compiler/backend/test_generator.spl` (NEW)
```simple
# Auto-generates test cases for all instruction categories
class BackendTestGenerator:

    # Generate tests for all constant instructions
    static fn constant_tests() -> [TestCase]:
        [
            TestCase(
                name: "ConstInt positive",
                mir: MirTestBuilder.new().add_const_int(0, 42).build(),
                expected_backends: ["cranelift", "llvm", "vulkan"]
            ),
            TestCase(
                name: "ConstInt negative",
                mir: MirTestBuilder.new().add_const_int(0, -42).build(),
                expected_backends: ["cranelift", "llvm", "vulkan"]
            ),
            TestCase(
                name: "ConstFloat",
                mir: MirTestBuilder.new().add_const_float(0, 3.14).build(),
                expected_backends: ["cranelift", "llvm", "vulkan"]
            ),
            # ... all constant types
        ]

    # Generate tests for all arithmetic operations
    static fn arithmetic_tests() -> [TestCase]:
        val ops = [BinOp.Add, BinOp.Sub, BinOp.Mul, BinOp.Div,
                   BinOp.Mod, BinOp.Pow]

        ops.map(\op:
            TestCase(
                name: "BinOp {op}",
                mir: MirTestBuilder.new()
                    .add_const_int(1, 10)
                    .add_const_int(2, 3)
                    .add_binop(0, op, 1, 2)
                    .build(),
                expected_backends: if op == BinOp.Pow:
                    ["cranelift"]  # Power not supported in LLVM yet
                else:
                    ["cranelift", "llvm"]
            )
        )

    # Generate tests for GPU instructions
    static fn gpu_tests() -> [TestCase]:
        [
            TestCase(
                name: "GpuGlobalId",
                mir: MirTestBuilder.new().add_gpu_global_id(0, 0).build(),
                expected_backends: ["vulkan"]  # GPU-only
            ),
            TestCase(
                name: "GpuBarrier",
                mir: MirTestBuilder.new().add_gpu_barrier().build(),
                expected_backends: ["vulkan"]
            ),
            # ... all GPU instructions
        ]

    # Generate comprehensive test suite
    static fn all_tests() -> [TestCase]:
        [
            ...self.constant_tests(),
            ...self.arithmetic_tests(),
            ...self.memory_tests(),
            ...self.control_flow_tests(),
            ...self.gpu_tests(),
            ...self.simd_tests(),
            ...self.concurrency_tests()
        ]
```

### Success Criteria (Phase 2)
- [ ] All 80+ `MirInst` variants have test cases
- [ ] All 3 backends (Cranelift, LLVM, Vulkan) tested
- [ ] Differential testing passes for supported instructions
- [ ] Clear categorization of supported/unsupported per backend
- [ ] All SSpec tests in `test/compiler/backend/` pass
- [ ] CI integration complete (tests run on every commit)

---

## Phase 3: Documentation & Tracking (Simple, ~16 hours)

### Goal
Auto-generate and maintain backend capability documentation.

### Implementation Files

#### Simple Documentation Tools
1. `src/compiler/backend/capability_tracker.spl` - Track what each backend supports
2. `src/compiler/backend/doc_generator.spl` - Generate markdown documentation
3. `src/compiler/backend/matrix_builder.spl` - Build support matrix
4. `scripts/generate_backend_docs.spl` - CLI tool for doc generation

### Task 3.1: Backend Capability Tracker
**File:** `src/compiler/backend/capability_tracker.spl` (NEW)
```simple
# Tracks which backends support which instructions
class BackendCapabilities:
    backend_name: text
    supports_gpu: bool
    supports_simd: bool
    supports_32bit: bool
    instruction_support: Dict<text, InstructionSupport>

    static fn for_cranelift() -> BackendCapabilities:
        BackendCapabilities(
            backend_name: "Cranelift",
            supports_gpu: false,
            supports_simd: true,
            supports_32bit: false,
            instruction_support: self.detect_cranelift_support()
        )

    static fn for_llvm() -> BackendCapabilities:
        BackendCapabilities(
            backend_name: "LLVM",
            supports_gpu: false,
            supports_simd: false,  # Not yet implemented
            supports_32bit: true,
            instruction_support: self.detect_llvm_support()
        )

    static fn for_vulkan() -> BackendCapabilities:
        BackendCapabilities(
            backend_name: "Vulkan",
            supports_gpu: true,
            supports_simd: false,
            supports_32bit: false,
            instruction_support: self.detect_vulkan_support()
        )

    # Automatically detect support by analyzing backend code
    static fn detect_cranelift_support() -> Dict<text, InstructionSupport>:
        val file = "rust/compiler/src/codegen/instr/mod.rs"
        val content = File.read(file)

        val support = {}
        for inst_name in MirInst.all_variant_names():
            # Check if instruction appears in match arm (not in unsupported list)
            val is_supported = content.contains("MirInst::{inst_name} {")
            support[inst_name] = if is_supported:
                InstructionSupport.Supported
            else:
                InstructionSupport.Unsupported("Not implemented in Cranelift")

        support

    fn to_markdown() -> text:
        val lines = [
            "# {self.backend_name} Backend Capabilities",
            "",
            "## Overview",
            "- **GPU Support:** {self.supports_gpu}",
            "- **SIMD Support:** {self.supports_simd}",
            "- **32-bit Support:** {self.supports_32bit}",
            "",
            "## Instruction Support",
            ""
        ]

        for (inst, support) in self.instruction_support.sorted_by_key():
            val status = match support:
                InstructionSupport.Supported: "✅"
                InstructionSupport.Unsupported(_): "❌"
                InstructionSupport.Partial(_): "⚠️"

            lines.push("- {status} `{inst}`: {support.message}")

        lines.join("\n")

enum InstructionSupport:
    Supported
    Unsupported(reason: text)
    Partial(reason: text)

    fn message() -> text:
        match self:
            Supported: "Fully supported"
            Unsupported(r): r
            Partial(r): r
```

### Task 3.2: Backend Support Matrix Generator
**File:** `src/compiler/backend/matrix_builder.spl` (NEW)
```simple
# Generates comparison matrix across all backends
class BackendMatrixBuilder:
    backends: [BackendCapabilities]

    static fn new() -> BackendMatrixBuilder:
        BackendMatrixBuilder(backends: [
            BackendCapabilities.for_cranelift(),
            BackendCapabilities.for_llvm(),
            BackendCapabilities.for_vulkan()
        ])

    fn build_matrix() -> BackendMatrix:
        val all_instructions = MirInst.all_variant_names()
        val rows = []

        for inst in all_instructions:
            val row = InstructionRow(
                instruction: inst,
                cranelift: self.get_support("Cranelift", inst),
                llvm: self.get_support("LLVM", inst),
                vulkan: self.get_support("Vulkan", inst),
                category: MirInst.category_for(inst)
            )
            rows.push(row)

        BackendMatrix(rows: rows)

    fn to_markdown() -> text:
        val matrix = self.build_matrix()

        val lines = [
            "# Backend Instruction Support Matrix",
            "",
            "| Instruction | Category | Cranelift | LLVM | Vulkan | Notes |",
            "|-------------|----------|-----------|------|--------|-------|"
        ]

        for row in matrix.rows.sorted_by(\r: r.category):
            val cl_icon = row.cranelift.icon()
            val llvm_icon = row.llvm.icon()
            val vk_icon = row.vulkan.icon()
            val notes = self.generate_notes(row)

            lines.push("| `{row.instruction}` | {row.category} | {cl_icon} | {llvm_icon} | {vk_icon} | {notes} |")

        lines.join("\n")

    fn generate_statistics() -> BackendStats:
        val matrix = self.build_matrix()

        BackendStats(
            total_instructions: matrix.rows.len,
            cranelift_supported: matrix.rows.count(\r: r.cranelift.is_supported),
            llvm_supported: matrix.rows.count(\r: r.llvm.is_supported),
            vulkan_supported: matrix.rows.count(\r: r.vulkan.is_supported),
            coverage_percentages: {
                "cranelift": (matrix.rows.count(\r: r.cranelift.is_supported) as f64 / matrix.rows.len as f64) * 100.0,
                "llvm": (matrix.rows.count(\r: r.llvm.is_supported) as f64 / matrix.rows.len as f64) * 100.0,
                "vulkan": (matrix.rows.count(\r: r.vulkan.is_supported) as f64 / matrix.rows.len as f64) * 100.0
            }
        )
```

### Task 3.3: Documentation Generator CLI
**File:** `scripts/generate_backend_docs.spl` (NEW)
```simple
# CLI tool to generate all backend documentation
fn main(args: [text]):
    val cmd = if args.len > 0: args[0] else: "all"

    match cmd:
        "matrix":
            generate_matrix()
        "capabilities":
            generate_capabilities()
        "stats":
            generate_stats()
        "all":
            generate_all()
        _:
            print("Usage: simple scripts/generate_backend_docs.spl [matrix|capabilities|stats|all]")

fn generate_matrix():
    print("Generating backend support matrix...")
    val builder = BackendMatrixBuilder.new()
    val markdown = builder.to_markdown()
    File.write("doc/backend/BACKEND_SUPPORT_MATRIX.md", markdown)
    print("✓ Generated doc/backend/BACKEND_SUPPORT_MATRIX.md")

fn generate_capabilities():
    print("Generating backend capability docs...")

    for backend in ["cranelift", "llvm", "vulkan"]:
        val caps = BackendCapabilities.for(backend)
        val markdown = caps.to_markdown()
        File.write("doc/backend/{backend}_capabilities.md", markdown)
        print("✓ Generated doc/backend/{backend}_capabilities.md")

fn generate_stats():
    print("Generating backend statistics...")
    val builder = BackendMatrixBuilder.new()
    val stats = builder.generate_statistics()

    print("")
    print("Backend Instruction Coverage:")
    print("  Total Instructions: {stats.total_instructions}")
    print("  Cranelift: {stats.cranelift_supported} ({stats.coverage_percentages['cranelift']:.1f}%)")
    print("  LLVM:      {stats.llvm_supported} ({stats.coverage_percentages['llvm']:.1f}%)")
    print("  Vulkan:    {stats.vulkan_supported} ({stats.coverage_percentages['vulkan']:.1f}%)")

    val json = stats.to_json()
    File.write("doc/backend/stats.json", json)
    print("✓ Generated doc/backend/stats.json")

fn generate_all():
    generate_matrix()
    generate_capabilities()
    generate_stats()
    print("")
    print("✓ All backend documentation generated!")
```

### Task 3.4: SSpec Verification for Phase 3
**File:** `test/compiler/backend/documentation_spec.spl` (NEW)
```simple
describe "Backend Documentation Generation":
    it "generates accurate support matrix":
        val builder = BackendMatrixBuilder.new()
        val matrix = builder.build_matrix()

        # Verify all instructions are included
        expect(matrix.rows.len).to_equal(MirInst.variant_count())

        # Verify known supported instructions
        val const_int_row = matrix.rows.find(\r: r.instruction == "ConstInt")
        expect(const_int_row.cranelift.is_supported).to_be(true)
        expect(const_int_row.llvm.is_supported).to_be(true)
        expect(const_int_row.vulkan.is_supported).to_be(true)

        # Verify known unsupported instructions
        val gpu_barrier_row = matrix.rows.find(\r: r.instruction == "GpuBarrier")
        expect(gpu_barrier_row.cranelift.is_supported).to_be(false)
        expect(gpu_barrier_row.llvm.is_supported).to_be(false)
        expect(gpu_barrier_row.vulkan.is_supported).to_be(true)

    it "calculates coverage statistics correctly":
        val builder = BackendMatrixBuilder.new()
        val stats = builder.generate_statistics()

        # Cranelift should have highest coverage (reference implementation)
        expect(stats.coverage_percentages["cranelift"]).to_be_greater_than(90.0)

        # All percentages should be 0-100
        for (_, pct) in stats.coverage_percentages:
            expect(pct).to_be_greater_than_or_equal(0.0)
            expect(pct).to_be_less_than_or_equal(100.0)

    it "generates valid markdown output":
        val builder = BackendMatrixBuilder.new()
        val markdown = builder.to_markdown()

        # Check structure
        expect(markdown).to_contain("# Backend Instruction Support Matrix")
        expect(markdown).to_contain("| Instruction | Category |")

        # Check all backends present
        expect(markdown).to_contain("Cranelift")
        expect(markdown).to_contain("LLVM")
        expect(markdown).to_contain("Vulkan")
```

### Success Criteria (Phase 3)
- [ ] Backend capability tracker implemented
- [ ] Support matrix auto-generation working
- [ ] Documentation CLI tool functional
- [ ] All generated docs in `doc/backend/` directory
- [ ] SSpec tests for doc generation pass
- [ ] Matrix stays in sync with code (automated)

---

## Phase 4: DSL-Based Code Generation (Simple DSL, ~40 hours)

### Goal
Reduce boilerplate and prevent missing implementations via declarative instruction definitions.

### Architecture

```
┌─────────────────────────────────┐
│ instructions.irdsl (Simple DSL) │
│ - Declarative instruction defs  │
│ - Per-backend lowering rules    │
└─────────────────────────────────┘
           ↓
┌─────────────────────────────────┐
│ irdsl_compiler.spl              │
│ - Parse DSL                     │
│ - Validate completeness         │
│ - Generate Rust code            │
└─────────────────────────────────┘
           ↓
┌─────────────────────────────────┐
│ Generated Rust Files            │
│ - mir/inst_enum.rs              │
│ - codegen/instr/mod.rs          │
│ - codegen/llvm/functions.rs    │
│ - codegen/vulkan/...            │
└─────────────────────────────────┘
```

### Task 4.1: Design IR DSL Syntax
**File:** `doc/design/ir_dsl_syntax.md` (NEW)
```markdown
# Simple IR DSL Syntax Design

## Instruction Definition

```irdsl
instruction ConstInt:
    fields:
        dest: VReg
        value: i64

    category: Constants

    effects: Pure

    backends:
        cranelift:
            code: |
                let val = builder.ins().iconst(types::I64, value);
                ctx.vreg_values.insert(dest, val);

        llvm:
            code: |
                let const_val = ctx.i64_type().const_int(value as u64, false);
                vreg_map.insert(dest, const_val.into());

        vulkan:
            code: |
                let i64_type = self.get_i64_type();
                let const_id = self.builder.constant_bit64(i64_type, value as u64);
                self.vreg_id_map.insert(dest, const_id);
```

## Unsupported Instructions

```irdsl
instruction GpuBarrier:
    fields: ()

    category: GPU

    effects: IO

    backends:
        cranelift:
            unsupported: "GPU intrinsics not supported by Cranelift. Use Vulkan backend."

        llvm:
            unsupported: "GPU intrinsics not supported by LLVM. Use Vulkan backend."

        vulkan:
            code: |
                use rspirv::spirv::{MemorySemantics, Scope};
                let scope = self.builder.constant_bit32(
                    self.get_u32_type(),
                    Scope::Workgroup as u32
                );
                let semantics = self.builder.constant_bit32(
                    self.get_u32_type(),
                    MemorySemantics::ACQUIRE_RELEASE.bits()
                );
                self.builder.control_barrier(scope, scope, semantics)?;
```
```

### Task 4.2: DSL Parser (Simple)
**File:** `src/compiler/irdsl/parser.spl` (NEW)
```simple
# Parser for IR DSL
class IrDslParser:
    source: text
    pos: i32

    static fn parse(source: text) -> IrDslAst:
        val parser = IrDslParser(source: source, pos: 0)
        parser.parse_module()

    fn parse_module() -> IrDslAst:
        val instructions = []

        while not self.is_at_end():
            self.skip_whitespace()
            if self.peek() == "instruction":
                instructions.push(self.parse_instruction())
            else:
                self.error("Expected 'instruction' keyword")

        IrDslAst(instructions: instructions)

    fn parse_instruction() -> InstructionDef:
        self.expect("instruction")
        val name = self.parse_identifier()
        self.expect(":")

        val fields = self.parse_fields()
        val category = self.parse_category()
        val effects = self.parse_effects()
        val backends = self.parse_backends()

        InstructionDef(
            name: name,
            fields: fields,
            category: category,
            effects: effects,
            backends: backends
        )

    fn parse_backends() -> Dict<text, BackendImpl>:
        self.expect("backends:")
        val backends = {}

        while self.peek() in ["cranelift", "llvm", "vulkan"]:
            val backend_name = self.parse_identifier()
            self.expect(":")

            if self.peek() == "code:":
                self.expect("code:")
                val code = self.parse_code_block()
                backends[backend_name] = BackendImpl.Code(code)
            elif self.peek() == "unsupported:":
                self.expect("unsupported:")
                val message = self.parse_string()
                backends[backend_name] = BackendImpl.Unsupported(message)

        backends
```

### Task 4.3: Code Generator (Simple)
**File:** `src/compiler/irdsl/codegen.spl` (NEW)
```simple
# Generates Rust code from IR DSL
class IrDslCodegen:
    ast: IrDslAst

    static fn generate(ast: IrDslAst) -> GeneratedCode:
        val codegen = IrDslCodegen(ast: ast)

        GeneratedCode(
            mir_enum: codegen.generate_mir_enum(),
            cranelift_impl: codegen.generate_cranelift_impl(),
            llvm_impl: codegen.generate_llvm_impl(),
            vulkan_impl: codegen.generate_vulkan_impl()
        )

    fn generate_mir_enum() -> text:
        val variants = self.ast.instructions.map(\inst:
            val fields = inst.fields.map(\f: "{f.name}: {f.ty}").join(", ")
            "    {inst.name} { {fields} },"
        )

        """
        #[derive(Debug, Clone, PartialEq)]
        pub enum MirInst {
        {variants.join("\n")}
        }
        """

    fn generate_cranelift_impl() -> text:
        val match_arms = self.ast.instructions.map(\inst:
            match inst.backends.get("cranelift"):
                Some(BackendImpl.Code(code)):
                    """
                    MirInst::{inst.name} { {inst.field_pattern()} } => {
                        {code}
                    }
                    """
                Some(BackendImpl.Unsupported(msg)):
                    """
                    MirInst::{inst.name} { .. } => {
                        return Err(CompileError::unsupported("{msg}"));
                    }
                    """
                None:
                    self.error("Cranelift backend missing for {inst.name}")
        )

        """
        pub fn compile_instruction<M: Module>(
            ctx: &mut InstrContext<'_, M>,
            builder: &mut FunctionBuilder,
            inst: &MirInst,
        ) -> InstrResult<()> {
            match inst {
        {match_arms.join("\n")}
            }
            Ok(())
        }
        """
```

### Task 4.4: Completeness Validator
**File:** `src/compiler/irdsl/validator.spl` (NEW)
```simple
# Validates that all backends handle all instructions
class IrDslValidator:
    ast: IrDslAst

    fn validate() -> ValidationResult:
        val errors = []

        # Check all instructions have all backends defined
        for inst in self.ast.instructions:
            for backend in ["cranelift", "llvm", "vulkan"]:
                if not inst.backends.contains_key(backend):
                    errors.push(ValidationError(
                        instruction: inst.name,
                        backend: backend,
                        message: "Missing backend implementation"
                    ))

        # Check no catch-all patterns (enforced by DSL structure)
        # DSL explicitly requires listing all backends for each instruction

        ValidationResult(
            is_valid: errors.is_empty,
            errors: errors
        )
```

### Task 4.5: SSpec Tests for Phase 4
**File:** `test/compiler/irdsl/dsl_parser_spec.spl` (NEW)
```simple
describe "IR DSL Parser":
    it "parses instruction definitions":
        val source = """
        instruction ConstInt:
            fields:
                dest: VReg
                value: i64
            category: Constants
            effects: Pure
            backends:
                cranelift:
                    code: |
                        let val = builder.ins().iconst(types::I64, value);
        """

        val ast = IrDslParser.parse(source)
        expect(ast.instructions.len).to_equal(1)

        val inst = ast.instructions[0]
        expect(inst.name).to_equal("ConstInt")
        expect(inst.fields.len).to_equal(2)
        expect(inst.backends.contains_key("cranelift")).to_be(true)

    it "validates all backends are defined":
        val source = """
        instruction TestInst:
            fields: ()
            category: Test
            backends:
                cranelift:
                    code: "// impl"
                # Missing llvm and vulkan!
        """

        val ast = IrDslParser.parse(source)
        val validator = IrDslValidator(ast: ast)
        val result = validator.validate()

        expect(result.is_valid).to_be(false)
        expect(result.errors.len).to_equal(2)  # Missing llvm, vulkan

describe "IR DSL Code Generator":
    it "generates valid Rust enum":
        val ast = IrDslAst(instructions: [
            InstructionDef(
                name: "ConstInt",
                fields: [Field(name: "dest", ty: "VReg"), Field(name: "value", ty: "i64")]
            )
        ])

        val generated = IrDslCodegen.generate(ast)
        val enum_code = generated.mir_enum

        expect(enum_code).to_contain("pub enum MirInst")
        expect(enum_code).to_contain("ConstInt { dest: VReg, value: i64 }")

    it "generates exhaustive match statements":
        val ast = IrDslAst(instructions: [
            InstructionDef(name: "Inst1", ...),
            InstructionDef(name: "Inst2", ...)
        ])

        val generated = IrDslCodegen.generate(ast)
        val cranelift_code = generated.cranelift_impl

        # Check no catch-all pattern
        expect(cranelift_code).not_to_contain("_ =>")

        # Check all instructions present
        expect(cranelift_code).to_contain("MirInst::Inst1")
        expect(cranelift_code).to_contain("MirInst::Inst2")
```

### Success Criteria (Phase 4)
- [ ] IR DSL syntax designed and documented
- [ ] DSL parser implemented in Simple
- [ ] Code generator produces valid Rust
- [ ] Completeness validator ensures all backends defined
- [ ] Generated code compiles without errors
- [ ] All SSpec tests for DSL pass
- [ ] Migration path for existing instructions defined

---

## Integration & CI

### Makefile Targets
```makefile
# Phase 1: Manual verification
check-exhaustiveness:
	@echo "Checking for catch-all patterns..."
	@./bin/wrappers/simple src/compiler/backend/exhaustiveness_validator.spl

# Phase 2: Run all backend tests
test-backends:
	@echo "Running backend coverage tests..."
	@./target/debug/simple_runtime test test/compiler/backend/

# Phase 3: Generate documentation
docs-backends:
	@echo "Generating backend documentation..."
	@./bin/wrappers/simple scripts/generate_backend_docs.spl all

# Phase 4: Regenerate code from DSL
codegen-from-dsl:
	@echo "Generating Rust code from IR DSL..."
	@./bin/wrappers/simple src/compiler/irdsl/main.spl

# Full pipeline
backend-completeness-full: check-exhaustiveness test-backends docs-backends
	@echo "✓ All backend completeness checks passed!"
```

### CI Integration
**File:** `.github/workflows/backend-completeness.yml` (NEW)
```yaml
name: Backend Completeness Checks

on: [push, pull_request]

jobs:
  exhaustiveness:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Check exhaustive pattern matching
        run: make check-exhaustiveness

  backend-tests:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Build Rust runtime
        run: cargo build
      - name: Run backend coverage tests
        run: make test-backends

  documentation:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - name: Generate backend docs
        run: make docs-backends
      - name: Check docs are up-to-date
        run: git diff --exit-code doc/backend/
```

---

## Timeline & Effort Estimates

| Phase | Description | Effort | Dependencies |
|-------|-------------|--------|--------------|
| **Phase 1** | Exhaustive matching | 8 hours | None |
| **Phase 2** | Testing infrastructure | 24 hours | Phase 1 |
| **Phase 3** | Documentation | 16 hours | Phase 2 |
| **Phase 4** | DSL code generation | 40 hours | Phase 3 |
| **Total** | **All phases** | **88 hours** | Sequential |

**Breakdown by Week:**
- Week 1: Phase 1 complete
- Week 2-3: Phase 2 complete
- Week 4: Phase 3 complete
- Week 5-6: Phase 4 complete

---

## Success Metrics

### Phase 1
- [ ] Rust compilation fails when new `MirInst` added
- [ ] Zero `_ => {}` patterns in backends
- [ ] All unsupported instructions have explicit errors

### Phase 2
- [ ] 100% instruction test coverage
- [ ] Differential tests pass (Cranelift vs LLVM)
- [ ] CI integration complete

### Phase 3
- [ ] Auto-generated documentation stays in sync
- [ ] Backend support matrix accurate
- [ ] Coverage statistics tracked

### Phase 4
- [ ] DSL compiles to valid Rust
- [ ] Generated code is exhaustive
- [ ] Adding new instruction only requires DSL update
- [ ] Time to add instruction < 15 minutes

---

## Risk Mitigation

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Phase 1 breaks existing code | Medium | High | Comprehensive testing before/after |
| Phase 2 tests have false positives | Medium | Medium | Careful semantic equivalence definition |
| Phase 4 DSL too complex | Low | High | Start simple, iterate based on feedback |
| Timeline too optimistic | Medium | Low | Phases are independent, can defer Phase 4 |

---

## Next Steps

1. **Review this plan** (30 min)
2. **Create tracking branch:** `feature/backend-completeness-all-phases`
3. **Begin Phase 1 implementation**
4. **Daily standup:** Progress check, blockers
5. **Weekly review:** Adjust timeline as needed

---

**Implementation Start Date:** 2026-01-31
**Expected Completion:** 2026-03-15 (6 weeks, assuming 15 hours/week)
