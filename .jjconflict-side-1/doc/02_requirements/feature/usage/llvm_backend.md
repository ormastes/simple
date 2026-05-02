# LLVM Backend Codegen Specification
*Source:* `test/feature/usage/llvm_backend_spec.spl`
**Feature IDs:** #4000  |  **Category:** Infrastructure  |  **Status:** In Progress

## Overview




The LLVM backend provides high-performance native code generation for the Simple language
compiler. It converts the compiler's Intermediate Representation (MIR) to LLVM IR, enabling
optimized machine code generation for multiple target platforms. This specification covers
LLVM IR generation, optimization passes, linking, and target-specific code generation.

## Key Concepts

| Concept | Description |
|---------|-------------|
| LLVM IR | Intermediate representation compatible with LLVM compiler framework |
| MIR to LLVM | Conversion pipeline from Simple's MIR to LLVM IR |
| Optimization Passes | LLVM-level optimizations (inlining, dead code elimination, etc) |
| Code Generation | Conversion of LLVM IR to native machine code |
| Target Platform | Architecture and OS-specific code generation (x86_64, ARM, etc) |
| Linking | Integration with system linker and native libraries |

## Behavior

The LLVM backend:
- Translates MIR instructions to equivalent LLVM IR constructs
- Preserves type information and memory semantics
- Enables high-level optimizations through LLVM optimization passes
- Generates platform-specific machine code
- Integrates with native linkers for final executable generation
- Supports multiple target architectures and operating systems

## Implementation Notes

- LLVM IR generation uses the `inkwell` Rust bindings
- Optimization level controlled via compiler flags
- Target triple determines platform-specific behavior
- Function attributes affect code generation and optimization
- Debug information preserved for debugging support

## Related Specifications

- Intermediate Representation (MIR format specification)
- Memory Model (reference capabilities and ownership rules)
- FFI Integration (native function calling conventions)
- Type System (type information preservation in codegen)

## Feature: LLVM Backend Codegen

## LLVM Backend Codegen Specification

    This test suite verifies LLVM backend code generation including:
    - Correct MIR to LLVM IR translation
    - Function prologue/epilogue generation
    - Stack frame management and calling conventions
    - Memory operations and pointer handling
    - Optimization level preservation
    - Platform-specific code generation

### Scenario: basic arithmetic operations

| # | Example | Status |
|---|---------|--------|
| 1 | generates code for integer addition | pass |
| 2 | generates code for integer multiplication | pass |
| 3 | generates code for floating-point operations | pass |

**Example:** generates code for integer addition
    Then  expect add(5, 3) == 8

**Example:** generates code for integer multiplication
    Then  expect multiply(5, 3) == 15

**Example:** generates code for floating-point operations
    Given val result = divide(10.0, 2.0)
    Then  expect (result - 5.0).abs() < 0.001

### Scenario: control flow generation

| # | Example | Status |
|---|---------|--------|
| 1 | generates code for if-else branches | pass |
| 2 | generates code for loops | pass |

**Example:** generates code for if-else branches
    Then  expect classify(5) == "positive"
    Then  expect classify(-3) == "non-positive"

**Example:** generates code for loops
    Given var sum = 0
    Given var i = 0
    Then  expect count_up(5) == 10

### Scenario: function calls and stack management

| # | Example | Status |
|---|---------|--------|
| 1 | handles function calls | pass |
| 2 | handles recursive function calls | pass |

**Example:** handles function calls
    Then  expect outer(3) == 11

**Example:** handles recursive function calls
    Then  expect fibonacci(6) == 8

### Scenario: memory operations

| # | Example | Status |
|---|---------|--------|
| 1 | generates code for variable assignment | pass |
| 2 | handles mutable struct fields | pass |

**Example:** generates code for variable assignment
    Given var x = 5
    Then  expect variable_ops() == 8

**Example:** handles mutable struct fields
    Given var p = Point(x: 0, y: 0)
    Given val (x, y) = move_point()
    Then  expect x == 10
    Then  expect y == 20

### Scenario: collection operations

| # | Example | Status |
|---|---------|--------|
| 1 | generates code for list operations | pass |
| 2 | generates code for map operations | pass |

**Example:** generates code for list operations
    Given val items = [1, 2, 3, 4, 5]
    Then  expect list_ops() == 5

**Example:** generates code for map operations
    Given val items = {"a": 1, "b": 2}
    Then  expect map_ops() == 1

### Scenario: type operations

| # | Example | Status |
|---|---------|--------|
| 1 | generates code for type conversions | pass |

**Example:** generates code for type conversions
    Given val i = 42
    Given val f = i.to_f64()
    Given val result = convert()
    Then  expect (result - 42.0).abs() < 0.001

### Scenario: optimization preservation

| # | Example | Status |
|---|---------|--------|
| 1 | preserves correct semantics under optimization | pass |
| 2 | maintains correct results with loop optimization | pass |

**Example:** preserves correct semantics under optimization
    Given val x = 5
    Given val y = 3
    Then  expect optimizable(2) == 10

**Example:** maintains correct results with loop optimization
    Given var result = 1
    Given var i = 1
    Then  expect loop_opt(5) == 120

### Scenario: optimization

| # | Example | Status |
|---|---------|--------|
| 1 | generates passes for optimization levels | pass |

**Example:** generates passes for optimization levels
    Given val debug_passes = passes_for_level(OptimizationLevel.Debug)
    Then  expect(debug_passes.len()).to_equal(2)
    Given val speed_passes = passes_for_level(OptimizationLevel.Speed)
    Then  expect(speed_passes.len()).to_be_greater_than(4)
    Given val aggressive_passes = passes_for_level(OptimizationLevel.Aggressive)
    Then  expect(aggressive_passes.len()).to_be_greater_than(8)

### Scenario: debug info

| # | Example | Status |
|---|---------|--------|
| 1 | emits debug info header | pass |

**Example:** emits debug info header
    Given val target = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
    Given var builder = LlvmIRBuilder__create("test", target)
    Given val ir = builder.instructions.join("{NL}")
    Then  expect(ir).to_contain("DICompileUnit")
    Then  expect(ir).to_contain("test.spl")

### Scenario: ABI

| # | Example | Status |
|---|---------|--------|
| 1 | emits typed function calls | pass |

**Example:** emits typed function calls
    Given val target = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
    Given var builder = LlvmIRBuilder__create("test", target)
    Given val ir = builder.instructions.join("{NL}")
    Then  expect(ir).to_contain("call i64 @add")

### Scenario: target datalayout

| # | Example | Status |
|---|---------|--------|
| 1 | emits datalayout for x86_64 | pass |
| 2 | emits datalayout for i686 | pass |
| 3 | emits datalayout for aarch64 | pass |
| 4 | emits datalayout before target triple | pass |

**Example:** emits datalayout for x86_64
    Given val target = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
    Given var builder = LlvmIRBuilder__create("test", target)
    Given val ir = builder.instructions.join("{NL}")
    Then  expect(ir).to_contain("target datalayout")
    Then  expect(ir).to_contain("n8:16:32:64-S128")

**Example:** emits datalayout for i686
    Given val target = LlvmTargetTriple__from_target(CodegenTarget.X86)
    Given var builder = LlvmIRBuilder__create("test", target)
    Given val ir = builder.instructions.join("{NL}")
    Then  expect(ir).to_contain("target datalayout")
    Then  expect(ir).to_contain("p:32:32")

**Example:** emits datalayout for aarch64
    Given val target = LlvmTargetTriple__from_target(CodegenTarget.AArch64)
    Given var builder = LlvmIRBuilder__create("test", target)
    Given val ir = builder.instructions.join("{NL}")
    Then  expect(ir).to_contain("target datalayout")
    Then  expect(ir).to_contain("n32:64-S128")

**Example:** emits datalayout before target triple
    Given val target = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
    Given var builder = LlvmIRBuilder__create("test", target)
    Given val ir = builder.instructions.join("{NL}")
    Given val dl_pos = ir.find("target datalayout")
    Given val tt_pos = ir.find("target triple")
    Then  expect(dl_pos).to_be_less_than(tt_pos)

### Scenario: 32-bit type handling

| # | Example | Status |
|---|---------|--------|
| 1 | native_int_type is i32 for 32-bit targets | pass |
| 2 | native_int_type is i64 for 64-bit targets | pass |
| 3 | type mapper uses 32-bit pointers for i686 | pass |
| 4 | type mapper uses 64-bit pointers for x86_64 | pass |
| 5 | builder size_type is i32 for 32-bit targets | pass |
| 6 | builder size_type is i64 for 64-bit targets | pass |

**Example:** native_int_type is i32 for 32-bit targets
    Given var translator = MirToLlvm__create("test", CodegenTarget.X86, nil)
    Then  expect(translator.native_int()).to_equal("i32")

**Example:** native_int_type is i64 for 64-bit targets
    Given var translator = MirToLlvm__create("test", CodegenTarget.X86_64, nil)
    Then  expect(translator.native_int()).to_equal("i64")

**Example:** type mapper uses 32-bit pointers for i686
    Given val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.X86)
    Then  expect(mapper.target_bits).to_equal(32)

**Example:** type mapper uses 64-bit pointers for x86_64
    Given val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.X86_64)
    Then  expect(mapper.target_bits).to_equal(64)

**Example:** builder size_type is i32 for 32-bit targets
    Given val target = LlvmTargetTriple__from_target(CodegenTarget.X86)
    Given var builder = LlvmIRBuilder__create("test", target)
    Then  expect(builder.size_type).to_equal("i32")

**Example:** builder size_type is i64 for 64-bit targets
    Given val target = LlvmTargetTriple__from_target(CodegenTarget.X86_64)
    Given var builder = LlvmIRBuilder__create("test", target)
    Then  expect(builder.size_type).to_equal("i64")

### Scenario: compatibility build

| # | Example | Status |
|---|---------|--------|
| 1 | selects correct CPU for x86_64 | pass |
| 2 | selects correct CPU for i686 | pass |
| 3 | selects correct CPU for aarch64 | pass |
| 4 | selects correct CPU for riscv64 | pass |
| 5 | selects correct CPU for riscv32 | pass |

**Example:** selects correct CPU for x86_64
    Given val config = LlvmTargetConfig__compatibility_build(CodegenTarget.X86_64)
    Then  expect(config.cpu).to_equal("x86-64")

**Example:** selects correct CPU for i686
    Given val config = LlvmTargetConfig__compatibility_build(CodegenTarget.X86)
    Then  expect(config.cpu).to_equal("i686")

**Example:** selects correct CPU for aarch64
    Given val config = LlvmTargetConfig__compatibility_build(CodegenTarget.AArch64)
    Then  expect(config.cpu).to_equal("generic")

**Example:** selects correct CPU for riscv64
    Given val config = LlvmTargetConfig__compatibility_build(CodegenTarget.Riscv64)
    Then  expect(config.cpu).to_equal("generic-rv64")

**Example:** selects correct CPU for riscv32
    Given val config = LlvmTargetConfig__compatibility_build(CodegenTarget.Riscv32)
    Then  expect(config.cpu).to_equal("generic-rv32")


