# LLVM Backend RISC-V 32-bit Specification
*Source:* `test/feature/usage/llvm_backend_riscv32_spec.spl`
**Feature IDs:** #4003  |  **Category:** Infrastructure  |  **Status:** In Progress

## Overview




Validates that the LLVM backend correctly generates code for RISC-V 32-bit targets.

## Feature: LLVM Backend RISC-V 32

### Scenario: target triple

| # | Example | Status |
|---|---------|--------|
| 1 | generates correct riscv32 triple | pass |

**Example:** generates correct riscv32 triple
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.Riscv32)
    Then  expect(triple.arch).to_equal("riscv32")
    Then  expect(triple.to_text()).to_contain("riscv32")

### Scenario: datalayout

| # | Example | Status |
|---|---------|--------|
| 1 | contains correct riscv32 layout | pass |

**Example:** contains correct riscv32 layout
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.Riscv32)
    Given val dl = triple.datalayout()
    Then  expect(dl).to_contain("p:32:32")

### Scenario: CPU defaults

| # | Example | Status |
|---|---------|--------|
| 1 | defaults to generic-rv32 | pass |
| 2 | includes standard extensions | pass |

**Example:** defaults to generic-rv32
    Given val config = LlvmTargetConfig__for_target(CodegenTarget.Riscv32, nil)
    Then  expect(config.cpu).to_equal("generic-rv32")

**Example:** includes standard extensions
    Given val config = LlvmTargetConfig__for_target(CodegenTarget.Riscv32, nil)
    Then  expect(config.features).to_contain("+m")
    Then  expect(config.features).to_contain("+a")
    Then  expect(config.features).to_contain("+f")
    Then  expect(config.features).to_contain("+d")
    Then  expect(config.features).to_contain("+c")

### Scenario: native integer type

| # | Example | Status |
|---|---------|--------|
| 1 | native_int_type is i32 | pass |

**Example:** native_int_type is i32
    Given var translator = MirToLlvm__create("test", CodegenTarget.Riscv32, nil)
    Then  expect(translator.native_int()).to_equal("i32")

### Scenario: type mapping

| # | Example | Status |
|---|---------|--------|
| 1 | uses 32-bit target_bits | pass |

**Example:** uses 32-bit target_bits
    Given val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.Riscv32)
    Then  expect(mapper.target_bits).to_equal(32)

### Scenario: bare-metal entry

| # | Example | Status |
|---|---------|--------|
| 1 | uses wfi instruction for halt | pass |

**Example:** uses wfi instruction for halt
    Given val halt = halt_instruction_for_target(CodegenTarget.Riscv32)
    Then  expect(halt).to_equal("wfi")

### Scenario: builder size type

| # | Example | Status |
|---|---------|--------|
| 1 | uses i32 size type | pass |

**Example:** uses i32 size type
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.Riscv32)
    Given var builder = LlvmIRBuilder__create("test", triple)
    Then  expect(builder.size_type).to_equal("i32")


