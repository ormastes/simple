# LLVM Backend RISC-V 64-bit Specification
*Source:* `test/feature/usage/llvm_backend_riscv64_spec.spl`
**Feature IDs:** #4005  |  **Category:** Infrastructure  |  **Status:** In Progress

## Overview




Validates that the LLVM backend correctly generates code for RISC-V 64-bit targets.

## Feature: LLVM Backend RISC-V 64

### Scenario: target triple

| # | Example | Status |
|---|---------|--------|
| 1 | generates correct riscv64 triple | pass |

**Example:** generates correct riscv64 triple
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.Riscv64)
    Then  expect(triple.arch).to_equal("riscv64")
    Then  expect(triple.to_text()).to_contain("riscv64")

### Scenario: datalayout

| # | Example | Status |
|---|---------|--------|
| 1 | contains correct riscv64 layout | pass |

**Example:** contains correct riscv64 layout
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.Riscv64)
    Given val dl = triple.datalayout()
    Then  expect(dl).to_contain("p:64:64")

### Scenario: CPU defaults

| # | Example | Status |
|---|---------|--------|
| 1 | defaults to generic-rv64 | pass |
| 2 | includes standard extensions | pass |

**Example:** defaults to generic-rv64
    Given val config = LlvmTargetConfig__for_target(CodegenTarget.Riscv64, nil)
    Then  expect(config.cpu).to_equal("generic-rv64")

**Example:** includes standard extensions
    Given val config = LlvmTargetConfig__for_target(CodegenTarget.Riscv64, nil)
    Then  expect(config.features).to_contain("+m")
    Then  expect(config.features).to_contain("+a")
    Then  expect(config.features).to_contain("+f")
    Then  expect(config.features).to_contain("+d")
    Then  expect(config.features).to_contain("+c")

### Scenario: native integer type

| # | Example | Status |
|---|---------|--------|
| 1 | native_int_type is i64 | pass |

**Example:** native_int_type is i64
    Given var translator = MirToLlvm__create("test", CodegenTarget.Riscv64, nil)
    Then  expect(translator.native_int()).to_equal("i64")

### Scenario: type mapping

| # | Example | Status |
|---|---------|--------|
| 1 | uses 64-bit target_bits | pass |

**Example:** uses 64-bit target_bits
    Given val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.Riscv64)
    Then  expect(mapper.target_bits).to_equal(64)

### Scenario: bare-metal entry

| # | Example | Status |
|---|---------|--------|
| 1 | uses wfi instruction for halt | pass |

**Example:** uses wfi instruction for halt
    Given val halt = halt_instruction_for_target(CodegenTarget.Riscv64)
    Then  expect(halt).to_equal("wfi")

### Scenario: builder size type

| # | Example | Status |
|---|---------|--------|
| 1 | uses i64 size type | pass |

**Example:** uses i64 size type
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.Riscv64)
    Given var builder = LlvmIRBuilder__create("test", triple)
    Then  expect(builder.size_type).to_equal("i64")


