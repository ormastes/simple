# LLVM Backend ARM 32-bit Specification
*Source:* `test/feature/usage/llvm_backend_arm32_spec.spl`
**Feature IDs:** #4004  |  **Category:** Infrastructure  |  **Status:** In Progress

## Overview




Validates that the LLVM backend correctly generates code for ARM 32-bit (ARMv7) targets.

## Feature: LLVM Backend ARM32

### Scenario: target triple

| # | Example | Status |
|---|---------|--------|
| 1 | generates correct armv7 triple | pass |
| 2 | includes gnueabihf env on linux | pass |

**Example:** generates correct armv7 triple
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.Arm)
    Then  expect(triple.arch).to_equal("armv7")
    Then  expect(triple.to_text()).to_contain("armv7")

**Example:** includes gnueabihf env on linux
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.Arm)
    Given val text = triple.to_text()
    Then  expect(text).to_contain("armv7")

### Scenario: datalayout

| # | Example | Status |
|---|---------|--------|
| 1 | contains correct arm32 layout | pass |

**Example:** contains correct arm32 layout
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.Arm)
    Given val dl = triple.datalayout()
    Then  expect(dl).to_contain("p:32:32")

### Scenario: CPU defaults

| # | Example | Status |
|---|---------|--------|
| 1 | defaults to cortex-a7 | pass |
| 2 | includes neon feature | pass |
| 3 | includes vfp4 feature | pass |

**Example:** defaults to cortex-a7
    Given val config = LlvmTargetConfig__for_target(CodegenTarget.Arm, nil)
    Then  expect(config.cpu).to_equal("cortex-a7")

**Example:** includes neon feature
    Given val config = LlvmTargetConfig__for_target(CodegenTarget.Arm, nil)
    Then  expect(config.features).to_contain("+neon")

**Example:** includes vfp4 feature
    Given val config = LlvmTargetConfig__for_target(CodegenTarget.Arm, nil)
    Then  expect(config.features).to_contain("+vfp4")

### Scenario: native integer type

| # | Example | Status |
|---|---------|--------|
| 1 | native_int_type is i32 | pass |

**Example:** native_int_type is i32
    Given var translator = MirToLlvm__create("test", CodegenTarget.Arm, nil)
    Then  expect(translator.native_int()).to_equal("i32")

### Scenario: type mapping

| # | Example | Status |
|---|---------|--------|
| 1 | uses 32-bit target_bits | pass |

**Example:** uses 32-bit target_bits
    Given val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.Arm)
    Then  expect(mapper.target_bits).to_equal(32)

### Scenario: bare-metal entry

| # | Example | Status |
|---|---------|--------|
| 1 | uses wfi instruction for halt | pass |

**Example:** uses wfi instruction for halt
    Given val halt = halt_instruction_for_target(CodegenTarget.Arm)
    Then  expect(halt).to_equal("wfi")

### Scenario: builder size type

| # | Example | Status |
|---|---------|--------|
| 1 | uses i32 size type | pass |

**Example:** uses i32 size type
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.Arm)
    Given var builder = LlvmIRBuilder__create("test", triple)
    Then  expect(builder.size_type).to_equal("i32")


