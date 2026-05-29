# LLVM Backend AArch64 Specification
*Source:* `test/feature/usage/llvm_backend_aarch64_spec.spl`
**Feature IDs:** #4002  |  **Category:** Infrastructure  |  **Status:** In Progress

## Overview




Validates that the LLVM backend correctly generates code for AArch64 (ARM 64-bit) targets.

## Feature: LLVM Backend AArch64

### Scenario: target triple

| # | Example | Status |
|---|---------|--------|
| 1 | generates correct aarch64 triple | pass |

**Example:** generates correct aarch64 triple
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.AArch64)
    Then  expect(triple.arch).to_equal("aarch64")
    Then  expect(triple.to_text()).to_contain("aarch64")

### Scenario: datalayout

| # | Example | Status |
|---|---------|--------|
| 1 | contains correct aarch64 layout | pass |
| 2 | emits datalayout in module header | pass |

**Example:** contains correct aarch64 layout
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.AArch64)
    Given val dl = triple.datalayout()
    Then  expect(dl).to_contain("n32:64-S128")

**Example:** emits datalayout in module header
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.AArch64)
    Given var builder = LlvmIRBuilder__create("test_aarch64", triple)
    Given val ir = builder.instructions.join("{NL}")
    Then  expect(ir).to_contain("target datalayout")

### Scenario: CPU defaults

| # | Example | Status |
|---|---------|--------|
| 1 | defaults to cortex-a53 | pass |
| 2 | includes neon feature | pass |
| 3 | includes fp-armv8 feature | pass |

**Example:** defaults to cortex-a53
    Given val config = LlvmTargetConfig__for_target(CodegenTarget.AArch64, nil)
    Then  expect(config.cpu).to_equal("cortex-a53")

**Example:** includes neon feature
    Given val config = LlvmTargetConfig__for_target(CodegenTarget.AArch64, nil)
    Then  expect(config.features).to_contain("+neon")

**Example:** includes fp-armv8 feature
    Given val config = LlvmTargetConfig__for_target(CodegenTarget.AArch64, nil)
    Then  expect(config.features).to_contain("+fp-armv8")

### Scenario: native integer type

| # | Example | Status |
|---|---------|--------|
| 1 | native_int_type is i64 | pass |

**Example:** native_int_type is i64
    Given var translator = MirToLlvm__create("test", CodegenTarget.AArch64, nil)
    Then  expect(translator.native_int()).to_equal("i64")

### Scenario: type mapping

| # | Example | Status |
|---|---------|--------|
| 1 | uses 64-bit target_bits | pass |

**Example:** uses 64-bit target_bits
    Given val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.AArch64)
    Then  expect(mapper.target_bits).to_equal(64)

### Scenario: bare-metal entry

| # | Example | Status |
|---|---------|--------|
| 1 | uses wfi instruction for halt | pass |

**Example:** uses wfi instruction for halt
    Given val halt = halt_instruction_for_target(CodegenTarget.AArch64)
    Then  expect(halt).to_equal("wfi")

### Scenario: builder size type

| # | Example | Status |
|---|---------|--------|
| 1 | uses i64 size type | pass |

**Example:** uses i64 size type
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.AArch64)
    Given var builder = LlvmIRBuilder__create("test", triple)
    Then  expect(builder.size_type).to_equal("i64")


