# LLVM Backend i686 (x86 32-bit) Specification
*Source:* `test/feature/usage/llvm_backend_i686_spec.spl`
**Feature IDs:** #4001  |  **Category:** Infrastructure  |  **Status:** In Progress

## Overview




Validates that the LLVM backend correctly generates code for 32-bit x86 (i686) targets.
This includes target triple generation, datalayout, native integer types, and CPU defaults.

## Feature: LLVM Backend i686

### Scenario: target triple

| # | Example | Status |
|---|---------|--------|
| 1 | generates correct i686 triple | pass |
| 2 | includes correct OS in triple | pass |

**Example:** generates correct i686 triple
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.X86)
    Then  expect(triple.arch).to_equal("i686")
    Then  expect(triple.to_text()).to_contain("i686")

**Example:** includes correct OS in triple
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.X86)
    Given val text = triple.to_text()
    Then  expect(text).to_contain("i686")

### Scenario: datalayout

| # | Example | Status |
|---|---------|--------|
| 1 | contains 32-bit pointer specification | pass |
| 2 | emits datalayout in module header | pass |

**Example:** contains 32-bit pointer specification
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.X86)
    Given val dl = triple.datalayout()
    Then  expect(dl).to_contain("p:32:32")

**Example:** emits datalayout in module header
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.X86)
    Given var builder = LlvmIRBuilder__create("test_i686", triple)
    Given val ir = builder.instructions.join("{NL}")
    Then  expect(ir).to_contain("target datalayout")
    Then  expect(ir).to_contain("p:32:32")

### Scenario: type mapping

| # | Example | Status |
|---|---------|--------|
| 1 | uses 32-bit target_bits | pass |

**Example:** uses 32-bit target_bits
    Given val mapper = LlvmTypeMapper__create_for_target(CodegenTarget.X86)
    Then  expect(mapper.target_bits).to_equal(32)

### Scenario: native integer type

| # | Example | Status |
|---|---------|--------|
| 1 | native_int_type is i32 | pass |

**Example:** native_int_type is i32
    Given var translator = MirToLlvm__create("test", CodegenTarget.X86, nil)
    Then  expect(translator.native_int()).to_equal("i32")

### Scenario: CPU defaults

| # | Example | Status |
|---|---------|--------|
| 1 | defaults to i686 CPU | pass |
| 2 | includes sse2 feature | pass |

**Example:** defaults to i686 CPU
    Given val config = LlvmTargetConfig__for_target(CodegenTarget.X86, nil)
    Then  expect(config.cpu).to_equal("i686")

**Example:** includes sse2 feature
    Given val config = LlvmTargetConfig__for_target(CodegenTarget.X86, nil)
    Then  expect(config.features).to_contain("+sse2")

### Scenario: compatibility build

| # | Example | Status |
|---|---------|--------|
| 1 | works for i686 | pass |

**Example:** works for i686
    Given val config = LlvmTargetConfig__compatibility_build(CodegenTarget.X86)
    Then  expect(config.cpu).to_equal("i686")

### Scenario: builder size type

| # | Example | Status |
|---|---------|--------|
| 1 | uses i32 size type for memcpy/memset | pass |

**Example:** uses i32 size type for memcpy/memset
    Given val triple = LlvmTargetTriple__from_target(CodegenTarget.X86)
    Given var builder = LlvmIRBuilder__create("test", triple)
    Then  expect(builder.size_type).to_equal("i32")


