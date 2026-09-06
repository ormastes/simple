# Baremetal Build Specification

> Tests covering Bare-Metal Build System, Linker Scripts, Startup Code, Configuration, Target Triples, Test Output Parsing, QEMU Runner.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Baremetal Build Specification

## Scenarios

### Bare-Metal Build System

### Linker Scripts

<details>
<summary>Advanced: ARM linker script exists</summary>

#### ARM linker script exists _(slow)_

- ARM linker script exists
   - Expected: file_exists("src/compiler/baremetal/arm/linker.ld") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ARM linker script exists")
expect(file_exists("src/compiler/baremetal/arm/linker.ld")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: x86_64 linker script exists</summary>

#### x86_64 linker script exists _(slow)_

- x86_64 linker script exists
   - Expected: file_exists("src/compiler/baremetal/x86_64/linker.ld") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("x86_64 linker script exists")
expect(file_exists("src/compiler/baremetal/x86_64/linker.ld")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: RISC-V linker script exists</summary>

#### RISC-V linker script exists _(slow)_

- RISC-V linker script exists
   - Expected: file_exists("src/compiler/baremetal/riscv/linker.ld") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("RISC-V linker script exists")
expect(file_exists("src/compiler/baremetal/riscv/linker.ld")).to_equal(true)
```

</details>


</details>

### Startup Code

<details>
<summary>Advanced: ARM crt0.s exists</summary>

#### ARM crt0.s exists _(slow)_

- ARM crt0.s exists
   - Expected: file_exists("src/compiler/baremetal/arm/crt0.s") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ARM crt0.s exists")
expect(file_exists("src/compiler/baremetal/arm/crt0.s")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: x86_64 crt0.s exists</summary>

#### x86_64 crt0.s exists _(slow)_

- x86_64 crt0.s exists
   - Expected: file_exists("src/compiler/baremetal/x86_64/crt0.s") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("x86_64 crt0.s exists")
expect(file_exists("src/compiler/baremetal/x86_64/crt0.s")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: RISC-V crt0.s exists</summary>

#### RISC-V crt0.s exists _(slow)_

- RISC-V crt0.s exists
   - Expected: file_exists("src/compiler/baremetal/riscv/crt0.s") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("RISC-V crt0.s exists")
expect(file_exists("src/compiler/baremetal/riscv/crt0.s")).to_equal(true)
```

</details>


</details>

### Configuration

<details>
<summary>Advanced: ARM config has correct paths</summary>

#### ARM config has correct paths _(slow)_

- ARM config has correct paths
   - Expected: config.linker_script equals `src/compiler/baremetal/arm/linker.ld`
   - Expected: config.crt0_path equals `src/compiler/baremetal/arm/crt0.s`
   - Expected: config.entry_point equals `reset_handler`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ARM config has correct paths")
val config = baremetal_config_arm()
expect(config.linker_script).to_equal("src/compiler/baremetal/arm/linker.ld")
expect(config.crt0_path).to_equal("src/compiler/baremetal/arm/crt0.s")
expect(config.entry_point).to_equal("reset_handler")
```

</details>


</details>

<details>
<summary>Advanced: x86_64 config has correct paths</summary>

#### x86_64 config has correct paths _(slow)_

- x86_64 config has correct paths
   - Expected: config.linker_script equals `src/compiler/baremetal/x86_64/linker.ld`
   - Expected: config.crt0_path equals `src/compiler/baremetal/x86_64/crt0.s`
   - Expected: config.entry_point equals `_start`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("x86_64 config has correct paths")
val config = baremetal_config_x86_64()
expect(config.linker_script).to_equal("src/compiler/baremetal/x86_64/linker.ld")
expect(config.crt0_path).to_equal("src/compiler/baremetal/x86_64/crt0.s")
expect(config.entry_point).to_equal("_start")
```

</details>


</details>

<details>
<summary>Advanced: RISC-V config has correct paths</summary>

#### RISC-V config has correct paths _(slow)_

- RISC-V config has correct paths
   - Expected: config.linker_script equals `src/compiler/baremetal/riscv/linker.ld`
   - Expected: config.crt0_path equals `src/compiler/baremetal/riscv/crt0.s`
   - Expected: config.entry_point equals `_start`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("RISC-V config has correct paths")
val config = baremetal_config_riscv()
expect(config.linker_script).to_equal("src/compiler/baremetal/riscv/linker.ld")
expect(config.crt0_path).to_equal("src/compiler/baremetal/riscv/crt0.s")
expect(config.entry_point).to_equal("_start")
```

</details>


</details>

### Target Triples

<details>
<summary>Advanced: ARM target triple</summary>

#### ARM target triple _(slow)_

- ARM target triple
   - Expected: config.target_triple() equals `armv7m-none-eabi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ARM target triple")
val config = baremetal_config_arm()
expect(config.target_triple()).to_equal("armv7m-none-eabi")
```

</details>


</details>

<details>
<summary>Advanced: x86_64 target triple</summary>

#### x86_64 target triple _(slow)_

- x86_64 target triple
   - Expected: config.target_triple() equals `x86_64-unknown-none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("x86_64 target triple")
val config = baremetal_config_x86_64()
expect(config.target_triple()).to_equal("x86_64-unknown-none")
```

</details>


</details>

<details>
<summary>Advanced: RISC-V target triple</summary>

#### RISC-V target triple _(slow)_

- RISC-V target triple
   - Expected: config.target_triple() equals `riscv64gc-unknown-none-elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("RISC-V target triple")
val config = baremetal_config_riscv()
expect(config.target_triple()).to_equal("riscv64gc-unknown-none-elf")
```

</details>


</details>

### Test Output Parsing

<details>
<summary>Advanced: parses passing tests</summary>

#### parses passing tests _(slow)_

- parses passing tests
   - Expected: result.tests_run equals `2`
   - Expected: result.tests_passed equals `2`
   - Expected: result.tests_failed equals `0`
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses passing tests")
val output = "[TEST START]\n[PASS] test_one\n[PASS] test_two\n[TEST END] passed=2 failed=0"
val result = parse_test_output(output, 1)
expect(result.tests_run).to_equal(2)
expect(result.tests_passed).to_equal(2)
expect(result.tests_failed).to_equal(0)
expect(result.success).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: parses failing tests</summary>

#### parses failing tests _(slow)_

- parses failing tests
   - Expected: result.tests_run equals `2`
   - Expected: result.tests_passed equals `1`
   - Expected: result.tests_failed equals `1`
   - Expected: result.success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("parses failing tests")
val output = "[TEST START]\n[PASS] test_one\n[FAIL] test_two: assertion failed\n[TEST END] passed=1 failed=1"
val result = parse_test_output(output, 1)
expect(result.tests_run).to_equal(2)
expect(result.tests_passed).to_equal(1)
expect(result.tests_failed).to_equal(1)
expect(result.success).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: adjusts QEMU exit codes correctly</summary>

#### adjusts QEMU exit codes correctly _(slow)_

- adjusts QEMU exit codes correctly
   - Expected: result1.exit_code equals `0`
   - Expected: result2.exit_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("adjusts QEMU exit codes correctly")
# isa-debug-exit: exit code 0 becomes 1
val result1 = parse_test_output("", 1)
expect(result1.exit_code).to_equal(0)

# isa-debug-exit: exit code 1 becomes 3
val result2 = parse_test_output("", 3)
expect(result2.exit_code).to_equal(1)
```

</details>


</details>

### QEMU Runner

<details>
<summary>Advanced: ARM QEMU executable</summary>

#### ARM QEMU executable _(slow)_

- ARM QEMU executable
   - Expected: runner.qemu_executable() equals `qemu-system-arm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ARM QEMU executable")
val config = baremetal_config_arm()
val runner = QemuRunner.new(config, 30000)
expect(runner.qemu_executable()).to_equal("qemu-system-arm")
```

</details>


</details>

<details>
<summary>Advanced: x86_64 QEMU executable</summary>

#### x86_64 QEMU executable _(slow)_

- x86_64 QEMU executable
   - Expected: runner.qemu_executable() equals `qemu-system-x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("x86_64 QEMU executable")
val config = baremetal_config_x86_64()
val runner = QemuRunner.new(config, 30000)
expect(runner.qemu_executable()).to_equal("qemu-system-x86_64")
```

</details>


</details>

<details>
<summary>Advanced: RISC-V QEMU executable</summary>

#### RISC-V QEMU executable _(slow)_

- RISC-V QEMU executable
   - Expected: runner.qemu_executable() equals `qemu-system-riscv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("RISC-V QEMU executable")
val config = baremetal_config_riscv()
val runner = QemuRunner.new(config, 30000)
expect(runner.qemu_executable()).to_equal("qemu-system-riscv64")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/02_integration/baremetal/baremetal_build_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Bare-Metal Build System, Linker Scripts, Startup Code, Configuration, Target Triples, Test Output Parsing, QEMU Runner.
- Bare-Metal Build System
- Linker Scripts
- Startup Code
- Configuration
- Target Triples
- Test Output Parsing
- QEMU Runner

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 18 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `40ac127325badc6cdcf4b404a4bd95d77739a638e34b8e8b82000772bcda2f97`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `40ac127325badc6cdcf4b404a4bd95d77739a638e34b8e8b82000772bcda2f97`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `40ac127325badc6cdcf4b404a4bd95d77739a638e34b8e8b82000772bcda2f97`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/baremetal/baremetal_build_spec.spl
mirror: doc/06_spec/02_integration/baremetal/baremetal_build_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/baremetal/baremetal_build_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/baremetal/baremetal_build_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/baremetal/baremetal_build_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/baremetal/baremetal_build_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ARM linker script exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/baremetal/baremetal_build_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'x86_64 linker script exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/baremetal/baremetal_build_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'RISC-V linker script exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
