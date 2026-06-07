# Baremetal Build Specification

> <details>

<!-- sdn-diagram:id=baremetal_build_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=baremetal_build_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

baremetal_build_spec -> std
baremetal_build_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=baremetal_build_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/compiler/baremetal/arm/linker.ld")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: x86_64 linker script exists</summary>

#### x86_64 linker script exists _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/compiler/baremetal/x86_64/linker.ld")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: RISC-V linker script exists</summary>

#### RISC-V linker script exists _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/compiler/baremetal/riscv/linker.ld")).to_equal(true)
```

</details>


</details>

### Startup Code

<details>
<summary>Advanced: ARM crt0.s exists</summary>

#### ARM crt0.s exists _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/compiler/baremetal/arm/crt0.s")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: x86_64 crt0.s exists</summary>

#### x86_64 crt0.s exists _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/compiler/baremetal/x86_64/crt0.s")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: RISC-V crt0.s exists</summary>

#### RISC-V crt0.s exists _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/compiler/baremetal/riscv/crt0.s")).to_equal(true)
```

</details>


</details>

### Configuration

<details>
<summary>Advanced: ARM config has correct paths</summary>

#### ARM config has correct paths _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = baremetal_config_arm()
expect(config.target_triple()).to_equal("armv7m-none-eabi")
```

</details>


</details>

<details>
<summary>Advanced: x86_64 target triple</summary>

#### x86_64 target triple _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = baremetal_config_x86_64()
expect(config.target_triple()).to_equal("x86_64-unknown-none")
```

</details>


</details>

<details>
<summary>Advanced: RISC-V target triple</summary>

#### RISC-V target triple _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = baremetal_config_riscv()
expect(config.target_triple()).to_equal("riscv64gc-unknown-none-elf")
```

</details>


</details>

### Test Output Parsing

<details>
<summary>Advanced: parses passing tests</summary>

#### parses passing tests _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = baremetal_config_arm()
val runner = QemuRunner.new(config, 30000)
expect(runner.qemu_executable()).to_equal("qemu-system-arm")
```

</details>


</details>

<details>
<summary>Advanced: x86_64 QEMU executable</summary>

#### x86_64 QEMU executable _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = baremetal_config_x86_64()
val runner = QemuRunner.new(config, 30000)
expect(runner.qemu_executable()).to_equal("qemu-system-x86_64")
```

</details>


</details>

<details>
<summary>Advanced: RISC-V QEMU executable</summary>

#### RISC-V QEMU executable _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
