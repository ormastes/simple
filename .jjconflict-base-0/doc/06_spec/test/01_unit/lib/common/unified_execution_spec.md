# Unified Execution Specification

> <details>

<!-- sdn-diagram:id=unified_execution_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unified_execution_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unified_execution_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unified_execution_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unified Execution Specification

## Scenarios

### Debug Adapter Layer

#### creates local adapter from config

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AdapterConfig.local()
check(config.kind == "local")
check(config.target == "local")
check(config.is_remote() == false)
```

</details>

#### local adapter has correct capabilities

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = AdapterCapabilities.local()
check(caps.can_stop)
check(caps.can_break)
check(caps.can_run_single_step)
```

</details>

#### creates GDB MI adapter from config

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AdapterConfig.qemu_riscv32()
check(config.kind == "qemu-riscv32")
check(config.port == 3333)
check(config.is_remote())
```

</details>

#### GDB adapter has correct capabilities

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = AdapterCapabilities.remote()
check(caps.can_stop)
check(caps.can_break)
check(caps.can_run_single_step == false)
```

</details>

### Execution Configuration

#### creates local execution config

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = parse_target("local")
check(config.kind == "local")
check(config.auto_reset)
```

</details>

#### creates QEMU RISC-V 32 config

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = parse_target("riscv32-qemu")
check(config.kind == "qemu-riscv32")
check(config.port == 3333)
```

</details>

#### creates QEMU x86_64 config

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = parse_target("x86_64-qemu")
check(config.kind == "qemu-x86_64")
check(config.port == 4444)
```

</details>

#### parses local target string

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = parse_target("local")
check(config.target == "local")
check(config.is_remote() == false)
```

</details>

#### parses riscv32-qemu target string

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = parse_target("riscv32-qemu")
check(config.target == "riscv32-qemu")
check(config.is_remote())
```

</details>

#### parses custom target with port

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AdapterConfig.custom("board:5555", 5555)
check(config.kind == "custom")
check(config.target == "board:5555")
check(config.port == 5555)
```

</details>

### Test Executor

#### creates executor for local target

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val executor = TestExecutor.create(AdapterConfig.local())
check(executor.mode == "local")
check(executor.uses_remote_transport() == false)
check(executor.capabilities.can_run_single_step)
```

</details>

#### creates executor for QEMU target

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val executor = TestExecutor.create(AdapterConfig.qemu_riscv32())
check(executor.mode == "remote")
check(executor.uses_remote_transport())
check(executor.capabilities.can_stop)
```

</details>

### QEMU Test Session

#### creates test session

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = QemuTestSession.create(3333, true)
check(session.gdb_port == 3333)
check(session.auto_reset)
check(session.running == false)
```

</details>

#### configures session with custom GDB port

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = QemuTestSession.create(4901, true)
check(session.gdb_port == 4901)
```

</details>

#### configures session with auto-reset disabled

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = QemuTestSession.create(4902, false)
check(session.auto_reset == false)
```

</details>

#### starts and stops QEMU session

- session start
- check
- session stop
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = QemuTestSession.create(4903, true)
session.start()
check(session.running)
session.stop()
check(session.running == false)
```

</details>

### QEMU Multi-Test Runner

#### creates multi-test runner

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = QemuTestSession.create(5000, true)
val runner = QemuMultiTestRunner.create(session)
check(runner.tests.len() == 0)
check(runner.session.gdb_port == 5000)
```

</details>

#### adds tests to runner

- runner add test
- runner add test
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = QemuTestSession.create(5001, true)
val runner = QemuMultiTestRunner.create(session)
runner.add_test("boot")
runner.add_test("smoke")
check(runner.tests.len() == 2)
check(runner.tests[0] == "boot")
check(runner.tests[1] == "smoke")
```

</details>

#### runs multiple tests with single QEMU instance

- runner add test
- runner add test
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = QemuTestSession.create(5002, true)
val runner = QemuMultiTestRunner.create(session)
runner.add_test("first")
runner.add_test("second")
check(runner.run_count() == 2)
check(runner.session.gdb_port == 5002)
```

</details>

### Unified Execution Integration

#### transparent execution - local

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val executor = TestExecutor.create(parse_target("local"))
check(executor.mode == "local")
check(executor.config.target == "local")
```

</details>

#### transparent execution - remote QEMU

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val executor = TestExecutor.create(parse_target("riscv32-qemu"))
check(executor.mode == "remote")
check(executor.config.target == "riscv32-qemu")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/unified_execution_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Debug Adapter Layer
- Execution Configuration
- Test Executor
- QEMU Test Session
- QEMU Multi-Test Runner
- Unified Execution Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
