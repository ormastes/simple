# Unified Execution Specification

> Tests covering Debug Adapter Layer, Execution Configuration, Test Executor, QEMU Test Session, QEMU Multi-Test Runner, Unified Execution Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unified Execution Specification

## Scenarios

### Debug Adapter Layer

#### creates local adapter from config

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates local adapter from config


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates local adapter from config")
val config = AdapterConfig.local()
check(config.kind == "local")
check(config.target == "local")
check(not config.is_remote())
```

</details>

#### local adapter has correct capabilities

- local adapter has correct capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("local adapter has correct capabilities")
val caps = AdapterCapabilities.local()
check(caps.can_stop)
check(caps.can_break)
check(caps.can_run_single_step)
```

</details>

#### creates GDB MI adapter from config

- creates GDB MI adapter from config


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates GDB MI adapter from config")
val config = AdapterConfig.qemu_riscv32()
check(config.kind == "qemu-riscv32")
check(config.port == 3333)
check(config.is_remote())
```

</details>

#### GDB adapter has correct capabilities

- GDB adapter has correct capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GDB adapter has correct capabilities")
val caps = AdapterCapabilities.remote()
check(caps.can_stop)
check(caps.can_break)
check(not caps.can_run_single_step)
```

</details>

### Execution Configuration

#### creates local execution config

- creates local execution config


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates local execution config")
val config = parse_target("local")
check(config.kind == "local")
check(config.auto_reset)
```

</details>

#### creates QEMU RISC-V 32 config

- creates QEMU RISC-V 32 config


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates QEMU RISC-V 32 config")
val config = parse_target("riscv32-qemu")
check(config.kind == "qemu-riscv32")
check(config.port == 3333)
```

</details>

#### creates QEMU x86_64 config

- creates QEMU x86_64 config


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates QEMU x86_64 config")
val config = parse_target("x86_64-qemu")
check(config.kind == "qemu-x86_64")
check(config.port == 4444)
```

</details>

#### parses local target string

- parses local target string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses local target string")
val config = parse_target("local")
check(config.target == "local")
check(not config.is_remote())
```

</details>

#### parses riscv32-qemu target string

- parses riscv32-qemu target string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses riscv32-qemu target string")
val config = parse_target("riscv32-qemu")
check(config.target == "riscv32-qemu")
check(config.is_remote())
```

</details>

#### parses custom target with port

- parses custom target with port


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses custom target with port")
val config = AdapterConfig.custom("board:5555", 5555)
check(config.kind == "custom")
check(config.target == "board:5555")
check(config.port == 5555)
```

</details>

### Test Executor

#### creates executor for local target

- creates executor for local target


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates executor for local target")
val executor = TestExecutor.create(AdapterConfig.local())
check(executor.mode == "local")
check(not executor.uses_remote_transport())
check(executor.capabilities.can_run_single_step)
```

</details>

#### creates executor for QEMU target

- creates executor for QEMU target


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates executor for QEMU target")
val executor = TestExecutor.create(AdapterConfig.qemu_riscv32())
check(executor.mode == "remote")
check(executor.uses_remote_transport())
check(executor.capabilities.can_stop)
```

</details>

### QEMU Test Session

#### creates test session

- creates test session


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates test session")
val session = QemuTestSession.create(3333, true)
check(session.gdb_port == 3333)
check(session.auto_reset)
check(not session.running)
```

</details>

#### configures session with custom GDB port

- configures session with custom GDB port


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("configures session with custom GDB port")
val session = QemuTestSession.create(4901, true)
check(session.gdb_port == 4901)
```

</details>

#### configures session with auto-reset disabled

- configures session with auto-reset disabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("configures session with auto-reset disabled")
val session = QemuTestSession.create(4902, false)
check(not session.auto_reset)
```

</details>

#### starts and stops QEMU session

- starts and stops QEMU session


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts and stops QEMU session")
val session = QemuTestSession.create(4903, true)
session.start()
check(session.running)
session.stop()
check(not session.running)
```

</details>

### QEMU Multi-Test Runner

#### creates multi-test runner

- creates multi-test runner


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates multi-test runner")
val session = QemuTestSession.create(5000, true)
val runner = QemuMultiTestRunner.create(session)
check(runner.tests.len() == 0)
check(runner.session.gdb_port == 5000)
```

</details>

#### adds tests to runner

- adds tests to runner


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds tests to runner")
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

- runs multiple tests with single QEMU instance


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs multiple tests with single QEMU instance")
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

- transparent execution - local


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transparent execution - local")
val executor = TestExecutor.create(parse_target("local"))
check(executor.mode == "local")
check(executor.config.target == "local")
```

</details>

#### transparent execution - remote QEMU

- transparent execution - remote QEMU


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transparent execution - remote QEMU")
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
| Source | `test/unit/lib/unified_execution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Debug Adapter Layer, Execution Configuration, Test Executor, QEMU Test Session, QEMU Multi-Test Runner, Unified Execution Integration.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e76e9fe05c52947610c64d4d6e1f683579d17a50162f8b262d5e7ef9dc55849d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e76e9fe05c52947610c64d4d6e1f683579d17a50162f8b262d5e7ef9dc55849d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e76e9fe05c52947610c64d4d6e1f683579d17a50162f8b262d5e7ef9dc55849d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/unified_execution_spec.spl
mirror: doc/06_spec/unit/lib/unified_execution_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/unified_execution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/unified_execution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/unified_execution_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates local adapter from config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/unified_execution_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'local adapter has correct capabilities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/unified_execution_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates GDB MI adapter from config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
