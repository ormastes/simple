# Qemu Specification

> Tests covering Qemu.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qemu Specification

## Scenarios

### Qemu

#### should define supported QEMU architectures and command names

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should define supported QEMU architectures and command names
   - Expected: src contains `enum QemuArch`
   - Expected: src contains `case QemuArch.X86: "qemu-system-i386"`
   - Expected: src contains `case QemuArch.X86_64: "qemu-system-x86_64"`
   - Expected: src contains `case QemuArch.ARM64: "qemu-system-aarch64"`
   - Expected: src contains `case QemuArch.RiscV32: "qemu-system-riscv32"`
   - Expected: src contains `case QemuArch.RiscV64: "qemu-system-riscv64"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should define supported QEMU architectures and command names")
val src = qemu_source()
expect(src.contains("enum QemuArch")).to_equal(true)
expect(src.contains("case QemuArch.X86: \"qemu-system-i386\"")).to_equal(true)
expect(src.contains("case QemuArch.X86_64: \"qemu-system-x86_64\"")).to_equal(true)
expect(src.contains("case QemuArch.ARM64: \"qemu-system-aarch64\"")).to_equal(true)
expect(src.contains("case QemuArch.RiscV32: \"qemu-system-riscv32\"")).to_equal(true)
expect(src.contains("case QemuArch.RiscV64: \"qemu-system-riscv64\"")).to_equal(true)
```

</details>

#### should define architecture defaults and aliases

- should define architecture defaults and aliases
   - Expected: src contains `fn default_machine() -> text`
   - Expected: src contains `case QemuArch.ARM32: "lm3s6965evb"`
   - Expected: src contains `fn default_memory() -> text`
   - Expected: src contains `case QemuArch.ARM32: "16M"`
   - Expected: src contains `fn from_string(s: text) -> QemuArch`
   - Expected: src contains `elif s == "riscv64" or s == "rv64"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should define architecture defaults and aliases")
val src = qemu_source()
expect(src.contains("fn default_machine() -> text")).to_equal(true)
expect(src.contains("case QemuArch.ARM32: \"lm3s6965evb\"")).to_equal(true)
expect(src.contains("fn default_memory() -> text")).to_equal(true)
expect(src.contains("case QemuArch.ARM32: \"16M\"")).to_equal(true)
expect(src.contains("fn from_string(s: text) -> QemuArch")).to_equal(true)
expect(src.contains("elif s == \"riscv64\" or s == \"rv64\"")).to_equal(true)
```

</details>

#### should define remote debug and test runner configurations

- should define remote debug and test runner configurations
   - Expected: src contains `class QemuConfig`
   - Expected: src contains `static fn for_remote_debug(arch: QemuArch, elf_path: text, port: i32) -> Qemu... (full value in folded executable source)`
   - Expected: src contains `gdb_enabled: true`
   - Expected: src contains `gdb_wait: true`
   - Expected: src contains `static fn for_test_runner(arch: QemuArch, elf_path: text) -> QemuConfig`
   - Expected: src contains `serial_stdio: true`
   - Expected: src contains `debug_exit: true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should define remote debug and test runner configurations")
val src = qemu_source()
expect(src.contains("class QemuConfig")).to_equal(true)
expect(src.contains("static fn for_remote_debug(arch: QemuArch, elf_path: text, port: i32) -> QemuConfig")).to_equal(true)
expect(src.contains("gdb_enabled: true")).to_equal(true)
expect(src.contains("gdb_wait: true")).to_equal(true)
expect(src.contains("static fn for_test_runner(arch: QemuArch, elf_path: text) -> QemuConfig")).to_equal(true)
expect(src.contains("serial_stdio: true")).to_equal(true)
expect(src.contains("debug_exit: true")).to_equal(true)
```

</details>

#### should build QEMU command line arguments from config fields

- should build QEMU command line arguments from config fields
   - Expected: src contains `fn build_args() -> [text]`
   - Expected: src contains `args.push("-machine")`
   - Expected: src contains `args.push("-kernel")`
   - Expected: src contains `args.push("-gdb")`
   - Expected: src contains `args.push("-serial")`
   - Expected: src contains `isa-debug-exit,iobase=0xf4,iosize=0x04`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should build QEMU command line arguments from config fields")
val src = qemu_source()
expect(src.contains("fn build_args() -> [text]")).to_equal(true)
expect(src.contains("args.push(\"-machine\")")).to_equal(true)
expect(src.contains("args.push(\"-kernel\")")).to_equal(true)
expect(src.contains("args.push(\"-gdb\")")).to_equal(true)
expect(src.contains("args.push(\"-serial\")")).to_equal(true)
expect(src.contains("isa-debug-exit,iobase=0xf4,iosize=0x04")).to_equal(true)
```

</details>

#### should expose process launch exit interpretation and tool discovery

- should expose process launch exit interpretation and tool discovery
   - Expected: src contains `class QemuInstance`
   - Expected: src contains `static fn start(config: QemuConfig) -> Result<QemuInstance, text>`
   - Expected: src contains `fn interpret_exit_code(exit_code: i32, has_debug_exit: bool) -> ExitCodeResult`
   - Expected: src contains `fn is_qemu_available(arch: QemuArch) -> bool`
   - Expected: src contains `fn find_gdb(arch: QemuArch) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should expose process launch exit interpretation and tool discovery")
val src = qemu_source()
expect(src.contains("class QemuInstance")).to_equal(true)
expect(src.contains("static fn start(config: QemuConfig) -> Result<QemuInstance, text>")).to_equal(true)
expect(src.contains("fn interpret_exit_code(exit_code: i32, has_debug_exit: bool) -> ExitCodeResult")).to_equal(true)
expect(src.contains("fn is_qemu_available(arch: QemuArch) -> bool")).to_equal(true)
expect(src.contains("fn find_gdb(arch: QemuArch) -> text")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Qemu.
- Qemu

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d17ea7350338760a80cf7a8b2adbbe37ef59ef0680b2a8cf811ae1c346d35abe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d17ea7350338760a80cf7a8b2adbbe37ef59ef0680b2a8cf811ae1c346d35abe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d17ea7350338760a80cf7a8b2adbbe37ef59ef0680b2a8cf811ae1c346d35abe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/qemu_spec.spl
mirror: doc/06_spec/01_unit/lib/qemu_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/qemu_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define supported QEMU architectures and command names' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/qemu_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should define supported QEMU architectures and command names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/qemu_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define architecture defaults and aliases' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/qemu_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should define architecture defaults and aliases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/qemu_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define remote debug and test runner configurations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/qemu_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should define remote debug and test runner configurations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/qemu_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should build QEMU command line arguments from config fields' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/qemu_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose process launch exit interpretation and tool discovery' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
