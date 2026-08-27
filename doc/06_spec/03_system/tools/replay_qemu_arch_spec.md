# Replay Qemu Arch Specification

> Tests covering Arch enum round-trip, qemu_binary_for_arch, machine_for_arch, supported_architectures.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Qemu Arch Specification

## Scenarios

### Arch enum round-trip

#### riscv32 round-trips through from_text and to_text

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- riscv32 round-trips through from_text and to_text
   - Expected: a.to_text() equals `riscv32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("riscv32 round-trips through from_text and to_text")
val a = Arch.from_text("riscv32")
expect(a.to_text()).to_equal("riscv32")
```

</details>

#### riscv64 round-trips through from_text and to_text

- riscv64 round-trips through from_text and to_text
   - Expected: a.to_text() equals `riscv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("riscv64 round-trips through from_text and to_text")
val a = Arch.from_text("riscv64")
expect(a.to_text()).to_equal("riscv64")
```

</details>

#### x86_64 round-trips through from_text and to_text

- x86_64 round-trips through from_text and to_text
   - Expected: a.to_text() equals `x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("x86_64 round-trips through from_text and to_text")
val a = Arch.from_text("x86_64")
expect(a.to_text()).to_equal("x86_64")
```

</details>

#### i386 alias resolves to X86_32

- i386 alias resolves to X86_32
   - Expected: a.to_text() equals `x86_32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("i386 alias resolves to X86_32")
val a = Arch.from_text("i386")
expect(a.to_text()).to_equal("x86_32")
```

</details>

#### aarch64 round-trips through from_text and to_text

- aarch64 round-trips through from_text and to_text
   - Expected: a.to_text() equals `aarch64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aarch64 round-trips through from_text and to_text")
val a = Arch.from_text("aarch64")
expect(a.to_text()).to_equal("aarch64")
```

</details>

### qemu_binary_for_arch

#### returns qemu-system-riscv32 for riscv32

- returns qemu-system-riscv32 for riscv32
   - Expected: qemu_binary_for_arch("riscv32") equals `qemu-system-riscv32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns qemu-system-riscv32 for riscv32")
expect(qemu_binary_for_arch("riscv32")).to_equal("qemu-system-riscv32")
```

</details>

#### returns qemu-system-riscv64 for riscv64

- returns qemu-system-riscv64 for riscv64
   - Expected: qemu_binary_for_arch("riscv64") equals `qemu-system-riscv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns qemu-system-riscv64 for riscv64")
expect(qemu_binary_for_arch("riscv64")).to_equal("qemu-system-riscv64")
```

</details>

#### returns qemu-system-x86_64 for x86_64

- returns qemu-system-x86_64 for x86_64
   - Expected: qemu_binary_for_arch("x86_64") equals `qemu-system-x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns qemu-system-x86_64 for x86_64")
expect(qemu_binary_for_arch("x86_64")).to_equal("qemu-system-x86_64")
```

</details>

#### returns qemu-system-i386 for i386

- returns qemu-system-i386 for i386
   - Expected: qemu_binary_for_arch("i386") equals `qemu-system-i386`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns qemu-system-i386 for i386")
expect(qemu_binary_for_arch("i386")).to_equal("qemu-system-i386")
```

</details>

#### returns qemu-system-aarch64 for aarch64

- returns qemu-system-aarch64 for aarch64
   - Expected: qemu_binary_for_arch("aarch64") equals `qemu-system-aarch64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns qemu-system-aarch64 for aarch64")
expect(qemu_binary_for_arch("aarch64")).to_equal("qemu-system-aarch64")
```

</details>

### machine_for_arch

#### returns virt for riscv32

- returns virt for riscv32
   - Expected: machine_for_arch("riscv32") equals `virt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns virt for riscv32")
expect(machine_for_arch("riscv32")).to_equal("virt")
```

</details>

#### returns virt for riscv64

- returns virt for riscv64
   - Expected: machine_for_arch("riscv64") equals `virt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns virt for riscv64")
expect(machine_for_arch("riscv64")).to_equal("virt")
```

</details>

#### returns q35 for x86_64

- returns q35 for x86_64
   - Expected: machine_for_arch("x86_64") equals `q35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns q35 for x86_64")
expect(machine_for_arch("x86_64")).to_equal("q35")
```

</details>

#### returns q35 for i386

- returns q35 for i386
   - Expected: machine_for_arch("i386") equals `q35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns q35 for i386")
expect(machine_for_arch("i386")).to_equal("q35")
```

</details>

#### returns virt for aarch64

- returns virt for aarch64
   - Expected: machine_for_arch("aarch64") equals `virt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns virt for aarch64")
expect(machine_for_arch("aarch64")).to_equal("virt")
```

</details>

### supported_architectures

#### returns exactly 5 entries

- returns exactly 5 entries
   - Expected: archs.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns exactly 5 entries")
val archs = supported_architectures()
expect(archs.len()).to_equal(5)
```

</details>

#### contains riscv32

- contains riscv32


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains riscv32")
val archs = supported_architectures()
expect(archs).to_contain("riscv32")
```

</details>

#### contains riscv64

- contains riscv64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains riscv64")
val archs = supported_architectures()
expect(archs).to_contain("riscv64")
```

</details>

#### contains x86_64

- contains x86_64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains x86_64")
val archs = supported_architectures()
expect(archs).to_contain("x86_64")
```

</details>

#### contains i386

- contains i386


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains i386")
val archs = supported_architectures()
expect(archs).to_contain("i386")
```

</details>

#### contains aarch64

- contains aarch64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains aarch64")
val archs = supported_architectures()
expect(archs).to_contain("aarch64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_qemu_arch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Arch enum round-trip, qemu_binary_for_arch, machine_for_arch, supported_architectures.
- Arch enum round-trip
- qemu_binary_for_arch
- machine_for_arch
- supported_architectures

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6b104948670531ddc0d81e11385c4768505a4f88244c572b9ccaccb738afe0c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6b104948670531ddc0d81e11385c4768505a4f88244c572b9ccaccb738afe0c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6b104948670531ddc0d81e11385c4768505a4f88244c572b9ccaccb738afe0c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/replay_qemu_arch_spec.spl
mirror: doc/06_spec/03_system/tools/replay_qemu_arch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/replay_qemu_arch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/replay_qemu_arch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/replay_qemu_arch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/replay_qemu_arch_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'riscv32 round-trips through from_text and to_text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/replay_qemu_arch_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'riscv64 round-trips through from_text and to_text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/replay_qemu_arch_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'x86_64 round-trips through from_text and to_text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
