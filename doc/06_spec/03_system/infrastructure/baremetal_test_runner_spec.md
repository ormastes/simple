# Baremetal Test Runner Specification

> Tests covering baremetal test runner, find_baremetal_elf, QEMU helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Baremetal Test Runner Specification

## Scenarios

### baremetal test runner

### find_baremetal_elf

#### returns a text path for riscv32 lookup

- returns a text path for riscv32 lookup
   - Expected: file_exists(elf_path) is true
   - Expected: elf_path equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns a text path for riscv32 lookup")
val elf_path = find_baremetal_elf(
    "test/fixtures/baremetal/trivial_baremetal_spec.spl", "riscv32"
)
if elf_path.len() > 0:
    expect(file_exists(elf_path)).to_equal(true)
else:
    expect(elf_path).to_equal("")
```

</details>

### QEMU helpers

#### returns correct binary for riscv32

- returns correct binary for riscv32
   - Expected: qemu_binary_for_arch("riscv32") equals `qemu-system-riscv32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns correct binary for riscv32")
expect(qemu_binary_for_arch("riscv32")).to_equal("qemu-system-riscv32")
```

</details>

#### returns correct binary for riscv64

- returns correct binary for riscv64
   - Expected: qemu_binary_for_arch("riscv64") equals `qemu-system-riscv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns correct binary for riscv64")
expect(qemu_binary_for_arch("riscv64")).to_equal("qemu-system-riscv64")
```

</details>

#### returns correct machine for riscv32

- returns correct machine for riscv32
   - Expected: qemu_machine_for_arch("riscv32") equals `virt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns correct machine for riscv32")
expect(qemu_machine_for_arch("riscv32")).to_equal("virt")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infrastructure/baremetal_test_runner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering baremetal test runner, find_baremetal_elf, QEMU helpers.
- baremetal test runner
- find_baremetal_elf
- QEMU helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `d03ba3a011ef89ad1ffcb9fcb999574c7463f0d365b72300ed73151be987a147`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d03ba3a011ef89ad1ffcb9fcb999574c7463f0d365b72300ed73151be987a147`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d03ba3a011ef89ad1ffcb9fcb999574c7463f0d365b72300ed73151be987a147`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/infrastructure/baremetal_test_runner_spec.spl
mirror: doc/06_spec/03_system/infrastructure/baremetal_test_runner_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/infrastructure/baremetal_test_runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/infrastructure/baremetal_test_runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/infrastructure/baremetal_test_runner_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a text path for riscv32 lookup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infrastructure/baremetal_test_runner_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns correct binary for riscv32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infrastructure/baremetal_test_runner_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns correct binary for riscv64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
