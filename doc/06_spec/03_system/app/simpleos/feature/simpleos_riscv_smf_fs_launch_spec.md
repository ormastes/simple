# Simpleos Riscv Smf Fs Launch Specification

> Tests covering SimpleOS RISC-V SMF filesystem launch, REQ-RISCV-SMF-005: QEMU scenarios.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Riscv Smf Fs Launch Specification

## Scenarios

### SimpleOS RISC-V SMF filesystem launch

### REQ-RISCV-SMF-005: QEMU scenarios

#### registers the RV64 filesystem SMF scenario

- registers the RV64 filesystem SMF scenario
   - Expected: scenario.name equals `riscv64-virtio-fat32-smf`
   - Expected: scenario.arch equals `Architecture.Riscv64`
   - Expected: scenario_test_timeout_ms(scenario) equals `60000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-RISCV-SMF-005 REQ-SSPEC-SYSTEM
step("registers the RV64 filesystem SMF scenario")
val scenario = scenario_riscv64_virtio_fat32_smf()
expect(scenario.name).to_equal("riscv64-virtio-fat32-smf")
expect(scenario.arch).to_equal(Architecture.Riscv64)
expect(scenario.qemu_extra).to_contain("virtio-blk-device,drive=rvdisk")
expect(scenario.qemu_extra).to_contain("-no-user-config")
expect(scenario.qemu_extra).to_contain("-monitor")
expect(scenario_test_timeout_ms(scenario)).to_equal(60000)
```

</details>

#### boots RV64 through the explicit OpenSBI provider without an interactive monitor

- boots RV64 through the explicit OpenSBI provider without an interactive monitor


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots RV64 through the explicit OpenSBI provider without an interactive monitor")
val scenario = scenario_riscv64_virtio_fat32_smf()
val command = build_scenario_command(scenario, "build/os/simpleos_riscv64_smf_fs.elf")
expect(command).to_contain("qemu-system-riscv64")
expect(command).to_contain("-bios")
expect(command).to_contain("default")
expect(command).to_contain("-no-user-config")
expect(command).to_contain("-monitor")
expect(command).to_contain("none")
```

</details>

#### registers the RV32 filesystem SMF scenario

- registers the RV32 filesystem SMF scenario
   - Expected: scenario.name equals `riscv32-virtio-fat32-smf`
   - Expected: scenario.arch equals `Architecture.Riscv32`
   - Expected: scenario_test_timeout_ms(scenario) equals `60000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("registers the RV32 filesystem SMF scenario")
val scenario = scenario_riscv32_virtio_fat32_smf()
expect(scenario.name).to_equal("riscv32-virtio-fat32-smf")
expect(scenario.arch).to_equal(Architecture.Riscv32)
expect(scenario.qemu_extra).to_contain("virtio-blk-device,drive=rvdisk")
expect(scenario_test_timeout_ms(scenario)).to_equal(60000)
```

</details>

#### resolves scenarios by name

- resolves scenarios by name
   - Expected: get_scenario("riscv64-virtio-fat32-smf").unwrap().name equals `riscv64-virtio-fat32-smf`
   - Expected: get_scenario("riscv32-virtio-fat32-smf").unwrap().name equals `riscv32-virtio-fat32-smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves scenarios by name")
expect(get_scenario("riscv64-virtio-fat32-smf").unwrap().name).to_equal("riscv64-virtio-fat32-smf")
expect(get_scenario("riscv32-virtio-fat32-smf").unwrap().name).to_equal("riscv32-virtio-fat32-smf")
```

</details>

#### binds scenarios to RISC-V smoke entries

- binds scenarios to RISC-V smoke entries
   - Expected: scenario_target(scenario_riscv64_virtio_fat32_smf()).entry equals `examples/09_embedded/simple_os/arch/riscv64/smoke_entry.spl`
   - Expected: scenario_target(scenario_riscv32_virtio_fat32_smf()).entry equals `examples/09_embedded/simple_os/arch/riscv32/smoke_entry.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds scenarios to RISC-V smoke entries")
expect(scenario_target(scenario_riscv64_virtio_fat32_smf()).entry).to_equal("examples/09_embedded/simple_os/arch/riscv64/smoke_entry.spl")
expect(scenario_target(scenario_riscv32_virtio_fat32_smf()).entry).to_equal("examples/09_embedded/simple_os/arch/riscv32/smoke_entry.spl")
```

</details>

#### requires the hosted RV64 entry to execute and collect filesystem processes

- requires the hosted RV64 entry to execute and collect filesystem processes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires the hosted RV64 entry to execute and collect filesystem processes")
val source = file_read("examples/09_embedded/simple_os/arch/riscv64/hosted_entry.spl")
expect(source).to_contain("riscv64_fs_exec_spawn_capture(app_path, [app_path], [])")
expect(source).to_contain("if result.exit_code != 0:")
expect(source).to_contain("stdout_bytes={result.bytes.len()}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_riscv_smf_fs_launch_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS RISC-V SMF filesystem launch, REQ-RISCV-SMF-005: QEMU scenarios.
- SimpleOS RISC-V SMF filesystem launch
- REQ-RISCV-SMF-005: QEMU scenarios

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-RISCV-SMF-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `65bef479952b050c136ee0ce3e08c0491b98d1d8c5eeb2e9a0939c7bb80673ac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `65bef479952b050c136ee0ce3e08c0491b98d1d8c5eeb2e9a0939c7bb80673ac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `65bef479952b050c136ee0ce3e08c0491b98d1d8c5eeb2e9a0939c7bb80673ac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/app/simpleos/feature/simpleos_riscv_smf_fs_launch_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_riscv_smf_fs_launch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos/feature/simpleos_riscv_smf_fs_launch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_riscv_smf_fs_launch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos/feature/simpleos_riscv_smf_fs_launch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/simpleos/feature/simpleos_riscv_smf_fs_launch_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers the RV64 filesystem SMF scenario' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_riscv_smf_fs_launch_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boots RV64 through the explicit OpenSBI provider without an interactive monitor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos/feature/simpleos_riscv_smf_fs_launch_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers the RV32 filesystem SMF scenario' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
