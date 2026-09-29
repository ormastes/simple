# Riscv Linux Rtl Dual Arch Completion Specification

> Tests covering REQ-RLD-001..007.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Linux Rtl Dual Arch Completion Specification

## Scenarios

### REQ-RLD-001..006

#### keeps dual-arch QEMU virt profiles public and deterministic

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-RLD-001..007
```

</details>

#### keeps the default FPGA manifest dual-arch

- keeps the default FPGA manifest dual-arch
   - Expected: manifest.lanes.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the default FPGA manifest dual-arch")
val manifest = create_default_riscv_fpga_linux_manifest()
expect(manifest.lanes.len()).to_equal(2)
expect(manifest.readiness_summary()).to_contain("rv32:")
expect(manifest.readiness_summary()).to_contain("rv64:")
```

</details>

#### publishes product configuration, budget, and formal gates per lane

- publishes product configuration, budget, and formal gates per lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("publishes product configuration, budget, and formal gates per lane")
val manifest = create_default_riscv_fpga_linux_manifest()
val text = manifest.rtl_manifest_text("/tmp/riscv_linux_rtl_dual_arch_completion")
expect(text).to_contain("product_level = \"linux-rtl\"")
expect(text).to_contain("configuration_profile = \"qemu-virt+fpga-board\"")
expect(text).to_contain("linux_abi = \"ilp32d\"")
expect(text).to_contain("linux_abi = \"lp64d\"")
expect(text).to_contain("linux_mmu = \"sv32\"")
expect(text).to_contain("linux_mmu = \"sv39\"")
expect(text).to_contain("rtl_size_budget_luts = \"25000\"")
expect(text).to_contain("rtl_size_budget_luts = \"45000\"")
expect(text).to_contain("perf_target_mhz = \"50\"")
expect(text).to_contain("formal_verification = \"rvfi+sby\"")
expect(text).to_contain("formal_gate = \"rvfi_port_manifest\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering REQ-RLD-001..007.
- REQ-RLD-001..007

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-RLD-001..007`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ec4bef808e62c4d2f9f397b52c9f39211f7b7d5bd66c5b24b121f3efb51966da`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ec4bef808e62c4d2f9f397b52c9f39211f7b7d5bd66c5b24b121f3efb51966da`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ec4bef808e62c4d2f9f397b52c9f39211f7b7d5bd66c5b24b121f3efb51966da`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.spl
mirror: doc/06_spec/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.spl:15:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'keeps dual-arch QEMU virt profiles public and deterministic' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the default FPGA manifest dual-arch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes product configuration, budget, and formal gates per lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
