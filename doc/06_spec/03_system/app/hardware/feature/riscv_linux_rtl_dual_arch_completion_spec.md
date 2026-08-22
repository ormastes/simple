# riscv_linux_rtl_dual_arch_completion_spec

> Verifies the riscv linux rtl dual arch completion behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# riscv_linux_rtl_dual_arch_completion_spec

Verifies the riscv linux rtl dual arch completion behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the riscv linux rtl dual arch completion behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### REQ-RLD-001..007

#### keeps dual-arch QEMU virt profiles public and deterministic

- Verify: keeps dual-arch QEMU virt profiles public and deterministic
   - Expected: qemu_virt_rv32_platform_profile().name equals `qemu_virt_rv32`
   - Expected: qemu_virt_rv64_platform_profile().name equals `qemu_virt_rv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RLD-001 REQ-RLD-001..007
step("Verify: keeps dual-arch QEMU virt profiles public and deterministic")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(qemu_virt_rv32_platform_profile().name).to_equal("qemu_virt_rv32")
expect(qemu_virt_rv64_platform_profile().name).to_equal("qemu_virt_rv64")
```

</details>

#### keeps the default FPGA manifest dual-arch

- Verify: keeps the default FPGA manifest dual-arch
   - Expected: manifest.lanes.len() equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RLD-001 REQ-RLD-001..007
step("Verify: keeps the default FPGA manifest dual-arch")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val manifest = create_default_riscv_fpga_linux_manifest()
expect(manifest.lanes.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(manifest.readiness_summary()).to_contain("rv32:")
expect(manifest.readiness_summary()).to_contain("rv64:")
```

</details>

#### publishes product configuration, budget, and formal gates per lane

- Verify: publishes product configuration, budget, and formal gates per lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RLD-001 REQ-RLD-001..007
step("Verify: publishes product configuration, budget, and formal gates per lane")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b401404d82e92450fd08722e6794ef9ea224f469ee8f502a52fac3a2c34dc168`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b401404d82e92450fd08722e6794ef9ea224f469ee8f502a52fac3a2c34dc168`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b401404d82e92450fd08722e6794ef9ea224f469ee8f502a52fac3a2c34dc168`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.spl
mirror: doc/06_spec/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
