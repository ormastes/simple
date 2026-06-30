# Hardening Gates Specification

> <details>

<!-- sdn-diagram:id=hardening_gates_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hardening_gates_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hardening_gates_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hardening_gates_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hardening Gates Specification

## Scenarios

### AC-5/R6 — stack canary is not 0xDEADBEEFDEADBEEFUL

#### simpleos_cxxabi.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(CXXABI_PATH)).to_equal(true)
```

</details>

#### simpleos_cxxabi.spl does NOT contain the hardcoded constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(CXXABI_PATH)
expect(body.contains("0xDEADBEEFDEADBEEF")).to_equal(false)
```

</details>

#### simpleos_cxxabi.spl does NOT contain the legacy DEADBEEF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(CXXABI_PATH)
expect(body.contains("DEADBEEF")).to_equal(false)
```

</details>

#### x86_64 canary value differs across two reboots

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log: text = file_read(_arch_canary_log("x86_64"))
expect(log.contains("\"differs_across_reboots\": true")).to_equal(true)
```

</details>

#### x86_32 canary value differs across two reboots

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log: text = file_read(_arch_canary_log("x86_32"))
expect(log.contains("\"differs_across_reboots\": true")).to_equal(true)
```

</details>

#### aarch64 canary value differs across two reboots

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log: text = file_read(_arch_canary_log("aarch64"))
expect(log.contains("\"differs_across_reboots\": true")).to_equal(true)
```

</details>

#### arm32 canary value differs across two reboots

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log: text = file_read(_arch_canary_log("arm32"))
expect(log.contains("\"differs_across_reboots\": true")).to_equal(true)
```

</details>

#### riscv64 canary value differs across two reboots

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log: text = file_read(_arch_canary_log("riscv64"))
expect(log.contains("\"differs_across_reboots\": true")).to_equal(true)
```

</details>

#### riscv32 canary value differs across two reboots

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log: text = file_read(_arch_canary_log("riscv32"))
expect(log.contains("\"differs_across_reboots\": true")).to_equal(true)
```

</details>

### AC-5/R6 — per-arch entropy source matches HAL design

#### x86_64 entropy.spl uses rdrand or rdseed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(_entropy_path("x86_64"))
val ok: bool = body.contains("rdrand") or body.contains("rdseed") or body.contains("RDRAND") or body.contains("RDSEED")
expect(ok).to_equal(true)
```

</details>

#### x86_32 entropy.spl uses rdrand (CPUID-gated)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(_entropy_path("x86_32"))
val ok: bool = body.contains("rdrand") or body.contains("RDRAND")
expect(ok).to_equal(true)
```

</details>

#### arm64 entropy.spl probes RNDR or falls back to CNTVCT

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(_entropy_path("arm64"))
val ok: bool = body.contains("rndr") or body.contains("RNDR") or body.contains("CNTVCT")
expect(ok).to_equal(true)
```

</details>

#### arm32 entropy.spl seeds from CNTVCT + DTB

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(_entropy_path("arm32"))
val ok: bool = body.contains("CNTVCT") or body.contains("dtb") or body.contains("DTB")
expect(ok).to_equal(true)
```

</details>

#### riscv64 entropy.spl uses sbi_get_random or cycle+time+instret

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(_entropy_path("riscv64"))
val ok: bool = body.contains("sbi_get_random") or body.contains("instret") or body.contains("Zkr")
expect(ok).to_equal(true)
```

</details>

#### riscv32 entropy.spl uses sbi_get_random or cycle+time+instret

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(_entropy_path("riscv32"))
val ok: bool = body.contains("sbi_get_random") or body.contains("instret")
expect(ok).to_equal(true)
```

</details>

### AC-5 — W^X enforcement

#### harden audit report exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(HARDEN_REPORT)).to_equal(true)
```

</details>

#### no W|X mapping anywhere in audited tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"wx_violations\": 0")).to_equal(true)
```

</details>

#### x86_32 PAE NX is active when CONFIG_X86_32_PAE is set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"x86_32_nx_status\"")).to_equal(true)
```

</details>

#### kernel write to .text page traps

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"text_write_trap\": true")).to_equal(true)
```

</details>

#### arm64 sandbox lowering maps non-exec rows to PXN and UXN

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read("src/os/kernel/arch/arm64/paging.spl")
expect(body.contains("arm64_sandbox_pte_bits_for_permissions")).to_equal(true)
expect(body.contains("PTE_PXN | PTE_UXN")).to_equal(true)
```

</details>

#### riscv64 boot installs sandbox PMP plan before os_main

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read("src/os/kernel/arch/riscv64/boot.spl")
val hook_index = body.index_of("sandbox_boot_apply_embedded_riscv64") ?? -1
val main_index = body.index_of("os_main()") ?? -1
expect(hook_index >= 0).to_equal(true)
expect(main_index >= 0).to_equal(true)
expect(hook_index < main_index).to_equal(true)
```

</details>

#### arm64 boot installs sandbox MPU plan before boot complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read("src/os/kernel/arch/arm64/boot.spl")
expect(body.contains("sandbox_boot_apply_embedded_arm_mpu()\n    _line_boot_complete()")).to_equal(true)
```

</details>

#### arm32 boot output path installs sandbox MPU plan before returning

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read("src/os/kernel/arch/arm32/boot.spl")
expect(body.contains("sandbox_boot_apply_embedded_arm_mpu()\n\n    BootOutputPort(")).to_equal(true)
```

</details>

#### sandbox boot bridge has RISC-V and ARM64 backends

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read("src/os/kernel/security/sandbox_boot_apply.spl")
expect(body.contains("pmp_write_plan_from_sandbox_lowering")).to_equal(true)
expect(body.contains("arm64_sandbox_pte_bits_from_lowering")).to_equal(true)
expect(body.contains("arm_mpu_mmio_write_plan_from_sandbox_lowering")).to_equal(true)
expect(body.contains("sandbox_boot_apply_embedded_arm_mpu")).to_equal(true)
expect(body.contains("mmio_write32")).to_equal(true)
```

</details>

#### sandbox boot bridge names linker metadata section bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read("src/os/kernel/security/sandbox_boot_apply.spl")
expect(body.contains("__simple_sandbox_start")).to_equal(true)
expect(body.contains("__simple_sandbox_end")).to_equal(true)
expect(body.contains("embedded_sandbox_section_bounds_valid")).to_equal(true)
```

</details>

#### sandbox boot bridge validates embedded lowering before use

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read("src/os/kernel/security/sandbox_boot_apply.spl")
expect(body.contains("end_addr > start_addr")).to_equal(true)
expect(body.contains("sandbox_lowering:")).to_equal(true)
expect(body.contains("pmp_region|")).to_equal(true)
expect(body.contains("return \"\"")).to_equal(true)
```

</details>

#### sandbox boot bridge reads embedded section bytes behind validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read("src/os/kernel/security/sandbox_boot_apply.spl")
expect(body.contains("embedded_sandbox_lowering_sdn_from_raw_bounds")).to_equal(true)
expect(body.contains("rt_bytes_from_raw")).to_equal(true)
expect(body.contains("rt_bytes_to_text")).to_equal(true)
expect(body.contains("embedded_sandbox_lowering_sdn_from_section(start_addr, end_addr, section_text)")).to_equal(true)
```

</details>

#### sandbox boot bridge gets linker section addresses from runtime providers

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read("src/os/kernel/security/sandbox_boot_apply.spl")
val runtime: text = file_read(RUNTIME_MINIMAL_C)
expect(body.contains("rt_simple_sandbox_section_start")).to_equal(true)
expect(body.contains("rt_simple_sandbox_section_end")).to_equal(true)
expect(body.contains("embedded_sandbox_lowering_sdn_from_raw_bounds(\n        rt_simple_sandbox_section_start(),\n        rt_simple_sandbox_section_end()")).to_equal(true)
expect(runtime.contains("__simple_sandbox_start[] __attribute__((weak))")).to_equal(true)
expect(runtime.contains("__simple_sandbox_end[] __attribute__((weak))")).to_equal(true)
expect(runtime.contains("rt_simple_sandbox_section_start")).to_equal(true)
expect(runtime.contains("rt_simple_sandbox_section_end")).to_equal(true)
```

</details>

#### ARM and baremetal linker scripts preserve sandbox metadata sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_linker_preserves_sandbox_metadata("src/os/kernel/arch/arm64/linker.ld")).to_equal(true)
expect(_linker_preserves_sandbox_metadata("src/os/kernel/arch/arm32/linker.ld")).to_equal(true)
expect(_linker_preserves_sandbox_metadata("src/compiler/70.backend/baremetal/arm/linker.ld")).to_equal(true)
expect(_linker_preserves_sandbox_metadata("src/os/realtime/boot/arm.ld")).to_equal(true)
expect(_linker_preserves_sandbox_metadata("examples/09_embedded/simple_os/arch/arm64/linker.ld")).to_equal(true)
expect(_linker_preserves_sandbox_metadata("examples/09_embedded/simple_os/arch/arm64/fs_exec_linker.ld")).to_equal(true)
expect(_linker_preserves_sandbox_metadata("examples/09_embedded/simple_os/arch/arm32/linker.ld")).to_equal(true)
expect(_linker_preserves_sandbox_metadata("examples/09_embedded/simple_os/arch/arm32/fs_exec_linker.ld")).to_equal(true)
expect(_linker_preserves_sandbox_metadata("examples/09_embedded/baremetal/baremetal/arm64.ld")).to_equal(true)
```

</details>

### AC-5 — capability check at every syscall entry

#### harden audit reports cap-check coverage = 100%

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"cap_check_coverage_pct\": 100")).to_equal(true)
```

</details>

#### no Syscall variant lacks a cap-check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"syscall_variants_uncovered\": 0")).to_equal(true)
```

</details>

### AC-5 — bounds-check intrinsic + @nocheck policy

#### no @nocheck outside arch/ HAL tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"nocheck_outside_hal\": 0")).to_equal(true)
```

</details>

#### no `unsafe` outside arch/ HAL tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"unsafe_outside_hal\": 0")).to_equal(true)
```

</details>

#### compiler emitted @check_bounds in arch-neutral kernel containers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"check_bounds_emitted\": true")).to_equal(true)
```

</details>

### AC-5 — bin/simple build check runs harden audit per-arch

#### harden audit per-arch summary present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"per_arch_exit_codes\"")).to_equal(true)
```

</details>

#### every arch lane exit code is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"all_arch_pass\": true")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/multiarch/hardening_gates_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AC-5/R6 — stack canary is not 0xDEADBEEFDEADBEEFUL
- AC-5/R6 — per-arch entropy source matches HAL design
- AC-5 — W^X enforcement
- AC-5 — capability check at every syscall entry
- AC-5 — bounds-check intrinsic + @nocheck policy
- AC-5 — bin/simple build check runs harden audit per-arch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
