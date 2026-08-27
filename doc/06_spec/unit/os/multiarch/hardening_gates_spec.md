# Hardening Gates Specification

> Tests covering AC-5/R6 — stack canary is not 0xDEADBEEFDEADBEEFUL, AC-5/R6 — per-arch entropy source matches HAL design, AC-5 — W^X enforcement, AC-5 — capability check at every syscall entry, AC-5 — bounds-check intrinsic + @nocheck policy, AC-5 — bin/simple build check runs harden audit per-arch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hardening Gates Specification

## Scenarios

### AC-5/R6 — stack canary is not 0xDEADBEEFDEADBEEFUL

#### simpleos_cxxabi.spl exists

- simpleos_cxxabi.spl exists
   - Expected: file_exists(CXXABI_PATH) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simpleos_cxxabi.spl exists")
expect(file_exists(CXXABI_PATH)).to_equal(true)
```

</details>

#### simpleos_cxxabi.spl does NOT contain the hardcoded constant

- simpleos_cxxabi.spl does NOT contain the hardcoded constant
   - Expected: body does not contain `0xDEADBEEFDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simpleos_cxxabi.spl does NOT contain the hardcoded constant")
val body: text = file_read(CXXABI_PATH)
expect(body.contains("0xDEADBEEFDEADBEEF")).to_equal(false)
```

</details>

#### simpleos_cxxabi.spl does NOT contain the legacy DEADBEEF

- simpleos_cxxabi.spl does NOT contain the legacy DEADBEEF
   - Expected: body does not contain `DEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simpleos_cxxabi.spl does NOT contain the legacy DEADBEEF")
val body: text = file_read(CXXABI_PATH)
expect(body.contains("DEADBEEF")).to_equal(false)
```

</details>

#### x86_64 canary value differs across two reboots

- x86_64 canary value differs across two reboots
   - Expected: log contains `"differs_across_reboots": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x86_64 canary value differs across two reboots")
"""Phase 5/7 capture two independent boot canary values into
canary_runtime.json. The harness asserts they differ."""
val log: text = file_read(_arch_canary_log("x86_64"))
expect(log.contains("\"differs_across_reboots\": true")).to_equal(true)
```

</details>

#### x86_32 canary value differs across two reboots

- x86_32 canary value differs across two reboots
   - Expected: log contains `"differs_across_reboots": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x86_32 canary value differs across two reboots")
val log: text = file_read(_arch_canary_log("x86_32"))
expect(log.contains("\"differs_across_reboots\": true")).to_equal(true)
```

</details>

#### aarch64 canary value differs across two reboots

- aarch64 canary value differs across two reboots
   - Expected: log contains `"differs_across_reboots": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aarch64 canary value differs across two reboots")
val log: text = file_read(_arch_canary_log("aarch64"))
expect(log.contains("\"differs_across_reboots\": true")).to_equal(true)
```

</details>

#### arm32 canary value differs across two reboots

- arm32 canary value differs across two reboots
   - Expected: log contains `"differs_across_reboots": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm32 canary value differs across two reboots")
val log: text = file_read(_arch_canary_log("arm32"))
expect(log.contains("\"differs_across_reboots\": true")).to_equal(true)
```

</details>

#### riscv64 canary value differs across two reboots

- riscv64 canary value differs across two reboots
   - Expected: log contains `"differs_across_reboots": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv64 canary value differs across two reboots")
val log: text = file_read(_arch_canary_log("riscv64"))
expect(log.contains("\"differs_across_reboots\": true")).to_equal(true)
```

</details>

#### riscv32 canary value differs across two reboots

- riscv32 canary value differs across two reboots
   - Expected: log contains `"differs_across_reboots": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv32 canary value differs across two reboots")
val log: text = file_read(_arch_canary_log("riscv32"))
expect(log.contains("\"differs_across_reboots\": true")).to_equal(true)
```

</details>

### AC-5/R6 — per-arch entropy source matches HAL design

#### x86_64 entropy.spl uses rdrand or rdseed

- x86_64 entropy.spl uses rdrand or rdseed
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x86_64 entropy.spl uses rdrand or rdseed")
val body: text = file_read(_entropy_path("x86_64"))
val ok: bool = body.contains("rdrand") or body.contains("rdseed") or body.contains("RDRAND") or body.contains("RDSEED")
expect(ok).to_equal(true)
```

</details>

#### x86_32 entropy.spl uses rdrand (CPUID-gated)

- x86_32 entropy.spl uses rdrand (CPUID-gated)
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x86_32 entropy.spl uses rdrand (CPUID-gated)")
val body: text = file_read(_entropy_path("x86_32"))
val ok: bool = body.contains("rdrand") or body.contains("RDRAND")
expect(ok).to_equal(true)
```

</details>

#### arm64 entropy.spl probes RNDR or falls back to CNTVCT

- arm64 entropy.spl probes RNDR or falls back to CNTVCT
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm64 entropy.spl probes RNDR or falls back to CNTVCT")
val body: text = file_read(_entropy_path("arm64"))
val ok: bool = body.contains("rndr") or body.contains("RNDR") or body.contains("CNTVCT")
expect(ok).to_equal(true)
```

</details>

#### arm32 entropy.spl seeds from CNTVCT + DTB

- arm32 entropy.spl seeds from CNTVCT + DTB
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm32 entropy.spl seeds from CNTVCT + DTB")
val body: text = file_read(_entropy_path("arm32"))
val ok: bool = body.contains("CNTVCT") or body.contains("dtb") or body.contains("DTB")
expect(ok).to_equal(true)
```

</details>

#### riscv64 entropy.spl uses sbi_get_random or cycle+time+instret

- riscv64 entropy.spl uses sbi_get_random or cycle+time+instret
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv64 entropy.spl uses sbi_get_random or cycle+time+instret")
val body: text = file_read(_entropy_path("riscv64"))
val ok: bool = body.contains("sbi_get_random") or body.contains("instret") or body.contains("Zkr")
expect(ok).to_equal(true)
```

</details>

#### riscv32 entropy.spl uses sbi_get_random or cycle+time+instret

- riscv32 entropy.spl uses sbi_get_random or cycle+time+instret
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv32 entropy.spl uses sbi_get_random or cycle+time+instret")
val body: text = file_read(_entropy_path("riscv32"))
val ok: bool = body.contains("sbi_get_random") or body.contains("instret")
expect(ok).to_equal(true)
```

</details>

### AC-5 — W^X enforcement

#### harden audit report exists

- harden audit report exists
   - Expected: file_exists(HARDEN_REPORT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("harden audit report exists")
expect(file_exists(HARDEN_REPORT)).to_equal(true)
```

</details>

#### no W|X mapping anywhere in audited tree

- no W|X mapping anywhere in audited tree
   - Expected: r contains `"wx_violations": 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no W|X mapping anywhere in audited tree")
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"wx_violations\": 0")).to_equal(true)
```

</details>

#### x86_32 PAE NX is active when CONFIG_X86_32_PAE is set

- x86_32 PAE NX is active when CONFIG_X86_32_PAE is set
   - Expected: r contains `"x86_32_nx_status"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x86_32 PAE NX is active when CONFIG_X86_32_PAE is set")
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"x86_32_nx_status\"")).to_equal(true)
```

</details>

#### kernel write to .text page traps

- kernel write to .text page traps
   - Expected: r contains `"text_write_trap": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("kernel write to .text page traps")
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"text_write_trap\": true")).to_equal(true)
```

</details>

#### arm64 sandbox lowering maps non-exec rows to PXN and UXN

- arm64 sandbox lowering maps non-exec rows to PXN and UXN
   - Expected: body contains `arm64_sandbox_pte_bits_for_permissions`
   - Expected: body contains `PTE_PXN | PTE_UXN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm64 sandbox lowering maps non-exec rows to PXN and UXN")
val body: text = file_read("src/os/kernel/arch/arm64/paging.spl")
expect(body.contains("arm64_sandbox_pte_bits_for_permissions")).to_equal(true)
expect(body.contains("PTE_PXN | PTE_UXN")).to_equal(true)
```

</details>

#### riscv64 boot installs sandbox PMP plan before os_main

- riscv64 boot installs sandbox PMP plan before os_main
   - Expected: hook_index >= 0 is true
   - Expected: main_index >= 0 is true
   - Expected: hook_index < main_index is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("riscv64 boot installs sandbox PMP plan before os_main")
val body: text = file_read("src/os/kernel/arch/riscv64/boot.spl")
val hook_index = body.index_of("sandbox_boot_apply_embedded_riscv64")
val main_index = body.index_of("os_main()")
expect(hook_index >= 0).to_equal(true)
expect(main_index >= 0).to_equal(true)
expect(hook_index < main_index).to_equal(true)
```

</details>

#### arm64 boot installs sandbox MPU plan before boot complete

- arm64 boot installs sandbox MPU plan before boot complete
   - Expected: body contains `sandbox_boot_apply_embedded_arm_mpu()\n    _line_boot_complete()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm64 boot installs sandbox MPU plan before boot complete")
val body: text = file_read("src/os/kernel/arch/arm64/boot.spl")
expect(body.contains("sandbox_boot_apply_embedded_arm_mpu()\n    _line_boot_complete()")).to_equal(true)
```

</details>

#### arm32 boot output path installs sandbox MPU plan before returning

- arm32 boot output path installs sandbox MPU plan before returning
   - Expected: body contains `sandbox_boot_apply_embedded_arm_mpu()\n\n    BootOutputPort(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arm32 boot output path installs sandbox MPU plan before returning")
val body: text = file_read("src/os/kernel/arch/arm32/boot.spl")
expect(body.contains("sandbox_boot_apply_embedded_arm_mpu()\n\n    BootOutputPort(")).to_equal(true)
```

</details>

#### sandbox boot bridge has RISC-V and ARM64 backends

- sandbox boot bridge has RISC-V and ARM64 backends
   - Expected: body contains `pmp_write_plan_from_sandbox_lowering`
   - Expected: body contains `arm64_sandbox_pte_bits_from_lowering`
   - Expected: body contains `arm_mpu_mmio_write_plan_from_sandbox_lowering`
   - Expected: body contains `sandbox_boot_apply_embedded_arm_mpu`
   - Expected: body contains `mmio_write32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sandbox boot bridge has RISC-V and ARM64 backends")
val body: text = file_read("src/os/kernel/security/sandbox_boot_apply.spl")
expect(body.contains("pmp_write_plan_from_sandbox_lowering")).to_equal(true)
expect(body.contains("arm64_sandbox_pte_bits_from_lowering")).to_equal(true)
expect(body.contains("arm_mpu_mmio_write_plan_from_sandbox_lowering")).to_equal(true)
expect(body.contains("sandbox_boot_apply_embedded_arm_mpu")).to_equal(true)
expect(body.contains("mmio_write32")).to_equal(true)
```

</details>

#### sandbox boot bridge names linker metadata section bounds

- sandbox boot bridge names linker metadata section bounds
   - Expected: body contains `__simple_sandbox_start`
   - Expected: body contains `__simple_sandbox_end`
   - Expected: body contains `embedded_sandbox_section_bounds_valid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sandbox boot bridge names linker metadata section bounds")
val body: text = file_read("src/os/kernel/security/sandbox_boot_apply.spl")
expect(body.contains("__simple_sandbox_start")).to_equal(true)
expect(body.contains("__simple_sandbox_end")).to_equal(true)
expect(body.contains("embedded_sandbox_section_bounds_valid")).to_equal(true)
```

</details>

#### sandbox boot bridge validates embedded lowering before use

- sandbox boot bridge validates embedded lowering before use
   - Expected: body contains `end_addr > start_addr`
   - Expected: body contains `sandbox_lowering:`
   - Expected: body contains `pmp_region|`
   - Expected: body contains `return ""`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sandbox boot bridge validates embedded lowering before use")
val body: text = file_read("src/os/kernel/security/sandbox_boot_apply.spl")
expect(body.contains("end_addr > start_addr")).to_equal(true)
expect(body.contains("sandbox_lowering:")).to_equal(true)
expect(body.contains("pmp_region|")).to_equal(true)
expect(body.contains("return \"\"")).to_equal(true)
```

</details>

#### sandbox boot bridge reads embedded section bytes behind validation

- sandbox boot bridge reads embedded section bytes behind validation
   - Expected: body contains `embedded_sandbox_lowering_sdn_from_raw_bounds`
   - Expected: body contains `rt_bytes_from_raw`
   - Expected: body contains `rt_bytes_to_text`
   - Expected: body contains `embedded_sandbox_lowering_sdn_from_section(start_addr, end_addr, section_text)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sandbox boot bridge reads embedded section bytes behind validation")
val body: text = file_read("src/os/kernel/security/sandbox_boot_apply.spl")
expect(body.contains("embedded_sandbox_lowering_sdn_from_raw_bounds")).to_equal(true)
expect(body.contains("rt_bytes_from_raw")).to_equal(true)
expect(body.contains("rt_bytes_to_text")).to_equal(true)
expect(body.contains("embedded_sandbox_lowering_sdn_from_section(start_addr, end_addr, section_text)")).to_equal(true)
```

</details>

#### sandbox boot bridge gets linker section addresses from runtime providers

- sandbox boot bridge gets linker section addresses from runtime providers
   - Expected: body contains `rt_simple_sandbox_section_start`
   - Expected: body contains `rt_simple_sandbox_section_end`
   - Expected: body contains `embedded_sandbox_lowering_sdn_from_raw_bounds(\n        rt_simple_sandbox_sec... (full value in folded executable source)`
   - Expected: runtime contains `__simple_sandbox_start[] __attribute__((weak))`
   - Expected: runtime contains `__simple_sandbox_end[] __attribute__((weak))`
   - Expected: runtime contains `rt_simple_sandbox_section_start`
   - Expected: runtime contains `rt_simple_sandbox_section_end`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sandbox boot bridge gets linker section addresses from runtime providers")
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

- ARM and baremetal linker scripts preserve sandbox metadata sections
   - Expected: _linker_preserves_sandbox_metadata("src/os/kernel/arch/arm64/linker.ld") is true
   - Expected: _linker_preserves_sandbox_metadata("src/os/kernel/arch/arm32/linker.ld") is true
   - Expected: _linker_preserves_sandbox_metadata("src/compiler/70.backend/baremetal/arm/linker.ld") is true
   - Expected: _linker_preserves_sandbox_metadata("src/os/realtime/boot/arm.ld") is true
   - Expected: _linker_preserves_sandbox_metadata("examples/09_embedded/simple_os/arch/arm64/linker.ld") is true
   - Expected: _linker_preserves_sandbox_metadata("examples/09_embedded/simple_os/arch/arm64/fs_exec_linker.ld") is true
   - Expected: _linker_preserves_sandbox_metadata("examples/09_embedded/simple_os/arch/arm32/linker.ld") is true
   - Expected: _linker_preserves_sandbox_metadata("examples/09_embedded/simple_os/arch/arm32/fs_exec_linker.ld") is true
   - Expected: _linker_preserves_sandbox_metadata("examples/09_embedded/baremetal/baremetal/arm64.ld") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ARM and baremetal linker scripts preserve sandbox metadata sections")
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

- harden audit reports cap-check coverage = 100%
   - Expected: r contains `"cap_check_coverage_pct": 100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("harden audit reports cap-check coverage = 100%")
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"cap_check_coverage_pct\": 100")).to_equal(true)
```

</details>

#### no Syscall variant lacks a cap-check

- no Syscall variant lacks a cap-check
   - Expected: r contains `"syscall_variants_uncovered": 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no Syscall variant lacks a cap-check")
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"syscall_variants_uncovered\": 0")).to_equal(true)
```

</details>

### AC-5 — bounds-check intrinsic + @nocheck policy

#### no @nocheck outside arch/ HAL tree

- no @nocheck outside arch/ HAL tree
   - Expected: r contains `"nocheck_outside_hal": 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no @nocheck outside arch/ HAL tree")
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"nocheck_outside_hal\": 0")).to_equal(true)
```

</details>

#### no `unsafe` outside arch/ HAL tree

- no `unsafe` outside arch/ HAL tree
   - Expected: r contains `"unsafe_outside_hal": 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no `unsafe` outside arch/ HAL tree")
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"unsafe_outside_hal\": 0")).to_equal(true)
```

</details>

#### compiler emitted @check_bounds in arch-neutral kernel containers

- compiler emitted @check_bounds in arch-neutral kernel containers
   - Expected: r contains `"check_bounds_emitted": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiler emitted @check_bounds in arch-neutral kernel containers")
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"check_bounds_emitted\": true")).to_equal(true)
```

</details>

### AC-5 — bin/simple build check runs harden audit per-arch

#### harden audit per-arch summary present

- harden audit per-arch summary present
   - Expected: r contains `"per_arch_exit_codes"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("harden audit per-arch summary present")
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"per_arch_exit_codes\"")).to_equal(true)
```

</details>

#### every arch lane exit code is 0

- every arch lane exit code is 0
   - Expected: r contains `"all_arch_pass": true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every arch lane exit code is 0")
val r: text = file_read(HARDEN_REPORT)
expect(r.contains("\"all_arch_pass\": true")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/multiarch/hardening_gates_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AC-5/R6 — stack canary is not 0xDEADBEEFDEADBEEFUL, AC-5/R6 — per-arch entropy source matches HAL design, AC-5 — W^X enforcement, AC-5 — capability check at every syscall entry, AC-5 — bounds-check intrinsic + @nocheck policy, AC-5 — bin/simple build check runs harden audit per-arch.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `249d3af817702fdecdd8d8ff8a1b7cf735f03948cc98037074fe3cf45de7f33b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `249d3af817702fdecdd8d8ff8a1b7cf735f03948cc98037074fe3cf45de7f33b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `249d3af817702fdecdd8d8ff8a1b7cf735f03948cc98037074fe3cf45de7f33b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/multiarch/hardening_gates_spec.spl
mirror: doc/06_spec/unit/os/multiarch/hardening_gates_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/multiarch/hardening_gates_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/multiarch/hardening_gates_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/multiarch/hardening_gates_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simpleos_cxxabi.spl exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/multiarch/hardening_gates_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simpleos_cxxabi.spl does NOT contain the hardcoded constant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/multiarch/hardening_gates_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simpleos_cxxabi.spl does NOT contain the legacy DEADBEEF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
