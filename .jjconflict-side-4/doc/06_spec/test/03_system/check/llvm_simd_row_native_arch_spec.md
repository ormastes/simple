# LLVM SIMD Row Native Architecture Contract

> vector load/store instructions.

<!-- sdn-diagram:id=llvm_simd_row_native_arch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_simd_row_native_arch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_simd_row_native_arch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_simd_row_native_arch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLVM SIMD Row Native Architecture Contract

vector load/store instructions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/llvm_simd_row_native_arch_spec.spl` |
| Updated | 2026-07-10 |
| Generator | `simple spipe-docgen` (Simple) |

## Requirements

- REQ-LLVM-SIMD-ROW-001: All hosted target binaries preserve exact row pixels.
- REQ-LLVM-SIMD-ROW-002: Each target executes native SIMD and RVV contains
  vector load/store instructions.

## Plan

Run the canonical architecture wrapper and inspect its evidence file.

## Design

The wrapper fails closed when a compiler, linker, emulator, exact-output check,
hit assertion, target file type, or vector instruction is missing.

## Research

N/A

## Scenarios

### LLVM SIMD row native architecture contract

<details>
<summary>Advanced: builds exact vectorized x86 AArch64 and RVV binaries</summary>

#### builds exact vectorized x86 AArch64 and RVV binaries _(slow)_

- Run the strict hosted architecture wrapper
   - Expected: code equals `0`
- Require every target and aggregate result to pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the strict hosted architecture wrapper")
val root = "build/test-llvm-simd-row-native-arch"
val (_, _, code) = process_run("/bin/sh", ["-c", "rm -rf " + root + " && BUILD_DIR=" + root + " sh scripts/check/check-llvm-simd-row-native-arch.shs"])
expect(code).to_equal(0)

step("Require every target and aggregate result to pass")
val evidence = file_read(root + "/evidence.env")
expect(evidence).to_contain("llvm_simd_row_native_arch_x86_64_status=pass")
expect(evidence).to_contain("llvm_simd_row_native_arch_aarch64_status=pass")
expect(evidence).to_contain("llvm_simd_row_native_arch_riscv64_rvv_status=pass")
expect(evidence).to_contain("llvm_simd_row_native_arch_status=pass")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
