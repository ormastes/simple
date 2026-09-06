# Make Os Disk Contract Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Make Os Disk Contract Specification

## Scenarios

### make_os_disk target payload and FAT contracts

#### selects and validates explicit target Simple payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/os/make_os_disk.shs")
expect(script).to_contain("validate_elf_payload \"$SIMPLEOS_SIMPLE_BINARY\" 62 Simple")
expect(script).to_contain("validate_simple_payload_provenance \"$SIMPLEOS_SIMPLE_BINARY\"")
expect(script).to_contain("target=x86_64-unknown-simpleos")
expect(script).to_contain("artifact_sha256")
expect(script).to_contain("bin/release/aarch64-unknown-simpleos/simple")
expect(script).to_contain("validate_elf_payload \"$SIMPLEOS_SIMPLE_BINARY\" 183 Simple")
expect(script).to_contain("bin/release/riscv64-unknown-simpleos/simple")
expect(script).to_contain("validate_elf_payload \"$SIMPLEOS_SIMPLE_BINARY\" 243 Simple")
expect(script).to_contain("validate_elf_payload \"$SIMPLEOS_CLANG_BINARY\" 62 Clang")
expect(script).to_contain("validate_elf_payload \"$SIMPLEOS_CLANG_BINARY\" 183 Clang")
expect(script).to_contain("validate_elf_payload \"$SIMPLEOS_CLANG_BINARY\" 243 Clang")
expect(script).to_contain("validate_elf_payload \"$SIMPLEOS_LLC_BINARY\" 62 LLC")
expect(script).to_contain("validate_elf_payload \"$SIMPLEOS_LLC_BINARY\" 183 LLC")
expect(script).to_contain("validate_elf_payload \"$SIMPLEOS_LLC_BINARY\" 243 LLC")
expect(script).to_contain("validate_elf_payload \"$SIMPLEOS_LLD_BINARY\" 62 LLD")
expect(script).to_contain("validate_elf_payload \"$SIMPLEOS_LLD_BINARY\" 183 LLD")
expect(script).to_contain("validate_elf_payload \"$SIMPLEOS_LLD_BINARY\" 243 LLD")
expect(script).to_contain("invalid SimpleOS $payload_name payload (not ELF)")
expect(script).to_contain("od -An -tu1 -j 4 -N 2")
expect(script).to_contain("[ \"$1\" -ne 2 ] || [ \"$2\" -ne 1 ]")
expect(script).to_contain("expected little-endian ELF64")
expect(script).to_contain("$(( $1 + 256 * $2 ))")
expect(script).to_contain("export SIMPLEOS_SIMPLE_BINARY")
```

</details>

#### runs the disk-free payload and kernel ELF validation matrices

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (payload_out, payload_err, payload_rc) = rt_process_run_timeout(
    "/bin/sh", ["scripts/os/make_os_disk.shs", "--self-test"], 30000)
expect(payload_rc).to_equal(0)
expect(payload_err).to_equal("")
expect(payload_out).to_contain("PASS make_os_disk target payload validation self-test")

val (kernel_out, kernel_err, kernel_rc) = rt_process_run_timeout(
    "/bin/sh", ["scripts/check/check-simpleos-x86-kernel-elf.shs", "--self-test"], 30000)
expect(kernel_rc).to_equal(0)
expect(kernel_err).to_equal("")
expect(kernel_out).to_contain("simpleos_x86_kernel_elf_self_test=pass")
```

</details>

#### gates canonical x86 filesystem kernels before packaging or QEMU

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = "check-simpleos-x86-kernel-elf.shs"
expect(file_read("scripts/os/build_fsexec_prod_ring3.shs")).to_contain(gate)
expect(file_read("scripts/os/build_clang_disk.shs")).to_contain(gate)
expect(file_read("scripts/os/ssh_simple_hello_uefi.shs")).to_contain(gate)
```

</details>

#### links usr bin for any staged executable payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("scripts/os/make_os_disk.c")
expect(source).to_contain("if (simple_usr_cluster || clang_bin_cluster || llc_bin_cluster || lld_bin_cluster)")
expect(source).to_contain("put_dir_entry(usr, &usr_n, \"BIN        \", usr_bin_cluster, 0, 0x10);")
```

</details>

#### reuses the staged clang hello source cluster at root

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("scripts/os/make_os_disk.c")
expect(source).to_contain("put_dir_entry(sys, &sys_n, \"CLANGHELC  \", clang_c_cluster, clang_c.len, 0x20);")
expect(source).to_contain("put_dir_entry(root, &root_n, \"HELLO   C  \", clang_c_cluster, clang_c.len, 0x20);")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/make_os_disk_contract_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- make_os_disk target payload and FAT contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
