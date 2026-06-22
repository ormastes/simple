# Os Packages Path Normalization Specification

> <details>

<!-- sdn-diagram:id=os_packages_path_normalization_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_packages_path_normalization_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_packages_path_normalization_spec -> std
os_packages_path_normalization_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_packages_path_normalization_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Packages Path Normalization Specification

## Scenarios

### OS package path normalization

#### places the kernel, core runtime, and shell on FreeBSD-style base paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val packages = list_all_packages(PkgArch.X86_64)

expect(packages[0].base.name).to_equal("simpleos-kernel")
expect(packages[0].base.files).to_equal(["/boot/kernel.elf"])

expect(packages[1].base.name).to_equal("simpleos-core")
expect(packages[1].base.files).to_equal([
    "/usr/lib/libos_core.a",
    "/usr/lib/libos_memory.a",
    "/usr/lib/libos_scheduler.a",
    "/usr/lib/libos_ipc.a",
    "/usr/lib/libos_drivers.a"
])

expect(packages[2].base.name).to_equal("simpleos-shell")
expect(packages[2].base.files).to_equal([
    "/bin/shell",
    "/etc/shell/profile.sdn"
])
```

</details>

#### splits tools across /sbin, /usr/sbin, /usr/bin, and /usr/local/bin

<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val packages = list_all_packages(PkgArch.X86_64)

expect(packages[4].base.name).to_equal("simpleos-tools")
expect(packages[4].base.files).to_equal([
    "/usr/sbin/pkg",
    "/sbin/bootctl",
    "/sbin/ifconfig",
    "/sbin/ping",
    "/usr/sbin/netstat",
    "/usr/sbin/lspci",
    "/usr/sbin/lsblk",
    "/usr/sbin/lsusb",
    "/usr/sbin/devinfo",
    "/usr/bin/tar",
    "/usr/bin/gzip",
    "/usr/bin/zip",
    "/usr/bin/ps",
    "/usr/bin/top",
    "/usr/bin/kill",
    "/usr/bin/log",
    "/usr/local/bin/wget",
    "/usr/bin/cmake",
    "/usr/bin/clang",
    "/usr/bin/clang-20",
    "/usr/bin/lld",
    "/usr/bin/ld.lld",
    "/usr/bin/llvm-ar",
    "/usr/bin/llvm-nm",
    "/usr/bin/llvm-ranlib",
    "/usr/bin/llvm-objdump",
    "/usr/bin/llvm-objcopy",
    "/usr/bin/llvm-strip",
    "/usr/bin/rustc",
    "/usr/bin/cargo",
    "/usr/bin/cargo-simpleos",
    "/usr/bin/ninja",
    "/SYS/CMAKEVER.TXT",
    "/SYS/CMAKEMAN.TXT",
    "/SYS/LLVMVER.TXT",
    "/SYS/LLVMMAN.TXT",
    "/SYS/CLANGVER.TXT",
    "/SYS/CLANGMAN.TXT",
    "/SYS/RUSTVER.TXT",
    "/SYS/RUSTMAN.TXT",
    "/SYS/CARGOVER.TXT",
    "/SYS/NINJAVER.TXT",
    "/SYS/NINJAMAN.TXT",
    "/SYS/TOOLSET.SDN",
    "/usr/share/simpleos/toolchain/llvm/hello.ll",
    "/usr/share/simpleos/toolchain/llvm/hello.s",
    "/usr/share/simpleos/toolchain/llvm/pipeline.step",
    "/usr/share/simpleos/toolchain/clang/hello.c",
    "/usr/share/simpleos/toolchain/clang/flags.rsp",
    "/usr/share/simpleos/toolchain/clang/pipeline.step",
    "/usr/share/simpleos/toolchain/rust/hello.rs",
    "/usr/share/simpleos/toolchain/rust/Cargo.toml",
    "/usr/share/simpleos/toolchain/rust/pipeline.step"
])
```

</details>

#### keeps installer media payloads under libexec and registry service binaries under /usr/sbin

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val packages = list_all_packages(PkgArch.X86_64)

expect(packages[8].base.name).to_equal("simpleos-installer")
expect(packages[8].base.files).to_equal([
    "/usr/libexec/simpleos-installer/installer",
    "/usr/libexec/simpleos-installer/packages/",
    "/usr/libexec/simpleos-installer/kernel/"
])

expect(packages[9].base.name).to_equal("simpleos-registry")
expect(packages[9].base.files).to_equal([
    "/usr/sbin/registry-server",
    "/etc/registry/config.sdn"
])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/packages/os_packages_path_normalization_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OS package path normalization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
