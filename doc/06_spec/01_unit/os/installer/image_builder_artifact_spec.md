# Image Builder Artifact Specification

> 1.  reset dir

<!-- sdn-diagram:id=image_builder_artifact_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=image_builder_artifact_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

image_builder_artifact_spec -> std
image_builder_artifact_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=image_builder_artifact_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Image Builder Artifact Specification

## Scenarios

### Image builder artifacts

#### writes a staged disk image tree and deploy manifest

1.  reset dir
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists(output) is true
   - Expected: rt_file_exists("{output}.manifest.sdn") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/etc/fstab") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/sbin/init") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/sys/apps/llvm") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/sys/apps/clang") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/sys/apps/rust") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/SYS/LLVMMAN.TXT") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/SYS/CLANGMAN.TXT") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/SYS/RUSTMAN.TXT") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/usr/share/simpleos/toolchain/llvm/hello.ll") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/usr/share/simpleos/toolchain/clang/hello.c") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/usr/share/simpleos/toolchain/rust/hello.rs") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "build/test-artifacts/image-builder"
_reset_dir(dir)
val output = "{dir}/simpleos-x86_64.img"
val result = build_install_image(PkgArch.X86_64, "", "", output, 64)
expect(result.is_ok()).to_equal(true)
expect(rt_file_exists(output)).to_equal(true)
expect(rt_file_exists("{output}.manifest.sdn")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/etc/fstab")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/sbin/init")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/sys/apps/llvm")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/sys/apps/clang")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/sys/apps/rust")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/SYS/LLVMMAN.TXT")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/SYS/CLANGMAN.TXT")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/SYS/RUSTMAN.TXT")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/usr/share/simpleos/toolchain/llvm/hello.ll")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/usr/share/simpleos/toolchain/clang/hello.c")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/usr/share/simpleos/toolchain/rust/hello.rs")).to_equal(true)
val llvm_manifest = rt_file_read_text("{output}.contents/rootfs/SYS/LLVMMAN.TXT")
val clang_manifest = rt_file_read_text("{output}.contents/rootfs/SYS/CLANGMAN.TXT")
val rust_manifest = rt_file_read_text("{output}.contents/rootfs/SYS/RUSTMAN.TXT")
expect(llvm_manifest).to_contain("mode=native-filesystem-app")
expect(llvm_manifest).to_contain("status=standalone-required")
expect(clang_manifest).to_contain("mode=native-filesystem-app")
expect(clang_manifest).to_contain("status=standalone-required")
expect(rust_manifest).to_contain("mode=native-filesystem-app")
expect(rust_manifest).to_contain("status=standalone-required")
```

</details>

#### writes installer-media staging for non-x86 architectures

1.  reset dir
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists(output) is true
   - Expected: rt_file_exists("{output}.manifest.sdn") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/usr/libexec/simpleos-installer/installer") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "build/test-artifacts/image-builder-installer"
_reset_dir(dir)
val output = "{dir}/simpleos-arm64-installer.iso"
val result = build_usb_installer_image(PkgArch.Arm64, "", "", output, 64)
expect(result.is_ok()).to_equal(true)
expect(rt_file_exists(output)).to_equal(true)
expect(rt_file_exists("{output}.manifest.sdn")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/usr/libexec/simpleos-installer/installer")).to_equal(true)
```

</details>

#### writes rootfs backend markers for alternate hosted backends while keeping FAT32 carrier

1.  reset dir
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists("{output}.contents/rootfs/etc/rootfs.sdn") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/SYS/ROOTFS.CFG") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "build/test-artifacts/image-builder-rootfs"
_reset_dir(dir)
val output = "{dir}/simpleos-x86_64-nvfs.img"
val result = build_install_image_with_rootfs(PkgArch.X86_64, "", "", output, 64, "nvfs")
expect(result.is_ok()).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/etc/rootfs.sdn")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/SYS/ROOTFS.CFG")).to_equal(true)
val manifest = rt_file_read_text("{output}.manifest.sdn")
val rootfs_cfg = rt_file_read_text("{output}.contents/rootfs/etc/rootfs.sdn")
val boot_marker = rt_file_read_text("{output}.contents/rootfs/SYS/ROOTFS.CFG")
expect(manifest).to_contain("rootfs_backend = \"nvfs\"")
expect(rootfs_cfg).to_contain("backend = \"nvfs\"")
expect(rootfs_cfg).to_contain("carrier = \"fat32\"")
expect(boot_marker).to_contain("rootfs_backend=nvfs")
expect(boot_marker).to_contain("rootfs_carrier=fat32")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/installer/image_builder_artifact_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Image builder artifacts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
