# Image Builder Artifact Specification

> Tests covering Image builder artifacts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Image Builder Artifact Specification

## Scenarios

### Image builder artifacts

#### writes a staged disk image tree and deploy manifest

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- writes a staged disk image tree and deploy manifest
   - Expected: rt_file_write_text(simple_payload, "SMF_FAKE_TARGET_SIMPLE\n") is true
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
   - Expected: rt_file_exists("{output}.contents/rootfs/bin/simple") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/bin/simple.smf") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/usr/bin/simple") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/usr/bin/simple.smf") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/sys/apps/simple_compiler") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/sys/apps/simple_interpreter") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/sys/apps/simple_loader") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/SYS/SIMPLETOOL.SDN") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes a staged disk image tree and deploy manifest")
val dir = "build/test-artifacts/image-builder"
_reset_dir(dir)
val output = "{dir}/simpleos-x86_64.img"
val simple_payload = "{dir}/simple-target.smf"
expect(rt_file_write_text(simple_payload, "SMF_FAKE_TARGET_SIMPLE\n")).to_equal(true)
val result = build_install_image_with_simple_binary(PkgArch.X86_64, "", "", output, 64, simple_payload)
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
expect(rt_file_exists("{output}.contents/rootfs/bin/simple")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/bin/simple.smf")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/usr/bin/simple")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/usr/bin/simple.smf")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/sys/apps/simple_compiler")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/sys/apps/simple_interpreter")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/sys/apps/simple_loader")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/SYS/SIMPLETOOL.SDN")).to_equal(true)
val llvm_manifest = rt_file_read_text("{output}.contents/rootfs/SYS/LLVMMAN.TXT")
val clang_manifest = rt_file_read_text("{output}.contents/rootfs/SYS/CLANGMAN.TXT")
val rust_manifest = rt_file_read_text("{output}.contents/rootfs/SYS/RUSTMAN.TXT")
val simple_manifest = rt_file_read_text("{output}.contents/rootfs/SYS/SIMPLETOOL.SDN")
expect(llvm_manifest).to_contain("mode=native-filesystem-app")
expect(llvm_manifest).to_contain("status=standalone-required")
expect(clang_manifest).to_contain("mode=native-filesystem-app")
expect(clang_manifest).to_contain("status=standalone-required")
expect(rust_manifest).to_contain("mode=native-filesystem-app")
expect(rust_manifest).to_contain("status=standalone-required")
expect(simple_manifest).to_contain("runtime_source = \"simpleos-filesystem\"")
expect(simple_manifest).to_contain("role = \"/usr/bin/simple\"")
```

</details>

#### embeds the real clang_static binary and sysroot when present

- embeds the real clang_static binary and sysroot when present
   - Expected: rt_file_write_text(fake_clang, "FAKE_CLANG_STATIC_ELF\n") is true
   - Expected: rt_file_write_text("{fake_root}/sysroot/lib/libsimpleos_c.a", "AR_FAKE\n") is true
   - Expected: rt_file_write_text("{fake_root}/sysroot/share/simpleos/simpleos.ld", "SECTIONS { }\n") is true
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists("{output}.contents/rootfs/usr/bin/clang") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/sys/apps/clang") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/usr/lib/libsimpleos_c.a") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/usr/share/simpleos/lib/libsimpleos_c.a") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/usr/share/simpleos/share/simpleos/simpleos.ld") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("embeds the real clang_static binary and sysroot when present")
val dir = "build/test-artifacts/image-builder-clang"
_reset_dir(dir)
val fake_root = "{dir}/toolchain"
rt_process_run("/bin/sh", ["-c", "mkdir -p '" + fake_root + "/bin' '" + fake_root + "/sysroot/lib' '" + fake_root + "/sysroot/share/simpleos'"])
val fake_clang = "{fake_root}/bin/clang_static"
expect(rt_file_write_text(fake_clang, "FAKE_CLANG_STATIC_ELF\n")).to_equal(true)
expect(rt_file_write_text("{fake_root}/sysroot/lib/libsimpleos_c.a", "AR_FAKE\n")).to_equal(true)
expect(rt_file_write_text("{fake_root}/sysroot/share/simpleos/simpleos.ld", "SECTIONS { }\n")).to_equal(true)
rt_env_set("SIMPLEOS_CLANG_BINARY", fake_clang)
rt_env_set("SIMPLEOS_SYSROOT", "{fake_root}/sysroot")
val output = "{dir}/simpleos-x86_64.img"
val result = build_install_image_with_simple_binary(PkgArch.X86_64, "", "", output, 64, "")
rt_env_set("SIMPLEOS_CLANG_BINARY", "")
rt_env_set("SIMPLEOS_SYSROOT", "")
expect(result.is_ok()).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/usr/bin/clang")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/sys/apps/clang")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/usr/lib/libsimpleos_c.a")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/usr/share/simpleos/lib/libsimpleos_c.a")).to_equal(true)
expect(rt_file_exists("{output}.contents/rootfs/usr/share/simpleos/share/simpleos/simpleos.ld")).to_equal(true)
val embedded_clang = rt_file_read_text("{output}.contents/rootfs/usr/bin/clang")
val clang_tool = rt_file_read_text("{output}.contents/rootfs/SYS/CLANGTOOL.SDN")
expect(embedded_clang).to_contain("FAKE_CLANG_STATIC_ELF")
expect(clang_tool).to_contain("status = \"embedded\"")
expect(clang_tool).to_contain("sysroot_embedded = true")
```

</details>

#### records a fixture marker when clang_static is not built

- records a fixture marker when clang_static is not built
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists("{output}.contents/rootfs/sys/apps/clang") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records a fixture marker when clang_static is not built")
val dir = "build/test-artifacts/image-builder-clang-fixture"
_reset_dir(dir)
# Point the override at a non-existent path so the example stays
# hermetic even when the real build/os/clang_static exists on the host.
rt_env_set("SIMPLEOS_CLANG_BINARY", "{dir}/missing/clang_static")
rt_env_set("SIMPLEOS_SYSROOT", "")
val output = "{dir}/simpleos-x86_64.img"
val result = build_install_image_with_simple_binary(PkgArch.X86_64, "", "", output, 64, "")
rt_env_set("SIMPLEOS_CLANG_BINARY", "")
expect(result.is_ok()).to_equal(true)
val clang_tool = rt_file_read_text("{output}.contents/rootfs/SYS/CLANGTOOL.SDN")
expect(clang_tool).to_contain("fixture: clang_static not built")
expect(rt_file_exists("{output}.contents/rootfs/sys/apps/clang")).to_equal(true)
```

</details>

#### writes installer-media staging for non-x86 architectures

- writes installer-media staging for non-x86 architectures
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists(output) is true
   - Expected: rt_file_exists("{output}.manifest.sdn") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/usr/libexec/simpleos-installer/installer") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes installer-media staging for non-x86 architectures")
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

- writes rootfs backend markers for alternate hosted backends while keeping FAT32 carrier
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists("{output}.contents/rootfs/etc/rootfs.sdn") is true
   - Expected: rt_file_exists("{output}.contents/rootfs/SYS/ROOTFS.CFG") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes rootfs backend markers for alternate hosted backends while keeping FAT32 carrier")
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
| Source | `test/unit/os/installer/image_builder_artifact_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Image builder artifacts.
- Image builder artifacts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `967f0045c9fa1dec839833aa20e4595ffcf37a7853d197800e250b74f93f409a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `967f0045c9fa1dec839833aa20e4595ffcf37a7853d197800e250b74f93f409a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `967f0045c9fa1dec839833aa20e4595ffcf37a7853d197800e250b74f93f409a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/installer/image_builder_artifact_spec.spl
mirror: doc/06_spec/unit/os/installer/image_builder_artifact_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/installer/image_builder_artifact_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/installer/image_builder_artifact_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/installer/image_builder_artifact_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes a staged disk image tree and deploy manifest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/installer/image_builder_artifact_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'embeds the real clang_static binary and sysroot when present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/installer/image_builder_artifact_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records a fixture marker when clang_static is not built' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
