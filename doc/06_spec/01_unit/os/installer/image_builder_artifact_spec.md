# Image Builder Artifact Specification

> Tests covering Image builder artifacts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Image Builder Artifact Specification

## Scenarios

### Image builder artifacts

#### rejects a marker file pretending to be a target Simple payload

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a marker file pretending to be a target Simple payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a marker file pretending to be a target Simple payload")
val dir = "build/test-artifacts/image-builder"
_reset_dir(dir)
val output = "{dir}/simpleos-x86_64.img"
val simple_payload = "{dir}/simple-target.smf"
expect(rt_file_write_text(simple_payload, "SMF_FAKE_TARGET_SIMPLE\n")).to_be(true)
val result = build_install_image_with_simple_binary(PkgArch.X86_64, "", "", output, 64, simple_payload)
expect(result.is_err()).to_be(true)
if val Err(message) = result:
    expect(message).to_contain("lacks target provenance")
expect(rt_file_exists("{output}.contents/rootfs/SYS/SIMPLETOOL.SDN")).to_be(false)
```

</details>

#### rejects a digest-bound header-only ELF before staging any toolchain role

- rejects a digest-bound header-only ELF before staging any toolchain role


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a digest-bound header-only ELF before staging any toolchain role")
val dir = "build/test-artifacts/image-builder-header-only"
_reset_dir(dir)
val output = "{dir}/simpleos-x86_64.img"
val simple_payload = "{dir}/simple-target"
val bytes = _header_only_elf()
expect(rt_file_write_bytes(simple_payload, bytes)).to_be(true)
expect(rt_file_write_text("{simple_payload}.build_stamp",
    _simple_stamp(sha256_u8_hex(bytes), "bin/release/simple"))).to_be(true)
val result = build_install_image_with_simple_binary(
    PkgArch.X86_64, "", "", output, 64, simple_payload)
expect(result.is_err()).to_be(true)
if val Err(message) = result:
    expect(message).to_contain(IMAGE_BOUNDED_FILE_READER_UNAVAILABLE_V1)
expect(rt_file_exists("{output}.contents/rootfs/bin/simple")).to_be(false)
```

</details>

#### rejects a digest-bound bootstrap seed receipt before staging

- rejects a digest-bound bootstrap seed receipt before staging


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a digest-bound bootstrap seed receipt before staging")
val dir = "build/test-artifacts/image-builder-seed-receipt"
_reset_dir(dir)
val output = "{dir}/simpleos-x86_64.img"
val simple_payload = "{dir}/simple-target"
val bytes = _header_only_elf()
expect(rt_file_write_bytes(simple_payload, bytes)).to_be(true)
expect(rt_file_write_text("{simple_payload}.build_stamp",
    _simple_stamp(sha256_u8_hex(bytes),
        "src/compiler_rust/target/bootstrap/simple"))).to_be(true)
val result = build_install_image_with_simple_binary(
    PkgArch.X86_64, "", "", output, 64, simple_payload)
expect(result.is_err()).to_be(true)
if val Err(message) = result:
    expect(message).to_contain(IMAGE_BOUNDED_FILE_READER_UNAVAILABLE_V1)
expect(rt_file_exists("{output}.contents/rootfs/bin/simple")).to_be(false)
```

</details>

#### rejects a payload whose build receipt digest does not bind its bytes

- rejects a payload whose build receipt digest does not bind its bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a payload whose build receipt digest does not bind its bytes")
val dir = "build/test-artifacts/image-builder-digest-mismatch"
_reset_dir(dir)
val output = "{dir}/simpleos-x86_64.img"
val simple_payload = "{dir}/simple-target"
val bytes = _header_only_elf()
expect(rt_file_write_bytes(simple_payload, bytes)).to_be(true)
expect(rt_file_write_text("{simple_payload}.build_stamp",
    _simple_stamp("f" * 64, "bin/release/simple"))).to_be(true)
val result = build_install_image_with_simple_binary(
    PkgArch.X86_64, "", "", output, 64, simple_payload)
expect(result.is_err()).to_be(true)
if val Err(message) = result:
    expect(message).to_contain(IMAGE_BOUNDED_FILE_READER_UNAVAILABLE_V1)
expect(rt_file_exists("{output}.contents/rootfs/bin/simple")).to_be(false)
```

</details>

#### records missing installer executables without staging false payloads

- records missing installer executables without staging false payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records missing installer executables without staging false payloads")
val dir = "build/test-artifacts/image-builder-installer"
_reset_dir(dir)
val output = "{dir}/simpleos-arm64-installer.iso"
val result = build_usb_installer_image(PkgArch.Arm64, "", "", output, 64)
expect(result.is_ok()).to_be(true)
expect(rt_file_exists(output)).to_be(true)
expect(rt_file_exists("{output}.manifest.sdn")).to_be(true)
expect(rt_file_exists("{output}.contents/rootfs/usr/libexec/simpleos-installer/installer")).to_be(false)
val manifest = rt_file_read_text("{output}.manifest.sdn")
expect(manifest).to_contain("[blocked_package_payload]")
expect(manifest).to_contain("path = \"/usr/libexec/simpleos-installer/installer\"")
expect(manifest).to_contain("reason = \"package-placeholder-rejected\"")
expect(rt_file_exists("{output}.contents/rootfs/sbin/init")).to_be(false)
expect(rt_file_exists("{output}.contents/rootfs/bin/simplebox")).to_be(false)
expect(rt_file_exists("{output}.contents/rootfs/boot/kernel.elf")).to_be(false)
expect(manifest).to_contain("path = \"/sbin/init\"")
expect(manifest).to_contain("path = \"/bin/simplebox\"")
expect(manifest).to_contain("path = \"/boot/kernel.elf\"")
expect(manifest).to_contain("path = \"/usr/bin/clang\"")
expect(manifest).to_contain("path = \"/sys/apps/clang\"")
expect(manifest).to_contain("path = \"/usr/bin/rustc\"")
expect(manifest).to_contain("path = \"/sys/apps/rust\"")
expect(manifest).to_contain("path = \"/usr/lib/libwm.a\"")
expect(manifest).to_contain("reason = \"package-bytes-unavailable\"")
expect(rt_file_exists("{output}.contents/rootfs/usr/lib/libwm.a")).to_be(false)
```

</details>

#### writes rootfs backend markers for alternate hosted backends while keeping FAT32 carrier

- writes rootfs backend markers for alternate hosted backends while keeping FAT32 carrier


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
expect(result.is_ok()).to_be(true)
expect(rt_file_exists("{output}.contents/rootfs/etc/rootfs.sdn")).to_be(true)
expect(rt_file_exists("{output}.contents/rootfs/SYS/ROOTFS.CFG")).to_be(true)
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Image builder artifacts.
- Image builder artifacts

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `058010d8a5c786544cf2a9d4bb5b943b96113cccc7edafea1d5aaff604451e26`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `058010d8a5c786544cf2a9d4bb5b943b96113cccc7edafea1d5aaff604451e26`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `058010d8a5c786544cf2a9d4bb5b943b96113cccc7edafea1d5aaff604451e26`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/installer/image_builder_artifact_spec.spl
mirror: doc/06_spec/01_unit/os/installer/image_builder_artifact_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/installer/image_builder_artifact_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/installer/image_builder_artifact_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/installer/image_builder_artifact_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a marker file pretending to be a target Simple payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/installer/image_builder_artifact_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a digest-bound header-only ELF before staging any toolchain role' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/installer/image_builder_artifact_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a digest-bound bootstrap seed receipt before staging' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
