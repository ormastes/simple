# Disk Image Bake Specification

> Tests covering SimpleOS I5 disk-image bake harness.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Disk Image Bake Specification

## Scenarios

### SimpleOS I5 disk-image bake harness

#### requires clang_static when the toolchain bake marker is enabled

- requires clang_static when the toolchain bake marker is enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("requires clang_static when the toolchain bake marker is enabled")
val src = rt_file_read_text("src/os/port/disk_image_bake.spl") ?? ""
expect(src).to_contain("if io.file_exists(\"build/os/.bake_include_toolchain\"):")
expect(src).to_contain("toolchain marker set but clang_static missing")
expect(src).to_contain("return Err(\"bake: toolchain marker set but clang_static missing: \" + clang_static_path)")
```

</details>

#### requires rustc_static when the toolchain bake marker is enabled

- requires rustc_static when the toolchain bake marker is enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("requires rustc_static when the toolchain bake marker is enabled")
val src = rt_file_read_text("src/os/port/disk_image_bake.spl") ?? ""
expect(src).to_contain("toolchain marker set but rustc_static missing")
expect(src).to_contain("return Err(\"bake: toolchain marker set but rustc_static missing: \" + rustc_static_path)")
```

</details>

#### skips heavyweight bake examples in interpreter spec

- skips heavyweight bake examples in interpreter spec


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("skips heavyweight bake examples in interpreter spec")
"""Always green on CI because heavyweight bake verification is manual."""
return "skip: heavyweight bake examples are disabled in interpreter spec"
```

</details>

#### bake() returns Ok and produces both artifact files

- bake() returns Ok and produces both artifact files


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bake() returns Ok and produces both artifact files")
"""Call bake() and assert both output paths exist with minimum sizes."""
return "skip: heavyweight bake examples are disabled in interpreter spec"
```

</details>

#### disk image is at least 32 MiB

- disk image is at least 32 MiB


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("disk image is at least 32 MiB")
"""Verify the FAT32 image has the expected minimum size."""
return "skip: heavyweight bake examples are disabled in interpreter spec"
```

</details>

#### initramfs artifact exists with non-zero size

- initramfs artifact exists with non-zero size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("initramfs artifact exists with non-zero size")
"""Verify the initramfs output file was written."""
return "skip: heavyweight bake examples are disabled in interpreter spec"
```

</details>

#### initramfs artifact validates as a real archive

- initramfs artifact validates as a real archive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("initramfs artifact validates as a real archive")
"""Verify the packed output can be decompressed and listed."""
return "skip: heavyweight bake examples are disabled in interpreter spec"
```

</details>

#### writes multi-payload disk image

- writes multi-payload disk image


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("writes multi-payload disk image")
"""Create a config with 2 payloads and assert both directory entries
are present in the raw image bytes (first two 32-byte dir entries)."""
return "skip: heavyweight bake examples are disabled in interpreter spec"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/integration/os/port/disk_image_bake_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS I5 disk-image bake harness.
- SimpleOS I5 disk-image bake harness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `567c288837dbccdb8347f012c4d680ced66734192f2dd98bbec29f5afb9aaf9c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `567c288837dbccdb8347f012c4d680ced66734192f2dd98bbec29f5afb9aaf9c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `567c288837dbccdb8347f012c4d680ced66734192f2dd98bbec29f5afb9aaf9c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/os/port/disk_image_bake_spec.spl
mirror: doc/06_spec/integration/os/port/disk_image_bake_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/os/port/disk_image_bake_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/os/port/disk_image_bake_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/os/port/disk_image_bake_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires clang_static when the toolchain bake marker is enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/os/port/disk_image_bake_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires rustc_static when the toolchain bake marker is enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/os/port/disk_image_bake_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips heavyweight bake examples in interpreter spec' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
