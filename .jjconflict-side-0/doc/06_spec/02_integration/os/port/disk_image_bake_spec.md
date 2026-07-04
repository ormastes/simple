# Disk Image Bake Specification

> _Static bake contracts plus disabled heavyweight examples._

<!-- sdn-diagram:id=disk_image_bake_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=disk_image_bake_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

disk_image_bake_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=disk_image_bake_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Disk Image Bake Specification

## Scenarios

### SimpleOS I5 disk-image bake harness
_Static bake contracts plus disabled heavyweight examples._

#### requires clang_static when the toolchain bake marker is enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/os/port/disk_image_bake.spl")
expect(src).to_contain("if io.file_exists(\"build/os/.bake_include_toolchain\"):")
expect(src).to_contain("toolchain marker set but clang_static missing")
expect(src).to_contain("return Err(\"bake: toolchain marker set but clang_static missing: \" + clang_static_path)")
```

</details>

#### requires rustc_static when the toolchain bake marker is enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read("src/os/port/disk_image_bake.spl")
expect(src).to_contain("toolchain marker set but rustc_static missing")
expect(src).to_contain("return Err(\"bake: toolchain marker set but rustc_static missing: \" + rustc_static_path)")
```

</details>

#### skips heavyweight bake examples in interpreter spec

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
return "skip: heavyweight bake examples are disabled in interpreter spec"
```

</details>

#### bake() returns Ok and produces both artifact files

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
return "skip: heavyweight bake examples are disabled in interpreter spec"
```

</details>

#### disk image is at least 32 MiB

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
return "skip: heavyweight bake examples are disabled in interpreter spec"
```

</details>

#### initramfs artifact exists with non-zero size

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
return "skip: heavyweight bake examples are disabled in interpreter spec"
```

</details>

#### initramfs artifact validates as a real archive

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
return "skip: heavyweight bake examples are disabled in interpreter spec"
```

</details>

#### writes multi-payload disk image

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
return "skip: heavyweight bake examples are disabled in interpreter spec"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/disk_image_bake_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
