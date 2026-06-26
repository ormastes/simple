# Ffi Specification

> <details>

<!-- sdn-diagram:id=ffi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ffi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ffi_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ffi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ffi Specification

## Scenarios

### Package FFI

#### keeps checksum and archive entrypoints available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_ffi_source()

expect(source).to_contain("fn calculate_checksum(file_path: text) -> text")
expect(source).to_contain("fn create_tarball(source_dir: text, output_path: text) -> bool")
expect(source).to_contain("fn extract_tarball(tarball_path: text, dest_dir: text) -> bool")
```

</details>

#### keeps filesystem primitives available for package install flows

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_ffi_source()

expect(source).to_contain("fn mkdir_all(dir_path: text) -> bool")
expect(source).to_contain("fn remove_dir_all(dir_path: text) -> bool")
expect(source).to_contain("fn copy_file(src_path: text, dst_path: text) -> bool")
expect(source).to_contain("fn path_exists(path: text) -> bool")
expect(source).to_contain("fn is_directory(path: text) -> bool")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/package/ffi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Package FFI

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
