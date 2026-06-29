# Manifest Specification

> <details>

<!-- sdn-diagram:id=manifest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=manifest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

manifest_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=manifest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Manifest Specification

## Scenarios

### Package Manifest

#### keeps the sync facade wired to the async manifest implementation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_manifest_facade_source()

expect(source).to_contain("export use std.gc_async_mut.package.manifest.*")
```

</details>

#### keeps bootstrap manifest generation and SDN serialization

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_manifest_source()

expect(source).to_contain("class PackageManifest")
expect(source).to_contain("static fn generate_bootstrap(version: text, platform: text) -> PackageManifest")
expect(source).to_contain("fn to_sdn() -> text")
expect(source).to_contain("name: \"simple-bootstrap\"")
expect(source).to_contain("app_dirs: [\"cli\", \"run\", \"compile\", \"check\", \"repl\"]")
```

</details>

#### keeps package manifest parsing and dependency construction

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_manifest_source()

expect(source).to_contain("fn parse_manifest_string(content: text) -> Result<Manifest, text>")
expect(source).to_contain("fn is_valid_package_name(name: text) -> bool")
expect(source).to_contain("fn parse_inline_text_array(raw: text) -> [text]")
expect(source).to_contain("fn build_manifest_dependency(name: text, version_field: text, git_url: text, path_value: text, ref_type: text, ref_value: text, optional: bool) -> Result<Dependency, text>")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/package/manifest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Package Manifest

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
