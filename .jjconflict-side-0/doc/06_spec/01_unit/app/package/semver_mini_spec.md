# Semver Mini Specification

> <details>

<!-- sdn-diagram:id=semver_mini_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=semver_mini_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

semver_mini_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=semver_mini_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semver Mini Specification

## Scenarios

### Package Semver Mini

#### keeps the tuple-based parser contract that avoids generic Result hangs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_semver_source()

expect(source).to_contain("fn parse_version(s: text) -> (bool, Version?, text)")
expect(source).to_contain("fn parse_int_component(s: text) -> (bool, i64, text)")
expect(source).to_contain("return (false, nil, \"Version must have exactly 3 components (MAJOR.MINOR.PATCH)\")")
expect(source).to_contain("return (false, 0, \"Version component cannot be empty\")")
```

</details>

#### keeps prerelease and build metadata parsing paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_semver_source()

expect(source).to_contain("val parts = s.split(\"+\")")
expect(source).to_contain("val pre_parts = version_part.split(\"-\")")
expect(source).to_contain("prerelease: prerelease")
expect(source).to_contain("build: build")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/package/semver_mini_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Package Semver Mini

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
