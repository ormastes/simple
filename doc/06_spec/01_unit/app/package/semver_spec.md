# Semver Specification

> <details>

<!-- sdn-diagram:id=semver_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=semver_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

semver_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=semver_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semver Specification

## Scenarios

### Package Semver

#### keeps the sync facade wired to the async semver implementation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_semver_facade_source()

expect(source).to_contain("export use std.gc_async_mut.package.semver.*")
```

</details>

#### keeps comparison helpers for dependency resolution

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_semver_source()

expect(source).to_contain("fn version_equal(a: Version, b: Version) -> bool")
expect(source).to_contain("fn version_greater(a: Version, b: Version) -> bool")
expect(source).to_contain("fn version_less(a: Version, b: Version) -> bool")
expect(source).to_contain("fn version_greater_equal(a: Version, b: Version) -> bool")
expect(source).to_contain("fn version_less_equal(a: Version, b: Version) -> bool")
```

</details>

#### keeps constraint parsing for common semver operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_semver_source()

expect(source).to_contain("fn parse_constraint(s: text) -> (bool, VersionConstraint?, text)")
expect(source).to_contain("if trimmed == \"*\":")
expect(source).to_contain("if trimmed.starts_with(\"^\"):")
expect(source).to_contain("if trimmed.starts_with(\"~\"):")
expect(source).to_contain("if trimmed.starts_with(\">=\"):")
expect(source).to_contain("if trimmed.starts_with(\"<=\"):")
```

</details>

#### keeps constraint satisfaction logic for exact, range, caret, and tilde constraints

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_semver_source()

expect(source).to_contain("fn satisfies(version: Version, constraint: VersionConstraint) -> bool")
expect(source).to_contain("VersionConstraint.Exact(v):")
expect(source).to_contain("VersionConstraint.GreaterEqual(v):")
expect(source).to_contain("VersionConstraint.Caret(v):")
expect(source).to_contain("VersionConstraint.Tilde(v):")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/package/semver_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Package Semver

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
