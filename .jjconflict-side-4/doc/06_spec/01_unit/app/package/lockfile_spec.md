# Lockfile Specification

> <details>

<!-- sdn-diagram:id=lockfile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lockfile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lockfile_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lockfile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lockfile Specification

## Scenarios

### Package Lockfile

#### keeps the sync facade wired to the async lockfile implementation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_lockfile_facade_source()

expect(source).to_contain("export use std.gc_async_mut.package.lockfile.*")
```

</details>

#### keeps lockfile parsing, serialization, and validation entrypoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_lockfile_source()

expect(source).to_contain("fn parse_lockfile_string(content: text) -> Result<Lockfile, text>")
expect(source).to_contain("fn generate_lockfile(resolved: [ResolvedDependency]) -> Lockfile")
expect(source).to_contain("fn lockfile_to_string(lockfile: Lockfile) -> text")
expect(source).to_contain("fn validate_lockfile(lockfile: Lockfile) -> bool")
expect(source).to_contain("fn compare_lockfiles(old: Lockfile, new: Lockfile) -> LockfileChanges")
```

</details>

#### keeps checksum and dependency-reference guards in validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = package_lockfile_source()

expect(source).to_contain("fn validate_checksum(checksum: text) -> bool")
expect(source).to_contain("checksum.starts_with(\"sha256:\")")
expect(source).to_contain("fn extract_package_name_from_ref(ref: text) -> text")
expect(source).to_contain("lockfile.has_package(dep_name)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/package/lockfile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Package Lockfile

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
