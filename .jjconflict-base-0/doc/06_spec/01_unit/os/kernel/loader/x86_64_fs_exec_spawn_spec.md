# X86 64 Fs Exec Spawn Specification

> <details>

<!-- sdn-diagram:id=x86_64_fs_exec_spawn_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_64_fs_exec_spawn_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_64_fs_exec_spawn_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_64_fs_exec_spawn_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 64 Fs Exec Spawn Specification

## Scenarios

### x86_64 filesystem exec seeded app spawn

#### spawns known seeded disk apps without requiring VFS byte materialization

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hello_pid = x86_64_fs_exec_spawn("/sys/apps/hello_world.smf", [], [])
val clang_pid = x86_64_fs_exec_spawn("/sys/apps/clang", ["/usr/share/simpleos/toolchain/clang/hello.c"], [])
val rust_pid = x86_64_fs_exec_spawn("/sys/apps/rust", ["/usr/share/simpleos/toolchain/rust/Cargo.toml"], [])
val simple_pid = x86_64_fs_exec_spawn("/sys/apps/simple.smf", ["--version"], [])

expect(hello_pid > 0).to_equal(true)
expect(clang_pid).to_equal(hello_pid + 1)
expect(rust_pid).to_equal(clang_pid + 1)
expect(simple_pid).to_equal(rust_pid + 1)
```

</details>

#### keeps unknown executables on the generic VFS failure path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pid = x86_64_fs_exec_spawn("/sys/apps/definitely_missing", [], [])

expect(pid).to_equal(-2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86_64 filesystem exec seeded app spawn

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
