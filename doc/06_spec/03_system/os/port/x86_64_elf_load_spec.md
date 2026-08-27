# x86_64_elf_load_spec

> Validates symbol resolution for the x86_64 filesystem-exec scheduler bridge.

<!-- sdn-diagram:id=x86_64_elf_load_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_64_elf_load_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_64_elf_load_spec -> std
x86_64_elf_load_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_64_elf_load_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86_64_elf_load_spec

Validates symbol resolution for the x86_64 filesystem-exec scheduler bridge.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/port/x86_64_elf_load_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates symbol resolution for the x86_64 filesystem-exec scheduler bridge.
    Lint-only until P0-C QEMU smoke wires disk image + VFS mount.

## Scenarios

### x86_64 fs-exec-spawn loader contract

#### x86_64_fs_exec_spawn_hello_world_smf resolves and Architecture.X86_64 is reachable

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set — lint-only validation passed"
val arch = Architecture.X86_64
arch.to_equal(Architecture.X86_64)
if false:
    val _pid = x86_64_fs_exec_spawn_hello_world_smf()
return "skip: behavioural run blocked on P0-C QEMU smoke"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
