# rustc_static_e2e_spec

> Lint-only: validates symbol resolution + IF-08 marker conventions for

<!-- sdn-diagram:id=rustc_static_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rustc_static_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rustc_static_e2e_spec -> std
rustc_static_e2e_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rustc_static_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rustc_static_e2e_spec

Lint-only: validates symbol resolution + IF-08 marker conventions for

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/port/rustc_static_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Lint-only: validates symbol resolution + IF-08 marker conventions for
    Phase 3 rustc_static smoke. Disk paths and markers referenced without
    invocation. Behavioural body env-gated until Team B static binary lands.
    Markers: [phase-2-rustc-version] [phase-2-rustc-compile-ok]

## Scenarios

### rustc_static in-guest QEMU e2e contract

#### rustc_static binary paths and spawn symbol resolve at lint time

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set — lint-only validation passed"
if false:
    val _pid = x86_64_fs_exec_spawn_hello_world_smf()
    val _p = "/usr/bin/rustc_static"
    val _fb = "/sys/apps/rustc_static"
    val _m1 = "[phase-2-rustc-version]"
    val _m2 = "[phase-2-rustc-compile-ok]"
return "skip: behavioural run blocked on Phase 3 Team B binary"
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
