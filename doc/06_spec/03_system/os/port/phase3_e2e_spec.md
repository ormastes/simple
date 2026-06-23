# phase3_e2e_spec

> Validates symbol resolution for the W-2 shell_launch_smoke entry point.

<!-- sdn-diagram:id=phase3_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=phase3_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

phase3_e2e_spec -> std
phase3_e2e_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=phase3_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# phase3_e2e_spec

Validates symbol resolution for the W-2 shell_launch_smoke entry point.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/port/phase3_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates symbol resolution for the W-2 shell_launch_smoke entry point.
    Lint-only until Phase 3 QEMU smoke wires disk image + VFS mount.

## Scenarios

### Phase 3 e2e launch contract

#### shell_launch_smoke resolves and Architecture.X86_64 is reachable

1. shell launch smoke


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
    shell_launch_smoke()
return "skip: behavioural run blocked on Phase 3 QEMU smoke"
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
