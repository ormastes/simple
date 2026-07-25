# Launcher Init Spec — SYS-GUI-006 Blocker 2 regression guard

> Focused guard for the `[desktop-e2e] launcher:fail registered=0` live-lane

<!-- sdn-diagram:id=launcher_init_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=launcher_init_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

launcher_init_spec -> std
launcher_init_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=launcher_init_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Launcher Init Spec — SYS-GUI-006 Blocker 2 regression guard

Focused guard for the `[desktop-e2e] launcher:fail registered=0` live-lane

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/launcher/launcher_init_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Focused guard for the `[desktop-e2e] launcher:fail registered=0` live-lane
regression. `DesktopShell.init()` invokes `launcher_init()` which registers
canonical default apps into the module-level registry (`app_name`, `app_path`,
... backed by fixed-size `[T; 32]` globals in
`src/os/services/launcher/launcher.spl`).

In the hosted interpreter this path works and `launcher_get_app_count()`
returns a nonzero app count. In the baremetal x86_64 desktop lane the same call returns 0,
indicating either module-level array storage is zeroed across the call
boundary, or `DesktopShell.init()`'s method body never executes (bare-method
dispatch picking the wrong `.init()` symbol). Either way, the hosted lane
must keep guarding the launcher-side API contract so any OS-side regression
of `launcher_init()` itself trips a unit failure before shipping to QEMU.

Diagnostic:
  doc/08_tracking/todo/launcher_module_storage_fix_plan_2026-04-14.md

## Scenarios

### Launcher init — desktop-ready precondition

#### registers at least one app after launcher_init()

1. launcher init


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val count = launcher_get_app_count()
expect(count > 0).to_be_true()
```

</details>

#### registers the canonical default desktop apps

1. launcher init


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val count = launcher_get_app_count()
expect(count >= 12).to_be_true()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
