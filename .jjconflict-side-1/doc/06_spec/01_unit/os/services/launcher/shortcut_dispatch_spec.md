# Launcher Shortcut Dispatch Specification

> Regression coverage for `launcher_shortcut_dispatch(key, modifiers)`.

<!-- sdn-diagram:id=shortcut_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shortcut_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shortcut_dispatch_spec -> std
shortcut_dispatch_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shortcut_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Launcher Shortcut Dispatch Specification

Regression coverage for `launcher_shortcut_dispatch(key, modifiers)`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/launcher/shortcut_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Regression coverage for `launcher_shortcut_dispatch(key, modifiers)`.

The x86_64 desktop_e2e baremetal entry dispatches Meta+B and Meta+H
through this path to drive the real launcher shortcut flow. The
dispatch must find the registered Browser Demo / Hello World slots
and return true. A previous bug hardcoded the `_app_key` / `_app_mod`
/ `_app_name` / `_app_index_by_name` helpers so `launcher_register`
always hit the "existing" branch and `app_count` stayed at 0, which
made the dispatch loop (`while i < app_count`) never match anything
— this spec locks that behaviour down.

## Scenarios

### Launcher shortcut dispatch

#### seeds canonical default apps with non-zero app_count

1. launcher init
   - Expected: launcher_get_app_count() equals `12`
   - Expected: launcher_get_app_name(0) equals `Hello World`
   - Expected: launcher_get_app_name(3) equals `Browser Demo`
   - Expected: launcher_get_app_name(4) equals `Editor`
   - Expected: launcher_get_app_name(10) equals `Clang`
   - Expected: launcher_get_app_name(11) equals `Rust`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
expect(launcher_get_app_count()).to_equal(12)
expect(launcher_get_app_name(0)).to_equal("Hello World")
expect(launcher_get_app_name(3)).to_equal("Browser Demo")
expect(launcher_get_app_name(4)).to_equal("Editor")
expect(launcher_get_app_name(10)).to_equal("Clang")
expect(launcher_get_app_name(11)).to_equal("Rust")
```

</details>

#### dispatches Meta+B to the Browser Demo slot

1. launcher init
   - Expected: dispatched is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val dispatched = launcher_shortcut_dispatch(KEY_B, MOD_META)
expect(dispatched).to_equal(true)
```

</details>

#### dispatches Meta+H to the Hello World slot

1. launcher init
   - Expected: dispatched is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val dispatched = launcher_shortcut_dispatch(KEY_H, MOD_META)
expect(dispatched).to_equal(true)
```

</details>

#### returns false for an unregistered shortcut

1. launcher init
   - Expected: dispatched is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val dispatched = launcher_shortcut_dispatch(KEY_UNUSED, MOD_META)
expect(dispatched).to_equal(false)
```

</details>

#### returns false when only the modifier matches but not the key

1. launcher init
   - Expected: dispatched is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
# Modifier matches Meta, but 0x00 is not a registered key.
val dispatched = launcher_shortcut_dispatch(0x00, MOD_META)
expect(dispatched).to_equal(false)
```

</details>

#### returns false when only the key matches but not the modifier

1. launcher init
   - Expected: dispatched is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
# Key matches Browser Demo's 'B', but no modifier means no match.
val dispatched = launcher_shortcut_dispatch(KEY_B, 0)
expect(dispatched).to_equal(false)
```

</details>

#### dispatches to a dynamically registered shortcut

1. launcher init
   - Expected: registered is true
   - Expected: launcher_get_app_count() equals `13`
   - Expected: launcher_find_by_name("Demo App") equals `12`
   - Expected: dispatched is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val registered = launcher_register("Demo App", "/apps/demo", "D", 0x44, MOD_META)
expect(registered).to_equal(true)
expect(launcher_get_app_count()).to_equal(13)
expect(launcher_find_by_name("Demo App")).to_equal(12)
val dispatched = launcher_shortcut_dispatch(0x44, MOD_META)
expect(dispatched).to_equal(true)
```

</details>

#### dispatches Meta+E to the seeded Editor slot

1. launcher init
   - Expected: dispatched is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val dispatched = launcher_shortcut_dispatch(KEY_E, MOD_META)
expect(dispatched).to_equal(true)
```

</details>

#### seeded fallback reports dispatched without synthetic pid when spawn fails

1. launcher init
   - Expected: dispatched is true
   - Expected: pid equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val dispatched = launcher_shortcut_dispatch(KEY_H, MOD_META)
expect(dispatched).to_equal(true)
val pid = launcher_get_last_launch_pid()
expect(pid).to_equal(0)
```

</details>

#### seeded fallback reports dispatched for Meta+F when spawn fails

1. launcher init
   - Expected: dispatched is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val dispatched = launcher_shortcut_dispatch(KEY_F, MOD_META)
expect(dispatched).to_equal(true)
```

</details>

#### seeded fallback reports dispatched for Meta+T when spawn fails

1. launcher init
   - Expected: dispatched is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val dispatched = launcher_shortcut_dispatch(KEY_T, MOD_META)
expect(dispatched).to_equal(true)
```

</details>

#### seeded fallback reports dispatched for Meta+G Clang when spawn fails

1. launcher init
   - Expected: dispatched is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val dispatched = launcher_shortcut_dispatch(KEY_G, MOD_META)
expect(dispatched).to_equal(true)
```

</details>

#### seeded fallback still rejects non-Meta modifier

1. launcher init
   - Expected: dispatched is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
launcher_init()
val dispatched = launcher_shortcut_dispatch(KEY_H, 0)
expect(dispatched).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
