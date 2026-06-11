# Steam Runtime Specification

> <details>

<!-- sdn-diagram:id=steam_runtime_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=steam_runtime_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

steam_runtime_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=steam_runtime_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Steam Runtime Specification

## Scenarios

### Steam runtime detection

#### detect with full soldier evidence returns is_ok=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = steam_runtime_detect("steam-runtime abi-x86_64 soldier")
expect(info.is_ok).to_equal(true)
expect(info.generation).to_equal("soldier")
expect(info.abi).to_equal("x86_64")
```

</details>

#### detect with sniper generation returns is_ok=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = steam_runtime_detect("steam-runtime abi-x86_64 sniper")
expect(info.is_ok).to_equal(true)
expect(info.generation).to_equal("sniper")
```

</details>

#### detect without steam-runtime token returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = steam_runtime_detect("abi-x86_64 soldier")
expect(info.is_ok).to_equal(false)
expect(info.error).to_equal("missing-steam-runtime")
```

</details>

#### detect without abi-x86_64 token returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = steam_runtime_detect("steam-runtime soldier")
expect(info.is_ok).to_equal(false)
expect(info.error).to_equal("missing-abi-x86_64")
```

</details>

#### detect without generation token returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = steam_runtime_detect("steam-runtime abi-x86_64")
expect(info.is_ok).to_equal(false)
expect(info.error).to_equal("missing-steam-linux-runtime-generation")
```

</details>

#### library_path is non-empty for valid info

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = steam_runtime_detect("steam-runtime abi-x86_64 soldier")
val path = steam_runtime_library_path(info)
expect(path).to_contain("soldier")
```

</details>

#### library_path is empty for invalid info

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = steam_runtime_detect("")
val path = steam_runtime_library_path(info)
expect(path).to_equal("")
```

</details>

#### rootfs_mount returns non-empty path for valid info

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = steam_runtime_detect("steam-runtime abi-x86_64 soldier")
val mount = steam_runtime_rootfs_mount(info)
expect(mount).to_contain("pressure-vessel")
```

</details>

#### rootfs_mount returns empty string for invalid info

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = steam_runtime_detect("")
expect(steam_runtime_rootfs_mount(info)).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/steam/steam_runtime_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Steam runtime detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
