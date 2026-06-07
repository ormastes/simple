# Steamworks Bridge Specification

> <details>

<!-- sdn-diagram:id=steamworks_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=steamworks_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

steamworks_bridge_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=steamworks_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Steamworks Bridge Specification

## Scenarios

### Steamworks IPC bridge

#### connect with valid socket path returns is_ok=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = steamworks_connect("/tmp/.steam/steam.sock")
expect(conn.is_ok).to_equal(true)
expect(conn.conn_id).to_be_greater_than(0)
```

</details>

#### connect with empty path returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = steamworks_connect("")
expect(conn.is_ok).to_equal(false)
expect(conn.error).to_equal("missing-socket-path")
```

</details>

#### two connects return distinct conn_ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c1 = steamworks_connect("/tmp/.steam/steam.sock")
val c2 = steamworks_connect("/tmp/.steam/steam.sock")
expect(c1.conn_id).to_not_equal(c2.conn_id)
```

</details>

#### validate_app returns owned=true for non-empty app_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = steamworks_connect("/tmp/.steam/steam.sock")
val result = steamworks_validate_app(conn.conn_id, "480")
expect(result.is_ok).to_equal(true)
expect(result.owned).to_equal(true)
expect(result.app_id).to_equal("480")
```

</details>

#### validate_app returns owned=false for empty app_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = steamworks_connect("/tmp/.steam/steam.sock")
val result = steamworks_validate_app(conn.conn_id, "")
expect(result.owned).to_equal(false)
```

</details>

#### validate_app returns is_ok=false on invalid connection

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = steamworks_validate_app(0, "480")
expect(result.is_ok).to_equal(false)
```

</details>

#### unlock_achievement returns unlocked=true for valid name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = steamworks_connect("/tmp/.steam/steam.sock")
val result = steamworks_unlock_achievement(conn.conn_id, "ACH_WIN_ONE_GAME")
expect(result.is_ok).to_equal(true)
expect(result.unlocked).to_equal(true)
```

</details>

#### unlock_achievement returns unlocked=false for empty name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = steamworks_connect("/tmp/.steam/steam.sock")
val result = steamworks_unlock_achievement(conn.conn_id, "")
expect(result.unlocked).to_equal(false)
```

</details>

#### disconnect removes connection

1. steamworks disconnect
   - Expected: result.is_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val conn = steamworks_connect("/tmp/.steam/steam.sock")
steamworks_disconnect(conn.conn_id)
val result = steamworks_validate_app(conn.conn_id, "480")
expect(result.is_ok).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/steam/steamworks_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Steamworks IPC bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
