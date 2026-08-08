# Steam 2048 Demo Specification

> <details>

<!-- sdn-diagram:id=steam_2048_demo_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=steam_2048_demo_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

steam_2048_demo_spec -> std
steam_2048_demo_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=steam_2048_demo_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Steam 2048 Demo Specification

## Scenarios

### SimpleOS Steam 2048 smoke game

#### keeps the deterministic 2048 merge rule executable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val merged = steam_2048_merge_left([2, 2, 0, 0])
expect(steam_2048_row_text(merged)).to_equal("4,0,0,0")
```

</details>

#### binds the open source 2048 game to the Steam facade

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = steam_2048_demo_run()
expect(run.source_game).to_equal("2048")
expect(run.upstream_url).to_equal("https://github.com/gabrielecirulli/2048")
expect(run.license).to_equal("MIT")
expect(run.steam.state.achievement_unlocked).to_equal(true)
expect(run.steam.state.drm_ticket).to_equal("simple-drm-ticket")
expect(run.port_profile.profile_version).to_equal("steamos-rebuild-v1")
expect(run.port_profile.rebuild_target).to_equal("simpleos-native")
```

</details>

#### emits a guest-checkable marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val marker = steam_2048_demo_marker()
expect(marker).to_contain("[steam-2048-demo]")
expect(marker).to_contain("runtime=SteamLinuxRuntime/soldier")
expect(marker).to_contain("network=true")
expect(steam_2048_simpleos_guest_marker_ready(marker)).to_equal(true)
```

</details>

#### emits a rebuild-porting manifest and marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = steam_2048_port_manifest()
val marker = steam_2048_port_marker()
expect(manifest).to_contain("port_profile=steamos-rebuild-v1")
expect(manifest).to_contain("source=2048")
expect(manifest).to_contain("rebuild_target=simpleos-native")
expect(marker).to_contain("steam_facade=simple-steam-sffi-v1")
expect(steam_2048_port_guest_marker_ready(marker)).to_equal(true)
```

</details>

#### rejects incomplete guest serial evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(steam_2048_simpleos_guest_marker_ready("[steam-2048-demo] source=2048")).to_equal(false)
expect(steam_2048_port_guest_marker_ready("[game-port] profile=steamos-rebuild-v1 source=2048")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/game/steam_2048_demo_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Steam 2048 smoke game

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
