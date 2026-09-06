# Port Contract Specification

> <details>

<!-- sdn-diagram:id=port_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=port_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

port_contract_spec -> std
port_contract_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=port_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Port Contract Specification

## Scenarios

### MDSOC game port contract

#### defines the common rebuild profile outside Steam implementation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = game_port_profile(2048, "SimpleOS Steam 2048 Smoke", "2048", "https://github.com/gabrielecirulli/2048", "MIT", "/sys/apps/steam_2048")
expect(profile.profile_version).to_equal("steamos-rebuild-v1")
expect(profile.rebuild_target).to_equal("simpleos-native")
expect(profile.graphics_api).to_equal("sdl2_subset")
expect(profile.steam_facade_abi).to_equal("simple-steam-sffi-v1")
```

</details>

#### probes required rebuild capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = game_port_profile(2048, "SimpleOS Steam 2048 Smoke", "2048", "https://github.com/gabrielecirulli/2048", "MIT", "/sys/apps/steam_2048")
val readiness = game_port_probe(profile, game_port_core_capabilities())
expect(readiness.ready).to_equal(true)
expect(readiness.matched_count).to_equal(readiness.required_count)
```

</details>

#### fails closed when the rebuild toolchain contract is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = game_port_profile(2048, "SimpleOS Steam 2048 Smoke", "2048", "https://github.com/gabrielecirulli/2048", "MIT", "/sys/apps/steam_2048")
val readiness = game_port_probe(profile, ["simpleos_smf_packaging"])
expect(readiness.ready).to_equal(false)
expect(readiness.blocker).to_contain("simple_native_rebuild")
```

</details>

#### emits a package manifest and guest marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = game_port_profile(2048, "SimpleOS Steam 2048 Smoke", "2048", "https://github.com/gabrielecirulli/2048", "MIT", "/sys/apps/steam_2048")
val readiness = game_port_probe(profile, game_port_core_capabilities())
val manifest = game_port_manifest(profile)
val marker = game_port_marker(profile, readiness)
expect(manifest).to_contain("port_profile=steamos-rebuild-v1")
expect(manifest).to_contain("upstream=https://github.com/gabrielecirulli/2048")
expect(manifest).to_contain("steam_facade=simple-steam-sffi-v1")
expect(marker).to_contain("[game-port]")
expect(marker).to_contain("ready=true")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/game/port_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MDSOC game port contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
