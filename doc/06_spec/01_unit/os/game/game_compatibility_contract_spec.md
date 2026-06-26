# Game Compatibility Contract Specification

> <details>

<!-- sdn-diagram:id=game_compatibility_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game_compatibility_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game_compatibility_contract_spec -> std
game_compatibility_contract_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game_compatibility_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game Compatibility Contract Specification

## Scenarios

### SimpleOS game compatibility platform contract

#### requires Linux ABI before native Linux games are ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_linux = game_target_native_linux(false, true, true, true, true, true)
val ready_linux = game_target_native_linux(true, true, true, true, true, true)
expect(game_target_ready(missing_linux)).to_equal(false)
expect(game_target_blocker(missing_linux)).to_equal("missing-linux-abi")
expect(game_target_ready(ready_linux)).to_equal(true)
expect(game_target_marker(ready_linux)).to_contain("[game-platform] target=native-linux blocker=ready")
```

</details>

#### requires Steam Runtime before Steam Linux games are ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_runtime = game_target_steam_linux(true, true, true, true, true, true, false)
val ready_runtime = game_target_steam_linux(true, true, true, true, true, true, true)
expect(game_target_blocker(no_runtime)).to_equal("missing-steam-runtime")
expect(game_target_ready(ready_runtime)).to_equal(true)
```

</details>

#### requires Proton host after Linux, Vulkan, audio, input, prefix, network, and Steam Runtime

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_vulkan = game_target_proton_x86(true, false, true, true, true, true, true, true)
val no_proton = game_target_proton_x86(true, true, true, true, true, true, true, false)
val ready_proton = game_target_proton_x86(true, true, true, true, true, true, true, true)
expect(game_target_blocker(no_vulkan)).to_equal("missing-vulkan")
expect(game_target_blocker(no_proton)).to_equal("missing-proton-host")
expect(game_target_ready(ready_proton)).to_equal(true)
```

</details>

#### blocks translated Proton on CPU translation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val translated = game_target_proton_translated(true, true, true, true, true, true, true, true, false)
expect(game_target_ready(translated)).to_equal(false)
expect(game_target_blocker(translated)).to_equal("missing-cpu-translation")
```

</details>

#### allows Simple-native games without Linux ABI

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_native = game_target_simple_native(true, true, true, true, true)
expect(game_target_ready(simple_native)).to_equal(true)
expect(game_target_blocker(simple_native)).to_equal("ready")
```

</details>

#### requires full game prefix layout

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val partial = game_runtime_prefix("123456", true, true, false, true, true, true)
val full = game_runtime_prefix("123456", true, true, true, true, true, true)
expect(game_runtime_prefix_ready(partial)).to_equal(false)
expect(game_runtime_prefix_blocker(partial)).to_equal("missing-shadercache:/games/app_123456/shadercache")
expect(game_runtime_prefix_ready(full)).to_equal(true)
expect(game_runtime_prefix_blocker(full)).to_equal("ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/game/game_compatibility_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS game compatibility platform contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
