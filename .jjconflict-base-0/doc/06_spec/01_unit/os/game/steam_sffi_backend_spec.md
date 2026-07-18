# Steam Sffi Backend Specification

> <details>

<!-- sdn-diagram:id=steam_sffi_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=steam_sffi_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

steam_sffi_backend_spec -> std
steam_sffi_backend_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=steam_sffi_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Steam Sffi Backend Specification

## Scenarios

### Steam SFFI backend contract

#### publishes the configured bridge discovery contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = steam_sffi_backend_plan()
expect(plan.env_var).to_equal("SIMPLE_STEAM_BRIDGE_PATH")
expect(plan.bridge_abi).to_equal("simple-steam-sffi-v1")
expect(plan.candidates.len()).to_equal(8)
expect(plan.required_symbols.len()).to_equal(20)
expect(plan.required_os_capabilities.len()).to_equal(11)
expect(steam_sffi_bridge_env_var()).to_equal("SIMPLE_STEAM_BRIDGE_PATH")
expect(steam_sffi_bridge_abi()).to_equal("simple-steam-sffi-v1")
expect(steam_sffi_bridge_candidates().join(",")).to_contain("libsteam_api.so")
expect(steam_sffi_bridge_health_symbols().join(",")).to_equal("simple_steam_bridge_is_mock,simple_steam_bridge_real_backend_ready")
```

</details>

#### resolves explicit paths before known candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val explicit = steam_sffi_find_bridge_path_from_candidates("/opt/steam/libsimple_steam_bridge.so", [])
expect(explicit).to_equal("/opt/steam/libsimple_steam_bridge.so")

val known = steam_sffi_find_bridge_path_from_candidates("", ["build/os/game/steam/libsimple_steam_bridge.so"])
expect(known).to_equal("build/os/game/steam/libsimple_steam_bridge.so")

val missing = steam_sffi_find_bridge_path_from_candidates("", ["other/path/libsimple_steam_bridge.so"])
expect(missing).to_equal("")
```

</details>

#### reports missing bridge path before symbol readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = steam_sffi_probe_from_evidence("", 0, true, steam_api_backend_required_symbols(), steam_api_backend_required_os_capabilities())
expect(status.ready).to_equal(false)
expect(status.blocker).to_equal("missing Steam SFFI bridge path")
expect(status.matched_symbol_count).to_equal(20)
expect(status.matched_os_capability_count).to_equal(11)
```

</details>

#### reports loaded bridge readiness from real symbol evidence

1. steam api backend required symbols
2. steam api backend required os capabilities
   - Expected: loaded_missing_client.ready is false
   - Expected: loaded_missing_client.blocker equals `missing authenticated Steam client`
3. steam api backend required symbols
4. steam api backend required os capabilities
   - Expected: ready.ready is true
   - Expected: ready.blocker equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loaded_missing_client = steam_sffi_probe_from_evidence(
    "build/os/game/steam/libsimple_steam_bridge.so",
    42,
    false,
    steam_api_backend_required_symbols(),
    steam_api_backend_required_os_capabilities()
)
expect(loaded_missing_client.ready).to_equal(false)
expect(loaded_missing_client.blocker).to_equal("missing authenticated Steam client")

val ready = steam_sffi_probe_from_evidence(
    "build/os/game/steam/libsimple_steam_bridge.so",
    42,
    true,
    steam_api_backend_required_symbols(),
    steam_api_backend_required_os_capabilities()
)
expect(ready.ready).to_equal(true)
expect(ready.blocker).to_equal("")
```

</details>

#### does not treat mock bridge symbols as real backend readiness

1. steam api backend required symbols
2. steam api backend required os capabilities
   - Expected: mock.ready is false
   - Expected: mock.mock_bridge is true
   - Expected: mock.real_backend_ready is false
   - Expected: mock.blocker equals `Steam SFFI bridge is a mock fixture`
3. steam api backend required symbols
4. steam api backend required os capabilities
   - Expected: no_backend.ready is false
   - Expected: no_backend.blocker equals `Steam SFFI bridge has no real Valve backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = steam_sffi_probe_from_evidence_with_health(
    "build/os/game/steam/libsimple_steam_bridge.so",
    42,
    true,
    steam_api_backend_required_symbols(),
    steam_api_backend_required_os_capabilities(),
    true,
    false
)
expect(mock.ready).to_equal(false)
expect(mock.mock_bridge).to_equal(true)
expect(mock.real_backend_ready).to_equal(false)
expect(mock.blocker).to_equal("Steam SFFI bridge is a mock fixture")

val no_backend = steam_sffi_probe_from_evidence_with_health(
    "build/os/game/steam/libsimple_steam_bridge.so",
    42,
    true,
    steam_api_backend_required_symbols(),
    steam_api_backend_required_os_capabilities(),
    false,
    false
)
expect(no_backend.ready).to_equal(false)
expect(no_backend.blocker).to_equal("Steam SFFI bridge has no real Valve backend")
```

</details>

#### lists exact missing symbols and SimpleOS capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_symbols = steam_sffi_missing_symbols(["SteamAPI_Init", "SteamAPI_Shutdown"])
expect(missing_symbols.len()).to_equal(18)
expect(missing_symbols.join(",")).to_contain("SteamInternal_CreateInterface")

val missing_os = steam_sffi_missing_os_capabilities(["elf64_dynamic_loader"])
expect(missing_os.len()).to_equal(10)
expect(missing_os.join(",")).to_contain("steam_runtime_container")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/game/steam_sffi_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Steam SFFI backend contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
