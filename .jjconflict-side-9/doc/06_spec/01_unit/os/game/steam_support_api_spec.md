# Steam Support Api Specification

> <details>

<!-- sdn-diagram:id=steam_support_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=steam_support_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

steam_support_api_spec -> std
steam_support_api_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=steam_support_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Steam Support Api Specification

## Scenarios

### SimpleOS Steam API facade

#### fails closed until initialized

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surface = steam_support_api_surface(2048, "2048", "/games/app_2048/compatdata")
val facade = steam_api_facade(surface)
expect(steam_api_ready(facade)).to_equal(false)
expect(steam_api_readiness_blocker(facade)).to_equal("SteamAPI_Init not called")
```

</details>

#### initializes a pure Simple SFFI surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surface = steam_support_api_surface(2048, "2048", "/games/app_2048/compatdata")
val facade = steam_api_init(steam_api_facade(surface))
expect(steam_api_ready(facade)).to_equal(true)
expect(steam_api_sffi_bridge_name(facade)).to_equal("simple-steam-sffi-v1")
expect(steam_api_summary(facade)).to_contain("ready=true")
```

</details>

#### records common Steamworks-style game state

1. var facade = steam api init
2. facade = steam api begin session
3. facade = steam api runtime env
4. facade = steam api launch options
5. facade = steam api friend identity
6. facade = steam api network message
7. facade = steam api unlock achievement
8. facade = steam api write stat
9. facade = steam api cloud write
10. facade = steam api join lobby
11. facade = steam api request drm ticket
   - Expected: facade.state.session_started is true
   - Expected: facade.state.runtime_env equals `SteamLinuxRuntime/soldier`
   - Expected: facade.state.launch_options equals `-simpleos-smoke`
   - Expected: facade.state.friend_persona equals `Simple Player`
   - Expected: facade.state.network_message equals `ready`
   - Expected: facade.state.achievement_unlocked is true
   - Expected: facade.state.stat_value equals `4`
   - Expected: facade.state.cloud_bytes_written equals `64`
   - Expected: facade.state.lobby_member_count equals `1`
   - Expected: facade.state.drm_ticket equals `ticket`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surface = steam_support_api_surface(2048, "2048", "/games/app_2048/compatdata")
var facade = steam_api_init(steam_api_facade(surface))
facade = steam_api_begin_session(facade)
facade = steam_api_runtime_env(facade, "SteamLinuxRuntime/soldier")
facade = steam_api_launch_options(facade, "-simpleos-smoke")
facade = steam_api_friend_identity(facade, "friend-1", "Simple Player")
facade = steam_api_network_message(facade, "peer", "reliable", "ready")
facade = steam_api_unlock_achievement(facade, "FIRST_MERGE")
facade = steam_api_write_stat(facade, "score", 4)
facade = steam_api_cloud_write(facade, "save.sdn", 64)
facade = steam_api_join_lobby(facade, "local-lobby", 1)
facade = steam_api_request_drm_ticket(facade, "ticket")

expect(facade.state.session_started).to_equal(true)
expect(facade.state.runtime_env).to_equal("SteamLinuxRuntime/soldier")
expect(facade.state.launch_options).to_equal("-simpleos-smoke")
expect(facade.state.friend_persona).to_equal("Simple Player")
expect(facade.state.network_message).to_equal("ready")
expect(facade.state.achievement_unlocked).to_equal(true)
expect(facade.state.stat_value).to_equal(4)
expect(facade.state.cloud_bytes_written).to_equal(64)
expect(facade.state.lobby_member_count).to_equal(1)
expect(facade.state.drm_ticket).to_equal("ticket")
```

</details>

#### advertises the pure Simple Steamworks interface catalog

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val interfaces = steam_api_interfaces()
expect(steam_api_interface_count()).to_equal(32)
expect(interfaces.join(",")).to_contain("ISteamUser")
expect(interfaces.join(",")).to_contain("ISteamAppTicket")
expect(interfaces.join(",")).to_contain("ISteamGameCoordinator")
expect(interfaces.join(",")).to_contain("ISteamHTTP")
expect(interfaces.join(",")).to_contain("ISteamTimeline")
expect(interfaces.join(",")).to_contain("SteamEncryptedAppTicket")
expect(interfaces.join(",")).to_contain("steam_gameserver")
expect(steam_api_interface_supported("ISteamApps")).to_equal(true)
expect(steam_api_interface_supported("ISteamNetworkingSockets")).to_equal(true)
expect(steam_api_interface_supported("ISteamUnknown")).to_equal(false)
expect(steam_api_real_backend_ready()).to_equal(false)
expect(steam_api_real_backend_blocker()).to_contain("upstream Steamworks SDK bridge")
```

</details>

#### records wider Steam domain state without a native Valve dependency

1. var facade = steam api init
2. facade = steam api auth session ticket
3. facade = steam api app install dir
4. facade = steam api activate overlay
5. facade = steam api input action
6. facade = steam api write screenshot
7. facade = steam api publish ugc
8. facade = steam api authorize microtxn
9. facade = steam api persona state
10. facade = steam api p2p packet
   - Expected: facade.state.auth_session_ticket equals `auth-ticket`
   - Expected: facade.state.install_dir equals `/games/app_2048/root`
   - Expected: facade.state.overlay_dialog equals `Friends`
   - Expected: facade.state.input_action equals `MoveLeft`
   - Expected: facade.state.screenshot_path equals `/games/app_2048/screenshots/first.png`
   - Expected: facade.state.ugc_title equals `SimpleOS board`
   - Expected: facade.state.microtxn_authorized is true
   - Expected: facade.state.persona_state equals `online`
   - Expected: facade.state.p2p_packet_bytes equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val surface = steam_support_api_surface(2048, "2048", "/games/app_2048/compatdata")
var facade = steam_api_init(steam_api_facade(surface))
facade = steam_api_auth_session_ticket(facade, "auth-ticket")
facade = steam_api_app_install_dir(facade, "/games/app_2048/root")
facade = steam_api_activate_overlay(facade, "Friends")
facade = steam_api_input_action(facade, "MoveLeft", 1)
facade = steam_api_write_screenshot(facade, "/games/app_2048/screenshots/first.png")
facade = steam_api_publish_ugc(facade, "ugc-1", "SimpleOS board")
facade = steam_api_authorize_microtxn(facade, "order-1", true)
facade = steam_api_persona_state(facade, "online")
facade = steam_api_p2p_packet(facade, "peer-1", 32)

expect(facade.state.auth_session_ticket).to_equal("auth-ticket")
expect(facade.state.install_dir).to_equal("/games/app_2048/root")
expect(facade.state.overlay_dialog).to_equal("Friends")
expect(facade.state.input_action).to_equal("MoveLeft")
expect(facade.state.screenshot_path).to_equal("/games/app_2048/screenshots/first.png")
expect(facade.state.ugc_title).to_equal("SimpleOS board")
expect(facade.state.microtxn_authorized).to_equal(true)
expect(facade.state.persona_state).to_equal("online")
expect(facade.state.p2p_packet_bytes).to_equal(32)
```

</details>

#### keeps real Steam backend readiness behind an executable SFFI gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_client = steam_api_probe_backend(false, [], [])
expect(no_client.ready).to_equal(false)
expect(no_client.blocker).to_equal("missing authenticated Steam client")
expect(no_client.required_symbol_count).to_equal(20)
expect(no_client.required_os_capability_count).to_equal(11)

val partial_symbols = steam_api_probe_backend(true, ["SteamAPI_Init"], steam_api_backend_required_os_capabilities())
expect(partial_symbols.ready).to_equal(false)
expect(partial_symbols.blocker).to_equal("missing Steamworks SFFI symbols")
expect(partial_symbols.matched_symbol_count).to_equal(1)

val partial_os = steam_api_probe_backend(true, steam_api_backend_required_symbols(), ["elf64_dynamic_loader"])
expect(partial_os.ready).to_equal(false)
expect(partial_os.blocker).to_equal("missing SimpleOS Linux/Steam Runtime capabilities")
expect(partial_os.matched_os_capability_count).to_equal(1)

val ready = steam_api_probe_backend(true, steam_api_backend_required_symbols(), steam_api_backend_required_os_capabilities())
expect(ready.ready).to_equal(true)
expect(ready.blocker).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/game/steam_support_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Steam API facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
