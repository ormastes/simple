# SimpleOS Steam-Compatible SDK Slice

<!-- codex-architecture -->

This slice is deliberately pure Simple. It does not embed Valve Steamworks
headers, a Steam client, Wine, Proton, or copied C/C++ bindings.

The rebuild-porting path follows MDSOC+ layering. The common game-port contract
lives at `src/os/game/common/port_contract.spl` and owns the stable source
rebuild profile, package manifest fields, required capability list, and guest
marker format. Steam support in `src/os/game/steam/` consumes that common node
through a facade; it does not own the general "port a SteamOS source game by
rebuild" policy. The 2048 proof is only a leaf consumer.

Layer list:

- `src/os/game/common/` — public game-port contracts and shared manifest format.
- `src/os/game/steam/` — Steam facade and SFFI backend projection.
- `examples/os/game/` — rebuildable game proofs and bridge fixtures.
- `scripts/os/make_os_disk.shs` plus `examples/simple_os/.../toolchain_vfs_probe_entry.spl` — guest packaging and spawn evidence.

Tree-level encapsulation:

- `common` is public to the next layer through `GamePortProfile`,
  `GamePortReadiness`, `game_port_manifest`, `game_port_marker`, and
  `game_port_probe`.
- `steam` is sibling-private for Steam-specific API state, backend probing, and
  SFFI health gates.
- example games may depend on `common` and `steam` facades, but may not define
  platform readiness policy themselves.

Common relative tree-node paths:

- `src/os/game/common/port_contract.spl` is the extracted common node for
  source rebuild profiles, required/optional capability names, manifest
  emission, and guest marker emission.
- `src/os/game/steam/support_api.spl` remains the Steam facade node.
- `src/os/game/steam/sffi_backend.spl` remains the optional native backend node.

Public surface matrix:

| Raw layer | common game-port node | Steam facade node | Guest packaging node |
| --- | --- | --- | --- |
| `common` | public to parent as profile/readiness/manifest/marker | public to next-layer sibling through data-only profile | public to next-layer sibling through marker text |
| `steam` | consumes profile and marker facade | public to examples as pure Steam API facade | emits Steam and game-port markers |
| `examples` | consumes only public common/Steam functions | no private Steam state access | produces host-visible proof output |
| `guest packaging` | consumes marker/manifest strings | no Steam backend internals | exposes `/SYS/ST204PRT.TXT`, `/SYS/MARKERS.TXT`, and `/sys/apps/steam_2048` |

This MDSOC+ split makes the original target explicit: source games from
SteamOS-like Linux stacks should rebuild against the SimpleOS game-port profile
and the Simple Steam facade. Real Steam client connectivity remains a separate
backend capability, not a prerequisite for proving the rebuild environment.

The implemented boundary is a Simple-owned facade in
`src/os/game/steam/support_api.spl`. Games call the facade through Simple data
types, and a future SFFI bridge can map those calls to a real Steamworks host
library when SimpleOS has a Linux ABI, dynamic loader, networking, file, and
process substrate capable of hosting it.

The facade now exposes a tested catalog for the current documented Steamworks
API interface families: Apps, AppTicket, Client, Controller, Friends,
GameCoordinator, GameServer, GameServerStats, HTMLSurface, HTTP, Input,
Inventory, Matchmaking, MatchmakingServers, Music, Networking,
NetworkingMessages, NetworkingSockets, NetworkingUtils, Parties, RemotePlay,
RemoteStorage, Screenshots, Timeline, UGC, User, UserStats, Utils, Video,
SteamEncryptedAppTicket, steam_api, and steam_gameserver. The pure Simple
implementation records deterministic state for auth tickets, install
directories, overlay dialogs, input actions, screenshots, UGC publication,
microtransaction authorization, persona state, P2P packets, achievements, stats,
cloud, lobbies, networking, and DRM ticket requests.

The first runnable proof target is a deterministic 2048 smoke program based on
the open-source MIT-licensed `gabrielecirulli/2048` project. The smoke program
validates local game logic, source rebuild metadata, achievement/stat/cloud/
lobby/DRM-ticket state, and serial markers that can be checked after a SimpleOS
guest boot.

The real-backend gate is executable rather than aspirational. `SteamBackendProbe`
requires an authenticated Steam client, twenty SFFI-visible Steamworks entry
points, and eleven SimpleOS host capabilities before `ready` can become true.
The required host capabilities are ELF64 dynamic loading, `dlopen` shared
objects, Linux/glibc ABI compatibility, pthread/futex threads, BSD
sockets/TLS/DNS, POSIX filesystem locks, Steam client IPC, callback pumping,
secure ticket crypto, a Steam Runtime container, and a Proton/Wine host.

The compiled-mode dynamic bridge contract lives in
`src/os/game/steam/sffi_backend.spl`. It follows the repo's optional native
library pattern: Simple code discovers `SIMPLE_STEAM_BRIDGE_PATH` first, then
known local bridge/Steamworks redistributable paths, loads the candidate with
`spl_dlopen`, checks every required `SteamAPI_*`/`SteamGameServer_*` symbol with
`spl_dlsym`, and feeds that evidence into the same backend gate used by the pure
facade. A real bridge must also export `simple_steam_bridge_is_mock` and
`simple_steam_bridge_real_backend_ready`; Simple refuses readiness when the
bridge identifies itself as a mock or cannot prove its Valve-backed runtime is
loaded. Interpreter tests use `steam_sffi_probe_from_evidence`; actual bridge
execution requires compiled Simple mode because `spl_dlopen` is not available in
the interpreter.

`examples/os/game/steam_bridge_mock/simple_steam_bridge_mock.c` is a deliberately
small local fixture for that compiled-mode path. It exports the required symbol
names so `examples/os/game/steam_sffi_probe_demo.spl` can prove the loader and
symbol probe work against a real shared object. The fixture is labeled
`mock_bridge=true real_steam_backend=false`; it must not be treated as a Steam
client, Valve SDK substitute, DRM backend, or network service.

`examples/os/game/steam_bridge_real/simple_steam_bridge_real.c` is the non-mock
bridge skeleton. It loads a user-provided Steamworks redistributable from
`SIMPLE_STEAMWORKS_LIB_PATH`, verifies the required symbols, and reports
`simple_steam_bridge_real_backend_ready` only when that library is present. It
still depends on a real Steam client/session around the process; the repository
does not vendor Valve binaries or credentials.

Current limitation: this is not real Valve Steamworks compatibility yet. Passing
tests prove the pure Simple facade and payload contract, not a Steam client login,
real upstream Steamworks SDK bridge, Steam backend authorization, or Steam
Runtime/Proton execution.
