# ARM64 direct sockets bypass exact endpoint authority

Status: open source finding, inspected on `feature/simpleos-live-positioned-owner-20260927` at `2d453ab592b` on 2026-09-27. No ARM64 guest execution or exploit claim is made.

## Reproduction from current source

1. `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c` routes syscalls 70–76 through `arm64_dispatch_net_shim`. When the VirtIO network path is ready, it calls the `spl_arm64_net_*_direct` export after only `spl_shim_net_capability_check`.
2. `src/os/kernel/abi/syscall_shim_net.spl` checks `NetConnect(0)` for socket creation and outbound I/O, or `NetListen(0)` for bind/listen/accept. Its exact portable checked owner is called by x86_64 strong shims, but the ARM64 ready direct path bypasses those strong shims.
3. `src/os/services/netstack/netstack_init.spl` copies `sockaddr_in` in `spl_arm64_net_bind_direct` and calls `net_tcp_bind` without checking `NetBindIpv4(address, port)` or the copied port's `NetListen` grant. `Arm64NetFdMap` records task ID and internal/external fd only, so listen, accept, send and receive cannot recover the bound port or accepted-listener provenance for exact checks.
4. `src/os/kernel/loader/arm64_fs_exec_spawn.spl` publishes wildcard `NetConnect(0)` and `NetListen(0)` for every payload, without `NetSocketCreate`. The existing `arm64_fs_exec_launch_capability_spec.spl` asserts that a generic payload lacks `NetListen(0)` and has three tokens; those assertions conflict with this source and require reconciliation before claiming a passing test.

## Required fix and evidence

- Socket creation must require `NetSocketCreate`, distinct from outbound connection authority. The ARM64 launch policy must grant it only to the payloads that need sockets.
- Bind must authorize the exact copied IPv4 address and port in the same transition that calls the direct backend. Reject a wrong address, wrong port, changed user memory, and missing capability before creating or committing an internal fd.
- The direct fd owner must retain bound-listener and accepted-child provenance under the authenticated task identity. Listen, accept and accepted I/O require the exact listener port; outbound I/O requires its own connect authority. Close and task exit must retire that provenance before descriptor reuse.
- Keep the ARM64 ready transport and its fallback under one authoritative decision contract. A broad C precheck alone cannot prove the direct effect's endpoint authorization.
- Update the contradictory source specs, then execute success and denial cases in a ring-3 ARM64 guest on an admitted pure-Simple build. Include port/address mismatch, forged fd, cross-task fd, stale close/reuse, changed input bytes, and teardown during pending I/O. Capture the selected direct/fallback route and actual network effect.

Release impact: ARM64 network parity and the SimpleOS release row remain unqualified until this evidence exists. The x86_64 candidate in PR #1691 does not qualify the ARM64 direct path.
