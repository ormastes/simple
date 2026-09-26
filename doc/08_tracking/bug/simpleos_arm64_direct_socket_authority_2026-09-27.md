# ARM64 direct sockets bypass exact endpoint authority

Status: candidate source repair on `feature/simpleos-arm64-net-authority-20260927`; ARM64 guest execution and release qualification remain open. The baseline finding was inspected on `feature/simpleos-live-positioned-owner-20260927` at `2d453ab592b` on 2026-09-27. No exploit claim is made.

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

## Candidate source repair and remaining gates

- The `arm64_fs_exec_spawn_ring3` launcher now calls the shared
  `fs_exec_launch_caps_with_launch_v1` policy with the actual `path`, `argv`,
  and `envp`. A generic payload receives
  socket creation and outbound authority but no listener grant; exact service
  pouches require the canonical launch tuple. The prior ARM64 wildcard-listen
  builder and its direct database-file grants are removed. No production
  caller of this launcher was found in the inspected tree; the authenticated
  launcher and raw resident bring-up remain separate release rows.
- The direct socket owner now checks `NetSocketCreate` before reservation,
  checks a single copied bind endpoint against `NetBindIpv4` and exact
  `NetListen` before `net_tcp_bind`, and records listener/accepted/outbound
  provenance per task-owned descriptor. Listen, accept, and accepted I/O check
  the recorded listener port; outbound connect and I/O check outbound authority.
  External descriptor numbers are not recycled within one boot, so a stale fd
  cannot name a later socket through simple close/reopen reuse.
- The C precheck now gates socket allocation and unknown/raw operations. Exact
  endpoint checks stay in the direct owner and the portable fallback owner,
  which both have the necessary copied endpoint or descriptor provenance.
- The ARM64 C syscall-33 path now separates its bounded file descriptor range
  from direct network descriptors starting at 100. It calls the direct owner
  only for network-range numbers and maps its non-owner sentinel to `EBADF`;
  task teardown remains a second retirement path. The earlier all-descriptor
  strong-shim close caused a kernel fault, so this narrower path still needs
  a ring-3 guest close/reopen and file-close regression before admission. The
  map retains its single-core transition assumption; multicore delivery needs
  serialization.
- The available repository release binary is an older Rust bootstrap seed. Its
  `check` command refused to provide source-matched validation, reporting a
  parser error in an unrelated `process_ops.spl`. No product test, ARM64 guest
  result, or release receipt is claimed for this candidate.
