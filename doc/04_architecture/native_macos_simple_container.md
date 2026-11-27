<!-- codex-design -->
# Native Simple Container on macOS and SimpleOS

The shared control layer freezes the host OS, execution OS, isolation class,
attempt identity, workload digest, policy, deadline, and output cap. It uses
`ContainerHostCapabilityV1` for exact admission and `RuntimeOperationV1` for
create/start/wait/stop/destroy observations. Mutable handles stay in sibling
providers; a copied receipt never authorizes a launch.

| Execution host | Provider owner | Isolation and exit authority |
|---|---|---|
| macOS | `MacOsNativeSandboxProviderV1` (to implement) | Signed App Sandbox helper, pinned native executable, owned process lease, observed exit and reaping. |
| SimpleOS | `SimpleOsContainerProviderV1` (separate lane) | ContainerWorld policy, authenticated loader, scheduler task and kernel exit. |

Both rows describe target authority; this change supplies only Mac admission,
worker protocol, and bundle generation. Hosted process
observation V3/V4 currently reports unavailable on macOS; an independent
sandboxed launch and native process owner must be built and qualified before
this row can publish lifecycle receipts.

The Mac-specific Simple leaf currently supplies bounded executable format
preflight and a fail-closed request gate. Its result preserves the shared
identity and prepared state and contains no executable command, PID, or exit
claim. This is an admission component; it does not own a sandboxed process.
It also supplies a bounded HMAC worker command protocol in
`src/lib/nogc_async_mut/container/providers/macos/worker_protocol_v1.spl`.
The protocol binds a provisioned key and nonce to one attempt and consumes
each sequence once. Key possession is not proof of a signed or sandboxed peer.
An independently launched service must own secure key provision, peer
validation, native process handles, and cleanup before it can use these
commands to publish lifecycle receipts.

`src/app/macos_xpc_bundle/` now packages caller-supplied Mac Mach-O app and
XPC service entrypoints into a `SimpleHost.app` bundle with an embedded
`SimpleWorker.xpc`, signs the service before the app, and verifies both. The
service receives its own App Sandbox entitlement; the host app does not inherit
that sandbox. The supplied app must connect to the service, and the supplied
service must call `xpc_main`. Bundle generation does not launch either process
or establish isolation, exit, or descendant cleanup evidence. This remains a
native macOS process architecture with no VM.

Implementation language: provider policy, identity checks, lifecycle state,
request/receipt handling, and helper logic must be written in Simple `.spl`.
The Mac leaf reuses the common value contracts and the SimpleOS provider's
owner-and-observation pattern, while retaining macOS process handles locally.
The Windows HCS leaf follows the same contract with its own native handles.
Shared code may validate copied values; neither hosted leaf imports the
SimpleOS scheduler/kernel or another host's private implementation. If a
required macOS authority has no callable Simple surface, leave launch
unavailable and record that exact boundary instead of adding a C control path.

The Mac provider must verify code signature and entitlements before start,
and check the running helper's sandbox state in the live fixture. It must not
substitute QEMU, Docker, Apple `container`, or an unsandboxed process. A single
signed helper identity may share its app data container across attempts; until
per-attempt isolation is proven, serialize this route and restrict it to one
trusted owner. The provider must reject incompatible Mach-O architecture and
unsupported filesystem, network, or resource policy before launch.

SimpleOS keeps its own scheduler and namespace authority. It never imports a
macOS process handle. Both leaves return immutable common observations with
exact attempt/generation/boot/native identity; the controller commits only a
matching result. No VM path is a Simple Container backend.

Darwin substrate for the separate custom-Seatbelt lane
(`doc/05_design/simple_container_macos_seatbelt.md` §2.3, §9.1, §15.2; source
only, NOT qualified on a Mac):

- `local_ipc_v1` now has a Darwin implementation beneath the same owned
  token/generation/close receipts (`src/runtime/runtime_local_unix_v1.h`).
  Origin is the PID only (no PID namespace); paths are re-walked and compared
  after connect/bind instead of `/proc/self/fd` anchoring; descriptor flags and
  `SO_NOSIGPIPE` are applied right after creation/accept/receipt; peer identity
  is `getpeereid` cross-checked against the `LOCAL_PEERTOKEN` audit token and
  `LOCAL_PEERPID`. `local_unix_peer_identity_class_v1()` reports this as
  `DarwinKernelObservedPeer`, weaker than Linux connect-time `SO_PEERCRED` and
  never an incarnation credential. The process-pipe stdout handoff stays
  Linux-only (unsupported on Darwin).
- SOSIX owns the Seatbelt activation leaf
  (`std.nogc_async_mut.sosix.darwin_sandbox_v1`, native call pair in
  `src/runtime/runtime_sosix_darwin_sandbox_v1.h`): `sandbox_init(profile, 0,
  &err)` + `sandbox_free_error`, a preallocated receipt, Simple-side profile
  admission and error sanitization, no unrestricted fallback, and
  `Unsupported` on every non-Darwin host without entering native code.
- Mac-qualified 2026-11-14 (macOS 26.5, arm64; build recipe from
  `doc/06_spec/01_unit/lib/io/local_ipc_v1_native_evidence.sdn` plus Darwin
  `-Wl,-dead_strip -Wl,-undefined,dynamic_lookup`):
  `local_unix_v1_selfcheck.c` prints `PASS Darwin local Unix
  bytes/peer(getpeereid+audit token)/path/ancillary/shutdown/close/listener
  contract; separate-UID accept NOT_RUN`. The disposable-child probe
  `src/runtime/test/sosix_darwin_sandbox_v1_selfcheck.c <profile> <root> <key>`,
  fed the exact text `seatbelt_profile_compile_v1(seatbelt_attempt_policy_v1(...,
  "endpoint-v1"))` emits, passes 12/12: unconfined control reads host-scope;
  after activation workspace read and output create are allowed, workspace
  write, private/host-scope/sibling-attempt/`/private/etc` reads, loopback inet
  connect and `fork` are denied, and only the attempt broker socket connects.
  The probe now reports every `seatbelt_qualification_plan_v1` canary as
  `canary <id> allow|deny` after an unconfined reachability control; on this
  Mac all 23 match (incl. symlink/case-alias to protected roots, home sentinel,
  IPv6/UDP/DNS/listen, other unix socket, mach-lookup, fork/posix_spawn/execve,
  refused-profile reporting; `child-inherits-confinement` comes from a real
  grandchild under the same profile plus `(allow process-fork)` only, and DNS
  and mach-lookup have unconfined controls). `seatbelt_manifest_from_probe_v1` decodes that
  transcript into a manifest that `seatbelt_capability_status_v1` reports
  `qualified` for the observed build (checked under `bin/simple test`; the
  seed `run` mode diverges, see
  `doc/08_tracking/bug/seed_run_mode_or_compare_diverges_from_test_2026-11-14.md`).
  Launch step 7 is therefore `qualified-darwin-native`; steps 2-6, 8-10 and
  fresh-worker admission stay unsupported, so the adapter still blocks with
  `darwin-worker-admission-unwired`. BSD: the probe is Darwin-only (exit 77
  elsewhere); no FreeBSD path changes.

Sources and code map:
[domain research](../01_research/domain/native_macos_simple_container_2026-09-27.md),
[local research](../01_research/local/native_macos_simple_container_2026-09-27.md).

## Endpoint network core (`endpoint-v1`, pure layer)

The emulated private network of the Seatbelt design
(`doc/05_design/simple_container_macos_seatbelt.md` 11, 12.2) has a pure
Simple decision core with no sockets and no host I/O:
`src/lib/common/contracts/container/endpoint_frame_v1.spl` (bounded binary
`endpoint-frame-v1` codec) and `src/lib/nogc_async_mut/container/network/`
(identities, bounded logical IPAM, network-scoped service registry,
default-deny `authorize_route`, policy revisions/revocation, per-session frame
flow control, external-address policy). `endpoint-v1` is an application-visible
endpoint fabric, not a kernel network namespace: logical addresses are never
assigned to a process stack, and routes are keyed by network + endpoint
identity + port + protocol + generation. `pod-ip-v1` is always rejected.
The broker transport (open/connect/accept/poll/close) is unqualified and fails
closed, so `endpoint-v1` admission stays blocked until a real macOS data plane
records native evidence.
## Separate direct-Seatbelt lane (2026-11-13)

A second, independent macOS lane exists beside the signed-App-Sandbox route:
backend `macos-seatbelt-process`, engine `macos-seatbelt-process-v1`
(design: [simple_container_macos_seatbelt](../05_design/simple_container_macos_seatbelt.md)).
It never aliases `docker`, `podman` or `macos-native-sandbox-v1`, and the
signed-helper provider above is unchanged. Implemented as pure Simple under
`src/lib/nogc_async_mut/container/providers/macos/`:

- `seatbelt_profile_v1.spl` — deterministic SBPL emitter: fixed baseline
  revision, `(deny default)`, separate read-data / read-metadata / write /
  execute rules, strict literal escaping and byte limits, no user SBPL/regex/
  import, direct network denied, one granted broker unix socket, digest.
- `seatbelt_capabilities_v1.spl` — canary plan + qualification manifest; reports
  `unqualified` until a Darwin probe records every canary for the exact OS
  build, architecture, helper digest, runtime ABI and baseline revision.
- `seatbelt_provider_v1.spl` — `MacOsSeatbeltAdapterV1` (facade function set),
  §8.1 lifecycle mapping, §10.2 attempt directory plan and §8.2 launch steps.
  Every native effect fails closed (`blocked`, `SCMAC-*` reason, lifecycle not
  advanced) until the SOSIX Darwin sandbox owner exists and qualification
  passes. Not yet wired into `SimpleContainerOwnerV2`.

Nothing in this lane has been run on macOS; no enforcement is claimed.
