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

Sources and code map:
[domain research](../01_research/domain/native_macos_simple_container_2026-09-27.md),
[local research](../01_research/local/native_macos_simple_container_2026-09-27.md).
