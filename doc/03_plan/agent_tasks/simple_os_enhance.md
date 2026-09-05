<!-- codex-design -->

# SimpleOS Enhancement — Parallel Development Plan

## Frozen Phase 0 contract

Lane A owns the only edits to `TaskControlBlock`. All lanes consume these
interfaces after its reviewed landing:

```text
KernelCallContext(task_id, principal_id, job_id, cspace_id,
                  isolation_domain_id, resource_domain_id, audit_context_id)
WorkloadManifest(identity, image, authority, isolation, resources,
                 lifecycle, observability)
CompiledExecutionPolicy(spawn_spec, syscall_filter, isolation_spec,
                        resource_spec, identity_lease, audit_policy)
```

All temporary cross-lane helpers fail with
`fail("simple_os_enhance helper is not implemented")` until their owner lands.

| Lane | Owner / sidecar | Scope | Depends on | Acceptance evidence |
| --- | --- | --- | --- | --- |
| A — Process/CSpace | `/root`; process/CSpace discovery sidecar | caller context, TCB identities, live CSpace spawn/exec/fork, root mint seal | Phase 0 interfaces | focused authority-path and CSpace specs |
| B — PID1/services | PID1/service discovery sidecar | boot handoff, manifest loading, dependency/readiness, supervision, restart | A | QEMU VFS→network→HTTP restart scenario |
| C — Namespace/VFS/IPC | `/root` after A | domain binding, caller-aware VFS, PID/endpoint view | A, B endpoint contract | cross-domain denial system scenarios |
| D — Resources/network/device | N/A until C domain semantics land | hierarchical accounting, egress and device brokers | A, C | limit/throttle and driver-restart scenarios |
| E — Container runtime | isolation/container discovery sidecar | OCI ingest/storage, live monitor/lifecycle, rootless mapping | B, C, D | QEMU create/start/exit/reap scenario |
| F — Human/agent policy | isolation/container discovery sidecar | principals, policy compiler, model/secret/tool/approval brokers | A, C, D | agent/subagent attenuation and approval scenarios |
| G — Evidence/formal | N/A until executable owners exist | SSpec manuals, QEMU fault injection, fuzzing, Lean and host rows | A–F | independent evidence matrix; blocked host rows retained |

## Execution order

```text
Phase 0 contracts → Lane A
                  → Lane B ─┬→ Lane C → Lane D
                            └→ Lane F
                                      ↓
                                  Lane E → Lane G
```

## Working agreements

- Lane owners do not edit another lane's owned files. Cross-lane changes first
  become an interface request in this plan.
- Manual flow vocabulary is fixed: `Start capability-confined PID1`, `Start
  dependent workloads`, `Crash and revoke stale grants`, `Verify cross-domain
  denial`, and `Reap the workload tree`.
- Common setup/checker names are `setup_kernel_call_context`,
  `setup_workload_manifest`, `check_authority_trace`,
  `check_fresh_restart_grants`, and `check_isolation_denial`.
- Merge owner and final normal/highest-capability reviewer: `/root`.
- Generated-manual quality reviewer: `/root`; a lane cannot mark its scenarios
  done until its mirrored Markdown manual is understandable without source.

## Current implementation start

Start Lane A with a narrow Phase 0 slice: locate the live filesystem-exec
caller-ID boundary, introduce the kernel-owned caller-context value adjacent to
existing security ownership, and prove that the gate receives the live TCB
capability set. Do not make a permissive compatibility fallback.

### Current evidence and merge boundary

The initial context value and context-capability gate are implemented in
`src/os/kernel/security/execution_context.spl` and
`src/os/kernel/loader/cap_exec_gate.spl`. The focused gate tests prove a
non-root caller succeeds only when its carried pouch has both FileExec and
ProcessSpawn. The live ABI dispatcher and filesystem-exec bridge still use
scalar/current-caller plumbing and are concurrently edited by another lane;
Lane A must consume the frozen contract there rather than duplicate that work.

The shared exec handler is now a first consuming path: it creates the context
from the live scheduled TCB and rejects a missing FileExec/ProcessSpawn pouch
before image work. Remaining ABI/syscall spawn and fork paths still require the
dispatcher-owner integration.

## Mission-critical evidence status

The focused host evidence currently covers context-gate denial and the live
scheduler fork attenuation boundary. It does **not** establish a mission-
critical release claim. The release aggregate run on 2026-08-11 found nine
stale evidence reports and supplied no `STATUS: PASS` record. Lane G must
refresh the named reports, then collect self-hosted, QEMU, and formal evidence
for the authority invariants before this plan can be promoted beyond host
diagnostics.

## Current parallel execution update — 2026-08-11

| Lane | Landed boundary | Next non-overlapping work |
| --- | --- | --- |
| A | live caller context, pledged child CSpace, root-mint seal | replace scalar IPC/network permission probes with endpoint handles |
| B | x86_64/RV64 filesystem-backed PID1 target ELFs, opaque catalogue spawn, RV64 IDs 1/61/136 delegation | real VFS/net/HTTP target payload ABI plus exit/readiness events |
| C | caller-aware filesystem-exec path | bind every VFS/FD path and endpoint lookup to the isolation domain |
| D | per-child process/memory syscall binding | storage/device and egress brokers needed by VFS/net services |
| E/F | model/runtime seams remain separate | do not attach containers or agents until the service/endpoint authority path is live |
| G | host unit checks and static target ELF | RV64 QEMU PID1 lifecycle after child-resume and real payloads exist |

The pure-Simple bake is now fail-closed for a selected PID1: it stages the
exact `/system/services/{vfs,net,http}.smf` files or stops. The C image baker
and RV64 QEMU scenario remain separate work; neither should be represented as
service-lifecycle evidence until they consume the same immutable catalogue
images.

### Critical follow-up — 2026-08-11

The kernel `MapBar` ABI is now an exact `(BDF, BAR index, optional user-VA
hint)` operation. The dispatcher checks the matching `DeviceBarMap` capability
and the kernel resolves PCI memory-BAR address/size; raw caller-provided
physical ranges are no longer accepted. This is a Lane-D prerequisite, not a
claim that VFS or net payloads own real brokered devices yet.

The driver-supervisor lane now has a bounded `ManagedDeviceGrantBroker` policy
ledger that emits only `DeviceGrant`, `DeviceBarMap`, `DeviceDma`, and
`IommuDomain` kinds, rejects duplicate BDF assignment, and generation-revokes
stale grants before reassignment. It must still be connected to the trusted
SpawnSpec/CSpace mint path before it counts as live enforcement.

RV64 target evidence is currently blocked during full source discovery by a
concurrent untracked file, `src/os/sosix/fs/ipc_codec_v1.spl:79`, whose local
identifier `out` is parsed as a reserved grammar construct. Preserve that
owner's change; repair/rebuild after it lands. No QEMU service-lifecycle claim
is permitted while this blocker remains.

## Authenticated catalogue gate (not yet authorized for implementation)

The required trust path is now concrete but cannot safely be fabricated. The
loader must use `os.crypto.ed25519.ed25519_verify` over a domain-separated,
fixed-order record binding target architecture and the exact bytes of the
VFS/net/HTTP catalogue payloads. Bake can use the host-only
`ed25519_sign_pkcs8` implementation to generate and self-check the detached
signature before staging it. This requires a release-owned public key compiled
into the kernel and a separate CI/HSM PKCS#8 signing-key path. No such root key
has been supplied by the repository; do not substitute an RFC fixture, an SSH
key, a self-derived hash, or an attacker-readable private key. Until a release
owner supplies that trust anchor, catalogue bytes remain unauthenticated and
this plan must not claim image verification.

## Payload implementation boundary — 2026-08-11

The net lane now has `net_service_main.spl`: it obtains only the child CSpace's
single broker-assigned `DeviceGrant`, initializes VirtIO-net, then starts the
existing owned-record `NetstackService` on endpoint `net`. It is suitable for
the catalogue's `net.smf` build once all companion payloads and catalogue
authentication exist. The next non-overlapping payload work remains: (1) a
storage broker/lease-backed VFS mount entry and (2) an HTTP service using the
native net IPC socket protocol. Do not stage endpoint-only stand-ins for either
slot, since production bake correctly fails closed when PID1 is selected.

### Transport and VFS gates — 2026-08-11

The owned-copy IPC ABI now carries an explicit reply kind: request receive
mints one permit; reply send consumes it; reply receive mints none. VFS and
net response helpers use the reply API. HTTP may consume this only after a
native socket-client state machine and `NetListen` broker enforcement exist.

VFS cannot be truthfully emitted as a target payload until the native compiler
lowers `Filesystem` trait slots/vtables correctly. The known failure is
`DUCK_DISPATCH_UNSUPPORTED_SLOT` in the `VfsManager.mounts[].fs` execution
path. Ownership of that repair belongs to the native compiler/lowering lane;
the service lane must prove task-local NVMe-to-VFS dispatch after it lands.

The kernel now decodes and gates native `NET_BIND` at the owned IPC boundary:
only an exact `NetListen(port)` holder may queue the bind to `net`. This is a
port-authority control, not yet a complete per-client socket-ownership model;
that state must be added before untrusted multi-client HTTP use is accepted.

The netstack now also stores the creator endpoint in each socket descriptor.
Every descriptor operation in the native IPC handler denies a different source
endpoint, and accepted connections inherit the listener owner. This supplies
the client-isolation prerequisite for a future HTTP payload.

The HTTP payload now exists in `src/os/services/web/http_service_main.spl` as
a bounded owned-IPC state machine for socket, bind:80, listen, accept, receive,
HTTP response, and close. It has no hosted-server dependency and consumes only
the catalogue's `http` endpoint, `IpcConnect("net")`, and `NetListen(80)`
authority. It must still be target-built and staged with authenticated VFS/net
images before PID1/QEMU acceptance can be attempted.

The VFS payload now exists in `src/os/services/vfs/vfs_service_main.spl`. It
owns its broker-assigned NVMe grant and a concrete in-closure FAT32
`Filesystem` adapter, then mounts and starts `VfsService` without the kernel
boot VFS global. This replaces the former source-level no-vtable blocker. The
unrelated full-tree native parser failure still prevents target artifact and
QEMU proof, so the service chain remains unverified until that external repair
lands.

### Native `Filesystem` trait dispatch repair — 2026-08-11

The native lowerer now preserves an HIR local's declared `type_name_hint` for
the duration of a function. Direct trait calls through an otherwise erased
local receiver supply that declared trait to method resolution, which selects
the registered trait vtable slot before any name-based fallback. The focused
MIR regression puts `Filesystem.read` and `ByteSource.read` in competition and
asserts that an erased `Filesystem` receiver selects slot 2 rather than the
`DUCK_DISPATCH_UNSUPPORTED_SLOT` sentinel. Formatting and diff checks are
clean. The focused Rust test cannot begin because the independently dirty
runtime export layer lacks `rt_expect_or_trap`, `rt_value_as_u64`, and
`rt_value_u64`; repair that coherent runtime change before retrying, then run
the target VFS payload test and QEMU chain.

### Native build recheck — 2026-08-11

The former `ipc_codec_v1.spl` reserved-identifier parse blocker is no longer
present. A fresh `sh scripts/os/simpleos-native-build.shs` now reaches compiler
selection but fails before compilation: every candidate self-hosted compiler
segfaults during the environment-write capability probe, while the Rust seed is
correctly rejected as bootstrap-only. No target artifact was produced. Resume
with the same command after a non-segfaulting self-hosted compiler is deployed;
do not substitute the Rust seed for PID1 or service payload evidence.

### Owned IPC authority hardening — 2026-08-11

The stateful owned-IPC dispatcher is now the only permitted execution route
for `IPC_SEND_OWNED` and `IPC_RECV_OWNED`. The legacy result-only dispatcher
returns `-ENOSYS` for both operations instead of reporting success after
discarding mutated port and reply-permit state. The stateful path enforces
concrete `IpcConnect` rights for requests, a one-shot reply permit for replies,
and exact `NetListen(port)` authority for `NET_BIND` records directed to
`net`. Replay, missing endpoint authority, a port mismatch, and permit-table
capacity failure all deny before enqueue. The focused source check completed
without changed-source diagnostics; the interpreter runner still truncates
before its concise test summary, so this is not target/QEMU PASS evidence.

### PID1-only network ownership — 2026-08-11

`os_main` no longer calls `init_riscv_services_with_network()` before preparing
PID1. It calls the storage/display bootstrap-only `init_riscv_services()` path,
so the catalogued `net` workload is the first network initializer and PID1 can
apply its CSpace, supervision and audit policy before network authority is
usable. The focused boot source check completed without a changed-source
diagnostic. Target boot proof remains contingent on the recovered compiler.

### PID1 dependency-failure containment — 2026-08-11

The ring-3 service manager now distinguishes a transient provider restart from
a terminal quarantine. A transient VFS or net crash still leaves its dependent
service alive for the normal reconnect path. Once PID1 exhausts a provider's
restart budget (or cannot relaunch it), it stops every later catalogued
dependent in reverse order through the PID1-only root-service stop ABI and
marks those services quarantined too. Thus VFS terminal failure contains net
and HTTP; net terminal failure contains HTTP. The focused source check
completed without a changed-source diagnostic and the diff check is clean.
The pure selection policy is covered by
`test/01_unit/os/services/init/service_dependency_policy_spec.spl`; its
generated manual is complete with no documentation warnings.
This source contract requires the later QEMU kill/quarantine scenario before
it can be considered runtime evidence.

### Self-host bootstrap/runtime ABI handoff — 2026-08-11

The isolated `--full-bootstrap --full-cli` run reached the current Rust runtime
and failed before SimpleOS compilation because `value/mod.rs` exports three
absent ABI functions: `rt_expect_or_trap`, `rt_value_u64`, and
`rt_value_as_u64`. They are not dead exports. Native dynamic/bare
`Option`/`Result.expect(message)` has a runtime function specification for the
first; pure-Simple MIR U64 lowering emits the latter pair. Do not delete the
exports or their compiler consumers merely to make bootstrap compile.

The correct owner change is additive: restore the exact `expect` helper while
preserving the concurrent `WideInt` refactor; also restore a distinct unsigned
heap representation and its construction, unboxing, lifecycle, display,
kind/type, equality/hash/order and traversal behavior. `WideInt` cannot stand
in for U64 because values above `2^63-1` and signed/unsigned equality are
semantically distinct. Use a new heap tag rather than the existing tags. The
owner verification sequence is `cargo fmt`, `cargo check -p simple-runtime`,
u64-boundary tests, native unwrap/expect evidence, native symbol lookup, then
the self-host bootstrap. Only after that sequence may the PID1 QEMU lane retry.

### Agent MCP call-time authority — 2026-08-11

`OsMcpServer.dispatch_for_session` now requires a sealed `LlmSession` and
routes every call through `resolve_tool_call`. This is a call-time gate, not
only tool-list filtering: unknown and denied tool names share one response;
filesystem calls require canonical absolute paths and recheck the exact path
against the session's FileRead/FileWrite prefix capabilities. Paths containing
dot segments or doubled separators deny before a handler is reached. The
legacy `dispatch` API remains deliberately unauthenticated for compatibility;
it does not receive a synthetic full session. Focused tests cover deny-all,
SystemTime, scoped file access/traversal denial, UI endpoint and legacy
compatibility. Current MCP registry handlers and transport do not carry an
`LlmSession`, so no live request is falsely described as authenticated; the
next transport/registry change must bind a kernel-issued session identity to
this method.

### Live resource-controller execution update — 2026-08-11

Lane D now owns the following live enforcement slice, deliberately separate
from the still-blocked target payload proof:

1. Anonymous `mmap`, compatibility `sys_mmap`, and DMA allocation reserve a
   per-task mapped-page charge and require admission by every ancestor
   resource domain. Their explicit unmap/free paths release it; task exit
   clears abandoned charges.
2. Device BAR mappings are recorded as borrowed resources. Exact unmap drops
   PTEs without returning MMIO pages to PMM; partial BAR unmap and every DMA
   overlap through generic `munmap` fail closed. Generic `mprotect` also
   rejects BAR/DMA ranges, preserving their NX device mapping policy.
3. Device and compatibility VM helpers receive an immutable
   `KernelCallContext` constructed from the current TCB at dispatch rather
   than a scalar caller ID.
4. `ResourceBudget.cpu_weight` now binds once into the child fair-scheduler
   weight and is attenuated against a bound parent weight. This is an
   individual share ceiling; aggregate sibling quota is still pending.

Focused source checks and lint completed without changed-source diagnostics.
The bootstrap test runner truncates its compact summary for the focused
resource tests, so they remain host-executed but not PASS-qualified evidence.
Next Lane-D work is hierarchical CPU, I/O, and network accounting; it must not
be described as complete merely because page accounting is live.
