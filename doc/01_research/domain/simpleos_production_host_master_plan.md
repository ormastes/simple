# SimpleOS Production Host-OS Master Plan (Domain Research)

Saved: 2026-07-27. Review basis: repository state + L4/seL4, OCI, POSIX.1-2024,
LLVM-libc, OpenSSH, PostgreSQL, SQLite, nginx, TUF, SLSA primary documentation.
Companion: `doc/01_research/local/simpleos_production_host_master_plan.md` (repo mapping),
`doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md` (execution plan).

## 1. Executive assessment

SimpleOS does not need another broad feature expansion or another parallel
implementation of IPC/VFS/loading/config/containers. It needs a **convergence
and enforcement program**. Substantial implementations or design seeds already
exist for: L4-like IPC + notifications, capabilities + spawn specs, per-process
FS-loaded ELF execution, SOSIX async APIs + POSIX facades, VFS/FAT32/NVMe,
service supervision, TTY/PTY/shell/SSH, native Simple execution, in-guest Clang
object emission, web/DB/browser/GUI/config, container and LLM-security models.

But several paths are still models, evidence contracts, adapters, or duplicates:

- `l4_fast_ipc.spl` is a benchmark/model, not integrated with real syscall/scheduler.
- Capability-aware spawning exists but live syscall enforcement and child CSpace
  injection are unwired; boot paths keep an ambient `spawn_full()` route.
- Containers are namespace metadata + prefix validation + readiness markers, not
  enforced kernel resource domains.
- Three overlapping filesystem stacks: old VFS, new FsDriver/mount-table, direct FAT32.
- Service capabilities are strings, not live capability objects in the child CSpace.
- `tty_write()` returns an accepted count without delivering to the output endpoint.
- POSIX module excludes writable shared `mmap()` and pthreads — both required by
  serious ports.
- In-guest Clang cc1 object emission proven (x86-64); in-guest link + execute open.
- Native raw HTTP benchmark fast, but full routed server is interpreter-bound;
  full Simple DB server unavailable.
- Browser has production-blocking isolation/network/origin/cookie/lifecycle/
  memory/conformance gaps.

**Production goal:** one small L4-style protection kernel, one typed capability
model, one process+loader pipeline, one async system API, one VFS, one driver
protocol, one service manifest, one configuration engine, generated
compatibility facades — then delete every bypass and duplicate.

## 2. Three release profiles, one kernel/ABI

| Product | Required | Optional |
|---|---|---|
| SimpleOS Server | kernel, storage, network, SOSIX/POSIX, SSH, init, logging, package/update, web+DB runtime | GUI, browser, IDE |
| SimpleOS Desktop | Server base + display/input/audio, compositor, desktop, settings, browser, accessibility | LLVM dev env |
| SimpleOS Developer | Desktop or Server base + Simple compiler, Clang/LLD, debugger, profiler, build tools, SDK | full source tree |

Browser blocks Desktop, not Server. Full LLVM blocks Developer, not a server
appliance. Separation reduces TCB, boot time, exposed services, update size,
and security review scope.

## 3. Target architecture

**L4 + exokernel is one architecture:** L4 semantics for protection/IPC/
scheduling/faults/capability transfer; exokernel principles for securely
exporting hardware to user-space drivers and library-OS components; MDSOC+
capsules for user-space service organization; SOSIX as the native async OS API;
POSIX personalities above SOSIX. seL4 MCS scheduling contexts + budget donation
to passive servers prevent client CPU-budget theft.

Stack (top→bottom): applications (Simple-native, POSIX, containerized, browser/
server/DB capsules) → compatibility runtimes (POSIX personality, optional Linux
personality, interpreter, AOT runtime, service stubs) → SOSIX (async process/
VFS/network/device/wait+cancel/capability APIs) → user-space services (initd,
serviced, procd, vfsd/paged, netd, devmgr/pcimgr/driver capsules, authd/secretd/
policyd, ttyd, logd/crashd/metricsd, timed, updated/pkgd, displayd/inputd/
audiod, containerd-simple) → K0 kernel (capabilities/object tables, endpoint/
reply/notification IPC, threads/processes/jobs/scheduling contexts, address
spaces/VMO/VMAR/pager, IRQ/timer/clock, IOMMU/DMA/DeviceGrant, fault+audit
endpoints) → hardware.

Kernel must NOT contain: filesystems, TCP/IP, SSH, config parsing, package
management, browser/DB logic, policy-heavy drivers.

**Kernel object model** (Zircon-style typed handles): Thread, Process, Job,
SchedulingContext, AddressSpace, VMO, VMAR, PagerEndpoint, Endpoint,
ReplyObject, Notification, WaitSet, Timer, IRQ, DeviceMemory, DmaBuffer,
IommuDomain, DeviceGrant, ResourceDomain, FaultEndpoint, AuditEndpoint.
Every handle resolves `object_id, generation, object_kind, rights, audit_label`.
Generation prevents stale-handle reuse; rights only attenuate on transfer
unless a privileged broker creates a new grant.

## 4. Shared ABI contracts (single owner, defined before parallel work)

| Contract | Owns |
|---|---|
| `src/os/abi/object_v1.spl` | object kinds, handles, generations, rights, status codes |
| `src/os/abi/ipc_v1.spl` | message header, call/reply, notifications, handle transfer |
| `src/os/abi/memory_v1.spl` | VMO, VMAR, mapping, pager contracts |
| `src/os/abi/spawn_v1.spl` | SpawnSpec, ArtifactManifest, auxv, process inheritance |
| `src/os/abi/container_v1.spl` | container namespaces, resource domains, image mounts |
| `src/os/abi/vfs_v1.spl` | vnode, open-file description, FD, mount namespace, async I/O |
| `src/os/abi/device_v1.spl` | device discovery, BAR, IRQ, DMA, IOMMU, reset |
| `src/os/abi/service_v1.spl` | service lifecycle, readiness, health, supervision |
| `src/os/abi/config_v1.spl` | typed config schema, validation, change transaction |
| `src/os/abi/security_v1.spl` | identities, policy subjects, profiles, approvals, audit |
| `src/os/abi/trace_v1.spl` | tracing, metrics, evidence receipt formats |
| `src/os/abi/version.spl` | ABI versioning, feature negotiation |

**Non-negotiable:** no subsystem may create a second IPC envelope, FD
abstraction, process manifest, config descriptor, or private capability syntax.
Generated code per contract: Simple sync client, async client, server dispatch
skeleton, C ABI binding, POSIX adapter, test fake, tracing wrapper, version check.

## 5. Kernel, IPC, scheduler, process, loader

**5.1 One production IPC path.** Named-port queue survives only as a compat
service. Kernel primitives: EndpointCall/Send/Receive, Reply,
NotificationSignal/Wait, WaitSetWait, typed handle transfer. Requirements:
bounded inline registers, out-of-line shared VMO for bulk, atomic handle
transfer, transfer-right checking, single-use reply objects, cancellation +
deadlines, scheduling-context donation, endpoint revocation, dead-server
detection, fault-safe copy/pin rules, arch-specific asm fastpath + validated
slowpath, sampled-only tracing on fastpath. CapTransfer must become a kernel
operation, not a convention struct.
Perf gates measured separately: same-core call/reply, cross-core, notification
latency, one-handle transfer, VMO grant, timeout/cancel, server chain depth,
donation, cache-hot/cold. A "fast IPC" claim requires real ring transition +
scheduler + rights validation + wakeup — not a language function benchmark.

**5.2 One global process manager/scheduler.** Replace per-exec bootstrap
scheduler. Model: Job → Process {AddressSpace, HandleTable/CSpace, Credentials,
ResourceDomain, Thread[], FDTable, MountNamespace, SignalState}. Lifecycle:
create job/process → restricted CSpace → address space → load → stack/argv/
envp/auxv → bind scheduling context → start → observe exit → collect → reap.
Add: parent/child, process groups/sessions, wait/reap, job control, signals +
fault conversion, rlimits, affinity, priority, suspend/resume, crash reason +
minidump, OOM victim selection, clean I/O cancellation.

**5.3 Unified FS execution.** One pipeline: path/cap-relative name → VFS open
with EXECUTE right → immutable executable handle → verify metadata/signature/
hash → identify ELF/SMF/script → create process + CSpace → map segments/module
graph → resolve allowed libraries → W^X relocation transition → argv/envp/auxv
→ enter userspace. Descriptor-based execution (POSIX `fexecve()` model)
prevents TOCTOU path replacement.
One `SimpleArtifactManifest` for ELF/SMF/script/native: format_version,
artifact_kind, target_os/arch/abi, entrypoint, required_abi_features/services/
capabilities, resource_limits, namespace_template, native+smf libraries,
interpreter, argument_schema, startup_preloads, content_hashes, signature,
debug_identity. Existing launch-metadata work is the correct base.

**5.4 Remove ambient spawn authority.** `spawn_full()` legal only for the root
task during bootstrap. Everything else uses SpawnSpec (requested caps,
executable handle, argv/envp, inherited handles, FD actions, scheduling,
resource-domain, mount + container namespace, identity, security profile).
`effective_rights = parent_delegable ∩ executable_policy_ceiling ∩
system_policy_ceiling ∩ manifest_request − explicit_denials`. No amplification
via child creation, handle dup, IPC transfer, dynamic loading, or container entry.

## 6. Native L4 capability containers

Container = Job + ResourceDomain + CSpaceTemplate + MountNamespace +
ProcessView + NetworkNamespace + IpcNamespace + IdentityMap + HostnameDomain +
optional TimeDomain + SecurityPolicy + ImageSnapshot. Enforced at every lookup:
kernel handle, IPC endpoint resolution, VFS traversal, mounts, process
enumeration/signal, network bind/connect/listen, shm attach, device grants,
debug/trace, credential/secret access. Replace (not extend) the eight-slot
namespace registry and marker-oriented contract.
**Rootless by construction:** the container never receives a global root
namespace; it starts with only its namespace handles, root dir handle, selected
service endpoints, scoped network endpoint, resource-domain handle, allowed
device grants, and explicitly inherited files/sockets.
**OCI at the edge:** importer/exporter adapter (OCI bundle → validate/normalize
→ ContainerSpec → SpawnSpec tree). Safety checks: reject `..` traversal,
escaping symlinks/hardlinks, uncontrolled device nodes; normalize UID/GID maps;
bound unpack size/count; verify digests+signatures; no lifecycle hooks unless
authorized; isolated network setup; no raw host mounts by default.
**Storage:** immutable content-addressed layers, RO base, COW writable
snapshot, per-container quota, explicit volumes, atomic snapshot/rollback,
signed metadata, ref-tracked GC. DBFS/custom overlay stays out of the security
boundary until power-fail recovery + namespace escape tests pass.

## 7. Driver architecture

Kernel keeps only: interrupt-controller setup, timer, early serial, initial MM,
IOMMU programming primitive, DMA pin/map/unmap, PCI/ACPI/DT discovery
primitives, emergency boot block path, device reset/revocation support.
User driver capsule ABI: probe/bind/start/quiesce/stop/reset/suspend/resume/
hotplug/health/stats. DeviceGrant carries independently revocable rights: BAR
ranges, I/O ports, IRQ wait/ack, MSI/MSI-X, DMA alloc, IOMMU mapping, reset,
power transitions, child-function discovery.
**Mandatory crash ordering:** stop scheduling → mask IRQs → revoke new DMA →
remove IOMMU mappings → quiesce/reset device → revoke MMIO+IRQ handles → fail
outstanding client requests → restart per policy → restore endpoint → replay
safe config only. Prevents dead/compromised driver DMA into unrelated memory.
Class priority: (1) timer/intc/serial, (2) NVMe + VirtIO block, (3) VirtIO net
+ one physical NIC family, (4) PCI + IOMMU, (5) USB host + HID, (6) fb/VirtIO
GPU, (7) audio, (8) power, (9) more storage/net, (10) vendor GPU. Each driver:
protocol conformance suite, fake-device units, QEMU integration, fault
injection, suspend/resume, hot-unplug, reset/recovery, real-hardware evidence.

## 8. One VFS and filesystem stack

Adopt only: SOSIX async VFS API → VFS service → mount namespace → FsDriver →
block/network/pseudo FS. Delete or shim: old Filesystem/VfsManager API, direct
FAT32 calls from apps/services, independent global mount structures,
per-filesystem FD interpretations, "use first mount" routing.
Objects: MountNamespace, Mount, Vnode, OpenFileDescription, FileDescriptor,
DirectoryCursor, FileLock, Watch, PageCacheEntry, WritebackRequest. FD is
process-local; open-file description is shareable (offset, flags, refcount, fs
instance, vnode, locks, async completion state).
Semantics required: cap-relative openat lookup, symlink depth limits, mount
crossing, rename atomicity, unlink-open-file, file/record locks, mmap shared+
private, msync/fsync/fdatasync, sparse files, truncate, stable directory
iteration, permissions/ACL/xattr, quotas, watches, page cache + read-ahead,
writeback, direct I/O, cancellation/deadlines, crash-consistent mount/unmount,
health/scrub. Do not claim a full POSIX profile while writable shared mapping
is absent (POSIX.1-2024 mapping requirements).
**Filesystem selection:** EFI/boot = FAT32 only. Production root v1 = one
mature journaled ext4-compatible FS service. tmpfs for /run. devfs/procfs/
sysfs-equivalent/pipefs. Containers = snapshot/overlay service. DBFS/NVFS
experimental until durability gates pass; optional root later. Never use boot
FAT32 as production root.
**Durability contract** published by VFS+block: sector/atomic-write
assumptions, flush/FUA, data-vs-metadata ordering, rename durability, dir
fsync, torn-write detection, cache volatility, TRIM, checksums, power-loss
recovery. (PostgreSQL WAL-before-data rule; SQLite WAL checkpoint semantics
depend on correct VFS locking/mapping/sync.)

## 9. SOSIX-native async API and POSIX profiles

Native model: `Future<Result<T>>`, CancellationToken, Deadline,
CompletionQueue, WaitSet, AsyncFd, SharedBuffer, ResourceHandle. Every op
supports completion, cancellation, timeout, partial progress, backpressure,
accounting, trace correlation, explicit ownership. POSIX blocking calls are
adapters over async (`read()` → `sosix_read_async()` → wait → errno) — no
independent sync implementations.
**Honest profiles:** A Simple Native (SOSIX, capability/async-first);
B POSIX Core (files, spawn/exec/wait, env, clocks, signals, pipes, sockets,
poll/select, terminal — no full-conformance claim); C POSIX Server (+pthreads,
futex-like, writable/private/shared mmap, file locks, AF_UNIX, robust signals/
EINTR, pgroups/sessions, termios subset, locale/tz subset, dlopen, shm, AIO, C
dev headers); D Linux personality (optional, user-space: epoll, eventfd,
timerfd, signalfd, /proc compat, ioctl translations, namespace/cgroup
translations). Do not define `_POSIX_VERSION=202405L` until actually conformant.
**Port-enabling order:** posix_spawn/exec/waitpid → signals+pgroups → full FD
semantics → pipes+AF_UNIX → poll/select → pthreads+sync → private+shared mmap
→ mprotect/msync/munmap → file/record locks → termios+PTY → dlopen → locale/tz
→ COW fork → extended compat. Fork is compatibility, not the native center.

## 10. TTY, PTY, shell, production SSH

ttyd owns /dev/console, /dev/tty, /dev/tty0…, /dev/pts/*, PTY allocation,
canonical/raw line discipline, output processing, termios ioctls, controlling
terminal, session + foreground pgroup, SIGINT/SIGTSTP/SIGHUP/SIGWINCH, winsize,
serial/display/remote backends. PTY data path must use real shared buffers or
pipe endpoints (master write → slave input queue → shell read; and reverse).
**SSH:** first production release ports OpenSSH Portable over POSIX Server
profile, PTYs via ttyd; Simple-native SSH stays experimental until it passes
the same interop + security suite (current source has x86-64-only FS-exec
handling, no-op arms elsewhere, documented runtime failures). Production SSH
needs: persistent host keys in secretd, authorized keys, authd-mediated
password auth, pubkey + certificates, SFTP/SCP, policy-controlled forwarding,
PTY/non-PTY, rate limiting, source penalties, connection/idle/auth limits,
audit, algorithm policy, key rotation, rekey, fuzzing of packet/KEX/auth
parsing. Map OpenSSH privilege separation to separate Jobs/CSpaces.

## 11. Interpreter/compiler/runtime/loader unification

Single owner per shared component: module resolver, module graph, type schema,
artifact manifest, target/ABI descriptor, **runtime extern registry** (the HTTP
report showed the self-hosted binary lacking an extern the seed had — a
generated authoritative registry kills this class), dynamic library resolver,
diagnostics format, symbol/debug metadata, cache identity.
**Generated runtime variants:** don't hand-duplicate nogc_sync_mut/
nogc_async_mut/gc_*/host/simpleos — canonical core + memory-policy traits +
mutation policy + async adapter + platform adapter + generated facades. Manual
hot-path specializations must pass the canonical contract tests.
**Migration rule for examples/**: name canonical owner → move one subsystem at
a time → temporary re-export adapter → run consumer+conformance tests → delete
old implementation → CI fails if old namespace regrows.

## 12. Startup argument parsing and preload-before-main

Extend the existing launch-metadata design (do not add a second preloader).
Manifest declares `argument_schema` + `preloads` (source_arg/fixed_path, mode
map_read_only, required, maximum_bytes, access, prefault, hash_policy).
Sequence: `_start` → read trusted manifest → generated minimal arg parser →
resolve preload bindings → cap-relative open → validate type/ownership/size/
digest → VMO-map or async prefetch → load declared libraries → StartupContext
→ `main()`. Host uses fd+mmap+madvise+host page cache; SimpleOS uses VFS
handle + file-backed VMO + pager read-ahead; same StartupContext API.
Security: only declared fields trigger preload; no directory scanning;
cap-rooted open; resolve once, consume verified handle; default RO non-exec
mapping; bound size/pages/time/concurrency; optional-preload failure falls
back, required-preload failure blocks main; prefetch never executes
constructors/plugins; hover prefetch warms bytes but never creates executable
mappings.

## 13. LLVM and native development environment

Proven: in-guest Simple interpreter; FS-resident Clang cc1 emitting
byte-correct x86-64 object. **Strictly sequential gate ladder:** (1) clang
--version via PATH/FS-exec, (2) cc1 emits object, (3) ld.lld starts via
FS-exec, (4) LLD links guest object, (5) resulting ELF starts from FS,
(6) expected status+output, (7) full clang driver, (8) tempfiles/pipes/
response files/diagnostics, (9) compiler-rt complete, (10) libc headers+
runtime pass suite, (11) libc++ + libunwind, (12) multithreaded compilation,
(13) shared-library loading, (14) debugger+symbolization, (15) build systems
without host proxying, (16) repeat arm64 + riscv64, (17) 32-bit as separate
compat tier. Maintain the LLVM-libc port as an OS config directory +
entrypoints.txt in upstream form, not a private monolithic sysroot script.
Required tools (all as ordinary FS programs, no boot-preloaded aliases, host
forwarding, ELF allowlists, per-program GOT hacks, or QEMU host exec): simple,
clang/clang++, ld.lld, llvm-ar/nm/objdump/readelf, make, ninja, CMake-compat
generator, debugger, profiler, test runner, package manager, VCS client,
archive tools, shell utilities.

## 14. Web server production program

The strongest benchmark used a pre-cached fixed response on raw TCP; the full
routed server ran interpreted. Target the full server; no benchmark-only fork.
Architecture: listener → per-core accept/demux → connection state machine →
parser → route/filter chain → static/proxy/app handler → response filters →
completion-driven write. Use SOSIX completion queues, per-core workers with
pinned connection ownership, bounded pools, slab/arena alloc, zero-copy
VFS→network, shared immutable static cache, TLS session cache, backpressure,
incremental parsing, deadlines, graceful worker restart, live config swap,
structured metrics. Implement nginx-equivalent event semantics directly over
SOSIX (not epoll emulation inside the server).
Protocol order: HTTP/1.1 → TLS 1.3 (audited provider) → reverse proxy →
static → WebSocket → HTTP/2 → QUIC/HTTP/3 → app framework. Pure-Simple TLS is
not production until constant-time review, side-channel tests, cert-path
validation, interop, fuzzing, independent review. Audited external TLS is
acceptable; RCE resistance beats language purity.
Fair benchmark matrix vs nginx (identical behavior): routed static, 1K/64K/1M
corpus, keep-alive on/off, TLS resume+full, real-upstream proxy, HTTP/2 mux,
dynamic handler, slow clients, churn, p50/p95/p99/p99.9, RSS/conn, CPU/req,
7-day soak, graceful reload, worker crash recovery.

## 15. Database production program

**Two products.** Simple DB Embedded: config, compiler metadata, package
indexes, local app data, low-contention tables — not a PostgreSQL competitor.
Simple DB Server: separate product (page store, buffer pool, WAL, recovery,
MVCC, query processing, auth, protocol, backup/ops) — currently absent.
**First DB milestone = SQLite port** over a proper SimpleOS VFS: exercises
locking, shm, mmap, fsync, atomic rename, WAL, checkpoints, concurrent
readers, crash recovery, power loss. Must pass upstream tests, WAL + rollback
journal tests, multi-process contention, forced process death, flush
reordering, ENOSPC, truncated WAL, corrupted shm index, checkpoint/restart.
**Server milestones (ordered):** page format+checksums → buffer pool → WAL+
group commit → deterministic recovery → B-tree/heap → transactions/snapshots →
MVCC → locks/deadlock → checkpoints → vacuum/GC → catalog → SQL parser/binder
→ planner/stats → executor → auth+TLS → backup/restore → online check →
replication → upgrades → admin tooling.
Compare embedded vs SQLite; server vs PostgreSQL only after equivalent
durability + isolation semantics. Immediate goal: correctness/durability
parity, then performance.

## 16. One config engine (std.config)

Extract `std.config`: schema, parser, round_trip_document, validate, migrate,
repair, layer, transaction, watch, secrets, cli, ui_model. Typed schema per
field: key, type, default, constraints, enums, category, label, description,
scope, owner service, sensitivity, restart requirement, live-apply, policy
lock, deprecated aliases, migration fn, doc link — generated from typed Simple
declarations, not hand-reconstructed structs.
Layer precedence: compiled default < vendor < machine < sysadmin < device <
user < named profile < workspace < session < **mandatory security policy**
(ceiling, not another editable layer).
System Settings and IDE consume the same schema/load/validation/migration/
repair/transaction/search model; user layout customization via a separate SDN
view doc that cannot alter types/validation/policy. VS Code compat via
importer/exporter mapping table; unsupported fields go to an import report,
never guessed. `simple config doctor`: detect unknown/deprecated/invalid,
migrate versions, propose repairs, preserve comments, diff, atomic apply,
rollback history. Live changes are transactions: validate-all → prepare →
apply → verify health → commit or rollback-all. Secrets in secretd; SDN holds
references only.

## 17. LLM CLI security profiles

Profiles per user: offline, code-review, workspace-write, network-research,
build-and-test, system-administration, custom. `effective = system ceiling ∩
user ceiling ∩ base grants ∩ overlay grants ∩ executable request − explicit
denies` (deny wins; never unrestricted union).
Dimensions: filesystem (read/write/exec roots, max size), network (dest, port,
protocol, DNS, loopback, listeners), process (spawn/signal/debug/attach, max
descendants), commands (exact executable/subcommand/arg-schema), devices, UI
(clipboard/screenshot/injection/a11y), secrets (labels, one-time, no
plaintext), models, resources (CPU/mem/storage/tokens/cost/wallclock),
approvals, audit, data classification, container template.
Every tool call passes policyd: normalize → identify resources → evaluate →
approval if required → short-lived capability → execute through broker →
revoke → audit. Never give an LLM CLI: root CSpace, inherited SSH agent by
default, unrestricted home read, unrestricted network, raw env secrets, broad
`sh -c` when a structured tool exists.
Audit record: timestamp, user, process/job/container, profile id+version,
model/provider, tool identity, normalized arg digest, resource identity, rules
evaluated, approval, capabilities issued, result, bytes r/w, destinations,
cost, redaction status. Lifecycle: versioned, signed, atomic, rollback, SDN
import/export, diff UI, simulation, explain-denial, expiration, per-project,
per-model ceiling, emergency global disable. Connect existing role/CSpace
research to actual spawn-time CSpaces.

## 18. Primary CLI tools

Pure-Simple core (certify): sosh, ls cat cp mv rm mkdir rmdir touch, pwd cd
env export, head tail wc sort uniq cut tr, grep find xargs sed, basic
awk-compatible, tee, ln readlink stat chmod chown, tar gzip zstd-compat, ps
top kill nice, mount umount df du, dmesg journal log, service, pkg, container,
sysctl, hostname date time, ip ping route ss dns, wget/curl-compat, simple,
config.
**Port rather than prematurely rewrite:** OpenSSH, SQLite, Clang/LLVM/LLD,
Git, Jujutsu (optional), TLS provider, compression libs — as normal SimpleOS
processes on POSIX/SOSIX. "Implemented in Simple" is a long-term preference,
never a reason to ship weaker SSH/crypto.
Tool provenance status per command: simple-native | ported-native |
compatibility-wrapper | host-proxy | stub. Production images contain **no
host-proxy and no user-visible stub** (current shell guide has permission
stubs and host-delegating Git/jj wrappers — invalid for a standalone host OS).

## 19. Browser production requirements

Process model: Browser (UI/tabs, nav policy, profile/permissions, renderer
lifecycle) | Network service (DNS, TLS, HTTP, cookies, cache, proxy) |
Renderer per site-isolation unit (HTML/CSS/DOM/JS/layout/paint; no direct FS
or raw network) | GPU process (validated commands, compositor, device grant) |
Storage service (local/session, IndexedDB, quotas) | media/utility.
Blockers: site isolation, browser-only JS capability profile, same-origin,
CSP, mixed-content blocking, cert validation, secure cookies, Fetch/CORS,
persistent event loop + rAF, monotonic-clock timers, canonical parser/DOM/
event path, brokered `file:`, no Node-style require/process/Buffer in page
runtime, renderer+GPU crash recovery, persistent profile/permissions, a11y
tree, memory limits + OOM recovery, download isolation, signed updates.
Gates: pinned WPT + Test262 corpora, TLS negative tests, top-site corpus,
origin-isolation, cookie/CORS suites, DOM mutation/event tests, renderer
escape tests, HTML/CSS/JS + GPU command fuzzing, restart/session restore, 10k
navigation soak, RSS tracking, **no missing artifact treated as pass** (the
hardening review found interaction evidence passing with absent artifacts —
CI must fail closed).

## 20. Production facilities not in the original request

Identity/auth (users/groups/service identities, password+key auth, privsep,
credential switching, sessions, lockout, ACL+capability integration). Network
admin (DHCP, IPv6, DNS resolver/cache, routing, firewall, VPN hooks, netns,
Wi-Fi, root store updates). Time (monotonic+realtime, NTP, tzdb, RTC,
suspend/resume correction, secure time for updates/certs). Resource mgmt
(memory pressure, OOM, CPU/I/O quotas, handle/process limits, per-service/
container accounting, pressure notifications). Operations (structured
journal, metrics, tracing, crash dumps, health, watchdogs, boot perf, remote
admin, diagnostic bundle). Power/lifecycle (shutdown/reboot, suspend/resume,
cpufreq/idle, device power states, battery, hotplug, thermal). Updates/
recovery (signed packages, transactional install, A/B or snapshots, rollback,
recovery env, secure+measured boot, key rotation, offline media — TUF-style
metadata for rollback/freeze defense, SLSA provenance attestations). Product
quality (a11y, l10n/Unicode, fonts/IME, installer, backup/restore, release
channels, ABI stability, deprecation policy, SDK, admin docs, vuln response,
support lifecycle, license/SBOM).

## 21. TDD, verification, evidence model

Order per feature: acceptance spec → abuse/security cases → failure-injection
→ perf budget → integration contract → unit/property tests → implementation →
conformance + soak. Never implement first and invent a matching test later.
Layers: architecture tests (duplicate-owner + dependency bans), ABI tests,
unit, property, integration (real IPC), QEMU, hardware, conformance (POSIX/
SSH/SQLite/browser/language), security (sandbox/rights/policy/fuzz), fault
(kill/timeout/ENOSPC/corruption/reset/power cut), performance, soak, upgrade.
**Formal invariants (Lean4 first, small core):** transferred rights ≤ sender
rights; child CSpace ⊆ authorized parent rights; reply objects single-use;
revoked generations unreusable; container cannot resolve outside its
namespaces; driver without IOMMU mapping cannot DMA; donated scheduling
context returned or cancelled; VFS transactions recover to pre-state or
committed; WAL commit implies flush ordering; restarted service retains no
stale device/secret grants. Formal complements live testing.
**Evidence receipt (SDN, per release gate):** commit, source_digest,
compiler_digest, image_digest, target, firmware, machine_or_qemu, test_id+
version, start_time, duration, result, metrics, logs, artifacts,
failure_reason. Rules: missing artifact = fail; stale artifact = fail;
expected string without causally verified behavior = fail; hosted fallback in
bare-metal test = fail; interpreter fallback in native-perf test = fail;
unsupported arch cannot silently pass.

## 22. Phased roadmap

- **Phase 0 — Truth/source-of-authority:** classify every OS component
  (production/partial/model/evidence-only/host-proxy/stub/duplicate); one
  canonical owner per subsystem; ADRs for kernel objects/IPC/process/VFS/
  driver/container/config; dependency graph; release profiles; automated
  duplicate-owner checks; remove false-green tests. Gate: every claimed
  feature points to executable evidence + a canonical implementation.
- **Phase 1 — Shared ABI + kernel objects:** typed handle/rights, endpoint/
  reply/notification, handle transfer, scheduling contexts, global process/job
  model, VMO/VMAR, pager, IRQ/timer, generation revocation, arch-neutral
  syscall ABI. Gate: two isolated processes call/reply, transfer a restricted
  VMO handle, donate budget, survive cancellation on x86-64/arm64/riscv64 QEMU.
- **Phase 2 — Process + FS execution:** unified SpawnSpec, live child CSpace
  installation, descriptor-based ELF exec, script/SMF/interpreter via same
  manifest, argv/envp/auxv, exit/wait/reap, signals/pgroups, resource domains,
  no non-root spawn_full. Gate: arbitrary signed executables launch from
  mounted FS with only declared rights and are reaped cleanly.
- **Phase 3 — VFS/storage/drivers:** one VFS, mount namespaces, FD/OFD model,
  page cache + pager, writable/shared mmap, production root FS, devfs/procfs/
  tmpfs, user-driver protocol, IOMMU+DMA revocation, NVMe+net drivers,
  durability contract. Gate: SQLite WAL survives forced crashes + block-fault
  injection; crashed user driver safely revoked and restarted.
- **Phase 4 — Services/POSIX/TTY/toolchain:** typed service manifests, health/
  watchdog, log/time/auth/secret services, TTY+PTY, POSIX Server profile,
  Clang/LLD compile-link-execute, build tools from FS, no host proxy. Gate:
  SSH in, compile C/C++, link, run tests, kill jobs, retrieve results.
- **Phase 5 — Containers/SSH/update security:** enforced containers, OCI
  adapter, rootless images, quotas, OpenSSH privsep, signed packages, TUF
  metadata, A/B rollback, SLSA provenance, LLM profile registry. Gate:
  container escape suite, compromised-update sims, SSH interop, policy
  attenuation all pass.
- **Phase 6 — Web/DB/config/CLI:** native web server, audited TLS, proxy+
  static, SQLite production port, DB server foundations, std.config, System
  Settings, pure-Simple coreutils, admin CLI. Gate: equivalent web benchmarks,
  SQLite recovery, config transactional rollback, sysadmin acceptance.
- **Phase 7 — Desktop/browser:** display/input/audio, compositor, desktop,
  browser process isolation, network service, origin/cookie/permissions, a11y,
  profile persistence, crash recovery, WPT/Test262/top-site gates. Gate:
  desktop hardware matrix + browser security/conformance with no host bypass.
- **Phase 8 — Production closure:** hardware qualification, secure boot,
  installer/recovery, soak, power-cycle, upgrade/rollback, SBOM + vuln
  process, ABI policy, docs, release engineering.

## 23. Multi-agent ownership (summary — execution detail in plan doc)

A00 Architecture/ABI · A01 Kernel IPC/Scheduler · A02 VM/Process/Loader ·
A03 VFS/Storage · A04 Drivers/Hardware · A05 SOSIX/POSIX/Network ·
A06 Services/TTY/SSH · A07 Container/Security/Update · A08 Language/Runtime/
LLVM · A09 Web/DB/CLI · A10 Config/Desktop/Browser · A11 Verification/Release.
Rules: A00 is sole writer of shared ABI; others propose via small RFC
(motivation, wire change, compat, security, tests, migration); generated
bindings not copied structs; one canonical path per subsystem; no `*_v2`/
`new_vfs`/`fast_loader2` trees without approved migrate-and-delete plan; every
shim carries a deletion condition; every change ships spec+tests+integration
evidence+security analysis+perf effect+rollback; A11 can reject readiness but
not rewrite; perf agents benchmark production paths only. Merge order: ABI →
kernel mechanism → service impl → compat adapter → product consumer →
old-path deletion.

## 24. First implementation tranche (ordered)

1. `production_status.sdn` — canonical owner + maturity per OS subsystem.
2. Architecture tests rejecting duplicate VFS/loader/IPC/config owners.
3. Freeze object_v1, ipc_v1, spawn_v1, rights definitions.
4. Global process manager replaces per-exec bootstrap scheduling.
5. SpawnSpec + real child CSpace installation in live spawn syscall.
6. Atomic handle transfer + single-use reply objects.
7. Restrict `spawn_full()` to root bootstrap task.
8. Descriptor-based executable loading.
9. Unify VFS mount + FD/open-description path.
10. Typed grants replace string service capabilities.
11. TTY output + PTY data queues on real endpoints.
12. Publish POSIX profile matrix; stop advertising unsupported features.
13. `/usr/bin/ld.lld` FS launch + guest compile-link-execute.
14. SQLite through the production VFS.
15. Extract std.config from IDE config implementation.
16. Versioned LLM Security Profile Registry.
17. OpenSSH over new POSIX/TTY path.
18. Full web server on native runtime; delete benchmark-only divergence.
19. Containers = Job + ResourceDomain + Namespace enforcement.
20. Begin browser renderer/network/GPU process separation.

## 25. Production definition (all must hold)

Arbitrary FS programs launch through one loader; no production service has
ambient full capabilities; containers enforced at kernel + service lookup;
one VFS for all production storage; durability demonstrated under power-fail;
crashed user drivers cannot retain IRQ/MMIO/DMA authority; POSIX claims match
implemented profiles; Clang/LLD compile-link-execute entirely in-guest; SSH
privsep + standard-client interop; services have typed manifests/health/
restart limits/logs; updates signed, fresh, transactional, reversible; all
core admin tools run locally (no host proxy); web comparisons use equivalent
production workloads; SQLite + DB recovery tests pass; browser renderer/
network/GPU isolated; config typed, versioned, migratable, transactional; LLM
processes get per-profile attenuated capabilities; x86-64/arm64/riscv64 have
reproducible QEMU evidence; each advertised hardware platform has real-device
evidence; release images have SBOM, provenance, recovery media, upgrade path;
missing or stale evidence always fails closed.

**Central decision:** not "add all remaining features" — make every existing
feature pass through one enforced capability/process/VFS/service/config/
evidence architecture, then delete every bypass and duplicate.
