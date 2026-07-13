# LLM Role Isolation: Per-Instance C-Spaces, Capability Containers, and the Spawn-With-CSpace ABI

**Status:** Research + concrete design (not committed to implementation yet)
**Date:** 2026-07-13
**Scope:** The driving use case for SimpleOS security: the SAME immutable application
binary running at DIFFERENT privileges depending on its assigned role — one instance is a
"ticketing LLM" (write-only access to the ticketing IPC channel, no filesystem), another
instance of the identical binary is a "scheduling LLM" (read/write calendar memory, no
ticketing). Covers: per-instance C-Spaces, zero-ambient-authority process start, immutable
content-addressed binaries, containers-as-capability-compartments, and the LLM
orchestrator lifecycle (attenuate → spawn → run → revoke).
**Method:** Web research on Capsicum, Fuchsia, seL4, WASI (preview1 + component model),
Nix, OCI/runc/gVisor/Firecracker, Singularity OS, and ocap literature (all cited inline),
plus repo recon of the existing SimpleOS capability/IPC/spawn infrastructure.
**Sibling docs (this design builds on both, does not repeat them):**
- `doc/01_research/os/security/privilege_ocap_sota_research.md` — SOTA survey (seL4 CDT,
  CHERI monotonicity, Fuchsia handles).
- `doc/01_research/os/security/capability_revocation_attenuation_research.md` — revocation
  and attenuation mechanisms; its §D recommends 4 layers (generation counters, kernel Gate
  objects, compiler-enforced monotonic attenuation, session arenas) which this design
  consumes as primitives.

**Existing SimpleOS assets this design builds on:**
- `src/os/kernel/types/capability_types.spl` — `CapabilityToken { kind, generation, owner,
  token_id, parent_token_id, depth }`; `CapabilityKind` (FileRead/Write/Exec(path_prefix),
  NetConnect/Listen(port), IpcConnect/IpcListen(port_name), SharedDataset(object_id,
  generation, rights), ProcessQueue(queue_id, generation, rights), ProcessSpawn, VmMap,
  DeviceGrant, …); `CapabilitySet`; `PrivilegeMask`; `Grant`.
- `src/os/kernel/ipc/capability.spl` — `CapabilityManager` with `delegate()` (child gets
  fresh `token_id`, `parent_token_id` lineage link, `depth - 1` delegation budget),
  generation equality validation, `revoke_transitive(root_token_id)` (iterative worklist
  over `parent_token_id` links), `init_task_record`,
  `capability_set_from_sandbox_lowering(task, sdn)`, pledge/unveil (`UnveilEntry`),
  `GrantTable.safecopy_from/to`.
- `src/os/kernel/scheduler/capability_bridge.spl` — `cap_init_task_record(task, full)`.
- `src/os/kernel/ipc/ipc.spl` + `src/os/kernel/types/ipc_types.spl` — `IpcManager`
  send/recv; `IpcFlags.CapTransfer` is DECLARED ("Message carries capability tokens",
  ipc.spl:112) but the transfer runtime is a stub.
- `src/os/kernel/types/endpoint_types.spl` — L4 model: `Endpoint { id, badge, buffer_phys,
  buffer_size }`, `IpcHeader { method: u32, cap_count: u16, flags: u16, payload_len: u32 }`,
  `WaitResult`, `IPC_OK/WOULD_BLOCK/INVALID_ENDPOINT/PERMISSION_DENIED/…`.
- `src/os/kernel/ipc/l4_fast_ipc.spl` — `L4InlineMessage32/64 { mrs…, badge }`,
  `L4BufferPool.transfer_4096` (register-message + bounded zero-copy models).
- `src/os/kernel/scheduler/process_isolation.spl` — `IsolationLevel` (struct with factory
  levels `none()/namespace()/container()/sandbox()`, boolean policy fields), currently
  ADVISORY; `ProcessIsolationPolicy`, `IsolationEnforcer`, `NamespaceRegistry`.
- `src/os/kernel/loader/fs_exec_spawn.spl` — `fs_exec_spawn_as(caller, path, argv, envp)`;
  `src/os/kernel/loader/cap_exec_gate.spl` — `exec_cap_check` (requires FileExec(path) +
  ProcessSpawn, but uses a throwaway per-call `CapabilityManager`).
- `src/os/kernel/ipc/syscall_process.spl` — `_handle_spawn` grants
  `CapabilitySet.full()` (lines 139, 654, 721) — THE ambient-authority hole.
- `src/os/kernel/loader/x86_64_fs_exec_ring3.spl` — `_build_sysv_stack_frame` (argc/argv/
  envp/auxv page, AT_PAGESZ/AT_RANDOM/AT_NULL) — the injection point for the C-Space ABI.
- `src/os/kernel/loader/container_namespace.spl` — `SimpleOsContainerContract`, evidence
  gates (pid/fs/ipc/net/capability), `/containers/` rootfs prefix enforcement.
- `src/os/services/llm/` — `OsMcpServer` + `tool_registry.spl` (`register_os_tools`:
  `process_spawn`, `file_read/write`, `system_exec`, …) — the natural orchestrator host.

**The four gaps this design fills** (confirmed by recon):
1. spawn/fork grant FULL caps or verbatim-inherit — no per-instance attenuated C-Space
   injection (`syscall_process.spl:_handle_spawn` → `CapabilitySet.full()`).
2. `IpcFlags.CapTransfer` exists but the cap-moving runtime is a stub.
3. No compiler-side capability enforcement (no sealed/ambient-free program mode).
4. `IsolationLevel` is advisory booleans, not derived-from/enforced-by capabilities.

---

## 1. The driving use case

One signed binary, `llm_worker`, is spawned twice:

| | Instance A: "ticketing LLM" | Instance B: "scheduling LLM" |
|---|---|---|
| Binary | blake3:9f3a… `llm_worker` | blake3:9f3a… `llm_worker` (IDENTICAL) |
| IPC | write-only cap to `svc.tickets` channel | none to tickets |
| Memory objects | model weights (read/map) | model weights (read/map) + calendar dataset (read/write) |
| Filesystem | NONE | NONE |
| Net | NONE | NONE |
| Spawn | NONE | NONE |

The binary must contain **no hardcoded paths** (`/var/log`, `/api/tickets`) and **no role
switch** (`if role == "ticketing"` reading a config file). Role = the set of capabilities
injected at spawn. This is pure dependency injection at the OS level: the app says "write
to the capability in slot 1", and *what slot 1 is* was decided by the spawner. If instance
A is prompt-injected into trying to read the calendar, there is no request it can even
express: it holds no calendar designator, and there is no global namespace in which to name
one ("no designation without authority" — the ocap core property
[Capability Myths Demolished](https://papers.agoric.com/assets/pdf/papers/capability-myths-demolished.pdf)).

Everything below exists to make that table real, cheap, and revocable.

---

## 2. What real systems teach

### 2.1 WASI — the closest mainstream model (preopens = injected slots)

WASI preview1 is the most direct precedent for "same binary, role decided by injected
handles":

- The runtime **preopens** host directories before instantiation and injects them as file
  descriptors **starting at fd 3** (0–2 = stdio). The module discovers them at startup via
  `fd_prestat_get(fd)` (returns tag `preopentype::dir` + name length) and
  `fd_prestat_dir_name(fd, buf, len)` (returns the *guest-visible name*)
  ([WASI preview1 spec](https://github.com/WebAssembly/WASI/blob/main/legacy/preview1/docs.md),
  [fd_prestat_get](https://wasix.org/docs/api-reference/wasi/fd_prestat_get)).
- **The libc startup scan is the injection-discovery pattern to copy**: wasi-libc's
  `__wasilibc_populate_preopens()` runs from `__wasm_call_ctors`, loops fds upward from 3
  calling `fd_prestat_get` until `EBADF`, and builds a path→fd table. A later
  `open("/foo/bar")` becomes `path_open(preopen_fd, "bar", …)` against the longest-prefix
  preopen; **no matching preopen → `ENOENT`** — "no capability" is indistinguishable from
  "doesn't exist"
  ([wasi-libc preopens.c](https://github.com/WebAssembly/wasi-libc/blob/main/libc-bottom-half/sources/preopens.c),
  [walkthrough](http://www.chikuwa.it/blog/2023/capability/)).
- The guest name is a **label, not a real path**: `wasmtime --dir HOST_PATH::GUEST_PATH`
  mounts a host dir under an arbitrary guest name; by default a WASI program has **no
  filesystem access at all** ([wasmtime CLI](https://docs.wasmtime.dev/cli-options.html)).
- Rights attenuate monotonically: preview1's `path_open` takes `fs_rights_base` +
  `fs_rights_inheriting`; granted rights must be a subset of the parent descriptor's
  inheriting set, and `fd_fdstat_set_rights` can only *remove* rights
  ([spec](https://github.com/WebAssembly/WASI/blob/main/legacy/preview1/docs.md)).
- **Component model (preview2)**: a WIT **world** declares exactly the imports a component
  may use — the import list IS the capability surface; anything not imported is
  unreachable ([worlds](https://component-model.bytecodealliance.org/design/worlds.html),
  [WIT](https://github.com/WebAssembly/component-model/blob/main/design/mvp/WIT.md)).
  Preopens become `wasi:filesystem/preopens.get-directories() -> list<tuple<descriptor,
  string>>` ([wasi-filesystem](https://github.com/WebAssembly/wasi-filesystem)).
  **WASI-Virt** shows attenuation-by-interposition: wrap a component in a virtualizing
  component (composed with `wasm-tools compose`) that denies, virtualizes, or passes
  through each subsystem — the wrapped component cannot tell
  ([WASI-Virt](https://github.com/bytecodealliance/WASI-Virt),
  [interposition principle](https://github.com/WebAssembly/WASI/blob/main/docs/Capabilities.md)).
- Design principle, verbatim target for SimpleOS: WASI has **"no ambient authorities: no
  global namespaces at runtime, and no global functions at link time"**
  ([DesignPrinciples.md](https://github.com/WebAssembly/WASI/blob/main/docs/DesignPrinciples.md)).

### 2.2 Capsicum — capability sandboxing retrofitted onto a Unix (FreeBSD)

Directly relevant because SimpleOS references FreeBSD:

- `cap_enter(2)` flips an **irreversible**, fork-inherited credential flag. In capability
  mode all **global namespaces** are cut off: absolute filesystem paths, the PID namespace,
  network address namespace, SysV/POSIX IPC names; violating syscalls fail `ECAPMODE`
  (only ~30 of ~3000 sysctl MIBs stay reachable)
  ([cap_enter(2)](https://man.freebsd.org/cgi/man.cgi?query=cap_enter&sektion=2&n=1),
  [capabilities.conf](https://github.com/freebsd/freebsd-src/blob/master/sys/kern/capabilities.conf)).
- Authority after `cap_enter` = **the file descriptors you already hold**, each limitable
  with `cap_rights_limit(2)` to a rights mask (`CAP_READ`, `CAP_WRITE`, `CAP_SEEK`,
  `CAP_FCNTL`, `CAP_LOOKUP`, `CAP_CONNECT`, `CAP_EVENT`, `CAP_MMAP_R/W/X`) — rights can
  only be **reduced, never regained**
  ([rights(4)](https://man.freebsd.org/cgi/man.cgi?query=rights)).
- Filesystem access shrinks to `openat(dirfd, relpath)`: absolute paths rejected, `..`
  escaping the dirfd subtree fails `ENOTCAPABLE`, dirfd needs `CAP_LOOKUP`
  ([open(2) FreeBSD](https://manpages.ubuntu.com/manpages/focal/man2/open.2freebsd.html)).
- Program structure (Watson/Anderson/Laurie/Kennaway, USENIX Security 2010): **acquire fds
  during privileged startup, then `cap_enter()`, then process untrusted input** — tcpdump
  was sandboxed in ~2 lines; Chromium in ~100
  ([Capsicum paper](https://www.usenix.org/legacy/event/sec10/tech/full_papers/Watson.pdf)).
- **Casper/libcasper**: needs that survive sandboxing (DNS, sysctl) are served by a
  delegated daemon over a channel (`cap_getaddrinfo` via `system.dns`), i.e. a proxy
  capability ([libcasper](https://man.freebsd.org/cgi/man.cgi?query=libcasper)).

Lesson: Capsicum proves the two-phase shape (inject-then-seal) works on a real Unix, but
because it *retrofits*, every program needs manual conversion. SimpleOS can make sealed
mode the default spawn mode.

### 2.3 Fuchsia — per-process handle tables + manifest-routed capabilities

- **Zircon handles** are per-process references to kernel objects; the same object can be
  held via handles with different rights (`ZX_RIGHT_READ/WRITE/DUPLICATE/TRANSFER`).
  `zx_handle_duplicate()` requires `ZX_RIGHT_DUPLICATE` and the new rights must be
  **strictly lesser or equal** — syscall-level attenuation
  ([handles](https://fuchsia.dev/fuchsia-src/concepts/kernel/handles),
  [handle_duplicate](https://fuchsia.dev/fuchsia-src/reference/syscalls/handle_duplicate)).
- Handles move between processes ONLY over channels: `zx_channel_write` (handle leaves the
  sender), and `zx_channel_write_etc` takes `zx_handle_disposition_t` with desired *final*
  rights — **attenuate-while-sending**, including stripping `ZX_RIGHT_TRANSFER` so the
  receiver cannot re-send
  ([channel_write_etc](https://fuchsia.dev/reference/syscalls/channel_write_etc)).
- **Process bootstrap = the injection ABI**: the loader writes a **processargs** message
  into the new process's bootstrap channel containing argv/env plus initial handles each
  tagged with a numbered `PA_*` id; `fuchsia.process.Launcher` builds the process and sends
  it ([program_loading](https://fuchsia.dev/fuchsia-src/concepts/process/program_loading)).
- **Component Framework v2**: `.cml` manifests declare `use` (capabilities placed in the
  instance's namespace, e.g. protocols at `/svc/fuchsia.logger.Log`), `offer` (grant to a
  child), `expose` (surface to parent); component manager walks the tree to route
  ([manifests](https://fuchsia.dev/fuchsia-src/concepts/components/v2/component_manifests),
  [namespaces](https://fuchsia.dev/fuchsia-src/concepts/process/namespaces)).
  **The same binary gets different power under different manifests** — precisely our
  use case, expressed declaratively.
- Programs have **no ambient authority**: "a newly created process cannot even allocate
  memory until its creator grants it capabilities"
  ([secure principle](https://fuchsia.dev/fuchsia-src/concepts/principles/secure)).
- Component URLs are content-anchored: `fuchsia-pkg://fuchsia.com/pkg#meta/comp.cm`,
  package identity = Merkle root of `meta.far`, blobs in content-addressed, write-once
  **blobfs** ([package](https://fuchsia.dev/fuchsia-src/concepts/packages/package)).

### 2.4 seL4 — the C-Space formalism

- A **CSpace** is a directed graph of **CNodes** (power-of-two capability-slot tables);
  capabilities are addressed by **CPtr** with per-CNode guards
  ([tutorial](https://docs.sel4.systems/Tutorials/capabilities.html)).
- `seL4_CNode_Mint` copies a cap with a **badge** and a **subset** of rights — never more;
  `seL4_CNode_Revoke` deletes **all caps derived** from the target across all CSpaces,
  tracked by the **capability derivation tree (CDT)**
  ([manual](https://sel4.systems/Info/Docs/seL4-manual-latest.pdf)). SimpleOS's
  `parent_token_id` chain + `revoke_transitive` is a CDT with explicit parent pointers.
- **Badged endpoints** identify senders: mint one badged endpoint cap per client; the badge
  arrives with each message — no ambient PID needed to know who called. SimpleOS's
  `Endpoint.badge` is exactly this.
- Caps ride inside IPC messages (`extraCaps` in `seL4_MessageInfo_t`); sending requires the
  **Grant** right on the endpoint; `seL4_Call` installs a one-shot reply cap
  ([IPC tutorial](https://docs.sel4.systems/Tutorials/ipc.html)). This is the semantics the
  `CapTransfer` stub should implement.
- Bootstrapping: the **root task** starts with ALL authority (BootInfo: untypeds + control
  caps) and constructs every other task's CSpace slot by slot
  ([untyped tutorial](https://docs.sel4.systems/Tutorials/untyped.html)) — authority flows
  strictly downward from one origin, the model for our orchestrator.

### 2.5 Object-capability principles (the theory)

- **Ambient authority** = authority exercised without explicit designation (any process
  can name `/etc/passwd`). Capabilities fuse **designation with authority**, which
  structurally eliminates the confused deputy
  ([Miller/Yee/Shapiro, Capability Myths Demolished](https://papers.agoric.com/assets/pdf/papers/capability-myths-demolished.pdf)).
- Standard patterns ([erights Walnut](http://wiki.erights.org/wiki/Walnut/Secure_Distributed_Computing/Capability_Patterns)):
  **attenuation** (facet/forwarder exposing a narrowed subset: read-only, N-uses, expiry);
  **caretaker** (revocable forwarder — the revoker is a *separate* capability);
  **membrane** (transitive caretaker over everything passing through). Sibling doc
  §B.3/§D.2 details these; this design uses caretaker-style kernel Gates for selective
  revoke and depth-limited delegation for containment.
- Lineage: GNOSIS → KeyKOS → EROS → Capsicum/seL4/Fuchsia
  ([KeyKOS](https://en.wikipedia.org/wiki/KeyKOS),
  [EROS](https://en.wikipedia.org/wiki/EROS_(microkernel))).

### 2.6 Immutability and content addressing (role-escape prevention)

- **Nix**: store paths `/nix/store/<hash>-name` where the hash covers *all inputs*; the
  store is read-only and packages are never modified in place; behavior is fully determined
  by declared inputs — **no mutable config drift**
  ([Nix derivation outputs](https://nix.dev/manual/nix/2.29/store/derivation/outputs/)).
  Content-addressed derivations hash the *output* instead (early cutoff)
  ([CA outputs](https://releases.nixos.org/nix/nix-2.31.0/manual/store/derivation/outputs/content-address.html)).
- **Fuchsia**: packages Merkle-rooted in write-once blobfs (§2.3).
- **OCI images**: manifest → config + layers, all referenced by `sha256:<digest>`; blob
  content MUST match its digest
  ([image-spec](https://github.com/opencontainers/image-spec/blob/main/manifest.md)).
- Why it matters here: if the binary or its config were mutable, a role could escape by
  editing what it *is* rather than what it *holds* (ticketing instance edits a config file
  to claim the calendar). With hash-identified immutable images and **no config file at
  all** (config = the C-Space), role behavior is a pure function of
  `(image_hash, injected_cspace)`. Singularity's **sealed processes** add the last piece:
  no dynamic code loading or self-modification inside a role
  ([Sealing OS Processes, EuroSys'07](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/EuroSys2007_SealedProcesses.pdf)).

### 2.7 Containers are a degenerate ocap system

A Linux container is not a kernel object — it is a stack of **subtractions** from a
process's enormous ambient authority:

| Mechanism | Subtracts | Source |
|---|---|---|
| namespaces (mnt/pid/net/uts/ipc/user/cgroup/time) | what you can SEE/name | [namespaces(7)](https://man7.org/linux/man-pages/man7/namespaces.7.html) |
| cgroups v2 (`cpu.max`, `memory.max`, `io.max`, `pids.max`) | how MUCH you can consume | [cgroup-v2](https://docs.kernel.org/admin-guide/cgroup-v2.html) |
| seccomp-bpf (Docker default blocks ~44 of 300+ syscalls) | which SYSCALLS | [Docker seccomp](https://docs.docker.com/engine/security/seccomp/) |
| capabilities(7) drops (drop CAP_SYS_ADMIN etc.) | which ROOT POWERS | [docker-caps](https://www.runxbuild.com/blog/docker-caps/) |

runc's OCI `config.json` (`mounts`, `linux.namespaces`, `linux.resources`,
`linux.seccomp`) is literally a **declarative list of subtractions**
([runtime-spec](https://github.com/opencontainers/runtime-spec/blob/main/config-linux.md)).
In ocap terms: Unix grants every process the user's full authority, then containers
laboriously carve it away — an ACL system emulating "starts with nothing" from the wrong
side. The failure mode is inherent: forget one subtraction (one mount, one syscall, one
capability) and authority leaks. An ocap OS inverts this: **start at zero, add exactly N
grants** — the container config and the C-Space recipe are the same artifact, but the
empty-by-default direction makes omission fail closed instead of open.

When the shared kernel is still too much attack surface, the industry pays overhead:
- **gVisor**: Sentry, a Go userspace kernel implementing the Linux syscall ABI (~240
  syscalls exposed, ~100 reach the host), platforms ptrace/Systrap/KVM, Gofer proxies the
  FS; cost ~2–10% CPU for syscall-light work, up to 2–3x syscall-heavy
  ([platforms](https://gvisor.dev/docs/architecture_guide/platforms/),
  [overview](https://northflank.com/blog/what-is-gvisor)).
- **Firecracker**: Rust microVM on KVM, minimal device model (virtio net/block/vsock);
  <125 ms boot, <5 MiB overhead, 150 microVMs/s/host; powers Lambda/Fargate; the *jailer*
  containerizes the hypervisor itself
  ([firecracker](https://github.com/firecracker-microvm/firecracker),
  [AWS](https://aws.amazon.com/blogs/aws/firecracker-lightweight-virtualization-for-serverless-computing/)).
- **Singularity OS (MSR)** — the escape hatch SimpleOS can take because it owns a safe
  compiler: all SIPs + kernel in ONE address space at ring 0, isolation from language
  type/memory safety; **software isolation costs <5% vs 25–33% for hardware protection
  domains**; ping-pong IPC round-trip **1,040 cycles vs 5,800 (Linux sockets)**; process
  creation **388k cycles vs 719k (Linux)**; channels are strongly-typed contracts over an
  **exchange heap** with static single-ownership = zero-copy pointer handoff
  ([Rethinking the Software Stack, OSR'07](https://courses.cs.washington.edu/courses/cse551/15sp/papers/singularity-osr07.pdf),
  [Deconstructing Process Isolation](https://www.microsoft.com/en-us/research/publication/deconstructing-process-isolation/)).
  Related: Theseus ([OSDI'20](https://www.usenix.org/system/files/osdi20-boos.pdf)),
  MirageOS unikernels ([ASPLOS'13](https://anil.recoil.org/papers/2013-asplos-mirage.pdf)).

**Conclusion for SimpleOS**: container-grade isolation without container overhead =
Simple-compiler-verified binaries run as software-isolated processes (SIP lane), sharing
an address space with cheap L4 register-IPC; the C-Space carries ALL policy; ring-3
address spaces (already implemented in `x86_64_fs_exec_ring3.spl`) remain the lane for
unverified/foreign code; a future VM lane (Firecracker-style) for hostile code.

---

## 3. The design

### 3.1 C-Space data structure (per instance, not per user)

Reuse `CapabilityToken` unchanged as the pouch entry; add a per-task slot table. New file
`src/os/kernel/ipc/cspace.spl`:

```simple
# One slot in a task's capability space. Slot index is the userspace name
# (the "fd 3" / PA_* analogue). The token is kernel-side; userspace never
# sees token internals, only the slot handle.
struct CSpaceSlot:
    occupied: bool
    token: CapabilityToken       # existing struct: kind/generation/owner/token_id/parent/depth
    label: text                  # role-neutral name: "ipc.tickets", "mem.calendar", "log"
    slot_gen: u32                # bumped on every free/reuse of THIS slot (stale-handle defense)
    flags: u32                   # CSLOT_TRANSFERABLE | CSLOT_DELEGABLE | CSLOT_SINGLE_USE

struct ResourceBudget:           # the cgroup analogue, held AS capability-like quota records
    cpu_ns_per_period: u64       # 0 = unlimited (root only)
    cpu_period_ns: u64
    mem_bytes_max: u64
    tasks_max: u32               # pids.max analogue: bounds spawn fan-out
    ipc_msgs_per_sec: u32        # flood control on endpoints
    io_bytes_per_sec: u64

struct CSpace:
    owner_task: u64
    sealed: bool                 # cap_enter analogue — see §3.4
    slots: [CSpaceSlot]          # dense array; MAX_CSPACE_SLOTS = 64 initial (grow by policy)
    budget: ResourceBudget
    session_id: u64              # arena tag for O(1) teardown (sibling doc §D.4)
```

**Userspace handle** = `u64 { slot_index: 32 | slot_gen: 32 }`. Unforgeability: userspace
only ever holds indexes into ITS OWN kernel-side table (Fuchsia/seL4/Unix-fd model); a
forged or stale handle fails the `slot_gen` check, and a revoked token fails the existing
`CapabilityManager` generation-equality check (capability.spl "same_gen"). Two independent
generation layers: slot reuse (per-slot) and object revocation (per-token, the sibling
doc's Layer D.1).

`CapabilityManager` gains a persistent per-task registry (fixing the
`cap_exec_gate.spl` throwaway-manager TODO):

```simple
struct CapabilityManager:        # existing fields retained
    ...
    cspaces: {u64: CSpace}       # task_id -> its C-Space (THE per-instance pouch)

    me cspace_of(task: u64) -> CSpace?
    me slot_lookup(task: u64, handle: u64, need: CapRightsMask) -> CapabilityToken?
        # decode handle -> check slot_gen -> check occupied -> validate token generation
        # -> capability_kind_allows(token.kind, need) -> return token or nil (ENOTCAPABLE)
```

Every syscall that today calls `check(task, required)` switches to
`slot_lookup(task, handle, need)` — **designation and authorization become one lookup**,
eliminating confused-deputy paths by construction.

### 3.2 spawn_with_cspace API

New syscall `SpawnWithCSpace` (next number after 13 `SpawnBinary`), plus a kernel-side
recipe type. `syscall_process.spl:_handle_spawn`'s `CapabilitySet.full()` (lines 139, 654,
721) is REPLACED by recipe evaluation; plain `SpawnBinary` becomes sugar for a recipe of
`[stdio inherit-attenuated]` — **empty pouch by default**, never full.

```simple
enum CapSource:
    DelegateFrom(parent_handle: u64)   # from the CALLER's own C-Space (the only normal source)
    MintRoot(kind: CapabilityKind)     # requires caller to hold MintAuthority (init/orchestrator)

struct AttenuationSpec:                # monotonic: every field may only NARROW the parent
    rights_keep: u32                   # subset mask (rights_new & parent_rights == rights_new)
    path_prefix_narrow: text           # "" = keep; else must extend parent prefix
    depth: i64                         # <= parent.depth - 1 (delegation budget, existing field)
    single_use: bool
    expiry_ms: u64                     # 0 = none; enforced lazily at slot_lookup

struct CapGrantSpec:
    dst_slot: u32                      # slot index in the CHILD C-Space
    label: text                        # what the child will see via cap_stat
    source: CapSource
    attenuation: AttenuationSpec
    flags: u32                         # CSLOT_* for the child's slot

struct SpawnSpec:
    image: ImageRef                    # §3.5: { hash: [u8;32], path_hint: text, require_seal: bool }
    argv: [text]
    envp: [text]                       # config VALUES only; never authority (see §3.4)
    grants: [CapGrantSpec]             # THE POUCH RECIPE
    isolation: IsolationLevel          # §3.6: now derived/enforced, not advisory
    budget: ResourceBudget             # must be <= caller's remaining budget (hierarchical)

pub fn spawn_with_cspace(caller: u64, spec: SpawnSpec) -> Result<u32, i32>
```

Kernel path (extends `fs_exec_spawn_as`, keeps `exec_cap_check`'s FileExec+ProcessSpawn
two-gate):

1. `exec_cap_check(caller, image)` — caller must hold `FileExec` (over the store prefix)
   and `ProcessSpawn`, now checked against the caller's PERSISTENT C-Space.
2. Verify image hash + signature against the content-addressed store (§3.5); select lane
   (SIP vs ring-3) from `isolation` + seal status.
3. Charge `spec.budget` against the caller's budget (hierarchical, cgroup-tree analogue;
   `tasks_max -= 1`).
4. For each `CapGrantSpec`: resolve source in the CALLER's C-Space; apply
   `CapabilityManager.delegate()` (existing: fresh `token_id`, `parent_token_id` = source,
   `depth - 1`) with the attenuation applied — kernel REJECTS any non-monotonic spec
   (`EPERM`), the seL4-Mint / `zx_handle_duplicate`-strictly-lesser rule.
5. Build the child `CSpace { sealed: from image manifest, slots: granted, budget, session_id: fresh }`.
6. Load image, build the startup frame with the C-Space manifest (§3.3), start the task.

Failure atomicity: any step failing unwinds all minted child tokens via
`revoke_transitive` on the session and refunds the budget.

**Fork** (where it survives at all — SIP lane has spawn only, like Fuchsia/Singularity):
child inherits the parent C-Space **verbatim-attenuated** (each token re-delegated with
depth-1, same rights) — never `full()`.

### 3.3 Resource-handle-injection ABI — how slot 1/2/3 reach the app

Three tiers, mirroring proven systems:

**Tier 0 — kernel → process (the raw ABI).** Extend `_build_sysv_stack_frame`
(`x86_64_fs_exec_ring3.spl`; same frame builder reused for the SIP lane) with one new
auxv entry, the Fuchsia-processargs / ELF-auxv hybrid:

```
AT_SIMPLE_CSPACE (private range, e.g. 0x53504C01) -> vaddr of a read-only mapped
                                                     CSpace Manifest Page
Manifest page layout (packed, little-endian):
  u32 magic 'SCSP' | u16 version | u16 entry_count
  entries[entry_count]:
      u32 slot_index | u32 slot_gen | u32 kind_tag | u32 rights_mask
      u16 label_off  | u16 label_len            # offsets into the string pool below
  string pool (labels, NUL-free, length-prefixed by the entry fields)
```

The page is mapped read-only into the child (kernel writes it once at spawn; in the SIP
lane it lives in the task's private region). Nothing in it is authority — it is a
*directory* of authority; the authority is the kernel-side slot table.

**Well-known slots** (fixed meaning, like WASI fd 0–2 + preopens-from-3):

| Slot | Label | Contents |
|---|---|---|
| 0 | `self` | this task's own task cap (introspection, exit) |
| 1 | `parent` | reply/request endpoint to the spawner (badged; the orchestrator line) |
| 2 | `log` | write-only log sink (structured; NOT a filesystem cap) |
| 3+ | role-defined | the pouch proper, discovered by scan |

**Tier 1 — runtime startup scan (the wasi-libc pattern).** New syscall + userlib:

```simple
# syscall: returns entry for slot or E_NO_SLOT past the end (scan terminator, like EBADF)
pub fn cap_stat(slot: u32) -> Result<CapStatInfo, i32>   # {slot_gen, kind_tag, rights, label}
```

`src/os/userlib/caps.spl` runs `_populate_cspace()` before `main` (the
`__wasilibc_populate_preopens` analogue): scan slots upward until `E_NO_SLOT` (or read the
manifest page directly when `AT_SIMPLE_CSPACE` is present — the syscall is the fallback),
build the label→handle map once.

**Tier 2 — the app-visible dependency-injection API.** Apps never name global resources:

```simple
use os.caps

fn main():
    val tickets = caps.get("ipc.tickets")       # Cap? — nil if this role wasn't granted it
    val calendar = caps.get("mem.calendar")     # nil for the ticketing instance
    ...
    caps.write(tickets!, payload)               # "write to the capability in slot N"
```

`caps.get` returns `nil` for an absent label — the WASI `ENOENT` property: *no capability
is indistinguishable from nonexistence*, so a prompt-injected instance cannot even probe
what it wasn't given. Legacy `open(path)` in sealed mode routes through the longest-prefix
match over `FileRead/FileWrite(path_prefix)` caps (the wasi-libc `path_open` translation);
no match → `ENOTCAPABLE`.

`envp` remains for pure configuration VALUES (temperature, prompt template name) — never
paths, never authority. This is the enforcement of "the binary has no hardcoded roles."

### 3.4 No ambient authority — the sealed mode (cap_enter, but default-on)

Unix: a process inherits ALL of the user's authority; every syscall re-decides via ACLs.
SimpleOS target = WASI's rule ("no global namespaces at runtime, no global functions at
link time") with Capsicum's mechanism:

- `CSpace.sealed = true` ⇒ every namespace-consulting syscall path is closed: no absolute
  `open`, no task-list enumeration, no `IpcConnect` by global port name, no
  device/sysctl-equivalent reads. The ONLY operative syscalls are slot-parameterized
  (`caps.read/write/call/map(handle, …)`) plus pure ones (clock via a granted TimeRead
  cap, memory within budget). Violations return `ECAPMODE`-analogue (`E_SEALED`).
- Sealing is **set at spawn from the image manifest** (`require_seal: true` for all LLM
  role images) and irreversible for the task lifetime, inherited by all descendants —
  Capsicum semantics, but chosen by the SPAWNER/manifest instead of by cooperative code
  calling `cap_enter` (retrofit lesson from §2.2: don't rely on the app opting in).
- A `cap_enter()`-equivalent (`caps.seal()`) is still exposed for the Capsicum two-phase
  pattern in *trusted* utilities (acquire, then seal before touching untrusted input).
- Post-seal needs that are legitimately global (name resolution, spawning sub-roles) go
  through **service capabilities** — a granted endpoint to a broker daemon, the
  Casper/libcasper pattern (§2.2), which in this OS is just another slot.
- Compiler layer (gap 3, sibling doc §D.3): Simple programs compiled with
  `--profile=sealed-role` get link-time enforcement — the ambient stdlib surface
  (`std.fs` path APIs, raw port connect) is simply ABSENT from the allowed import set,
  exactly a WASI **world**: the import list is checked at build time and stamped into the
  image manifest, so the kernel can trust (and the store can verify) that a sealed image
  *cannot express* an ambient call. Runtime sealing remains as defense in depth for
  hand-written or foreign code.

### 3.5 Immutable content-addressed role images

```simple
struct ImageRef:
    hash: [u8; 32]            # blake3 of the image bytes (content address, OCI-digest style)
    path_hint: text           # "/store/<hex>" — advisory; loader verifies hash regardless
    require_seal: bool

# RoleManifest — the .cml / WIT-world / OCI-config analogue, stored as SDN
# (extends the existing capability_set_from_sandbox_lowering(task, sdn) seed):
struct RoleManifest:
    role_name: text                     # "ticketing_llm"
    image: ImageRef
    sealed: bool
    world: [text]                       # allowed import surface (compiler-verified, §3.4)
    grants: [CapGrantSpec]              # the pouch recipe (labels + attenuations)
    budget: ResourceBudget
    isolation: IsolationLevel
```

- `/store/**` is a **read-only, content-addressed** region (Nix/blobfs model): file name =
  hash of contents, write-once, verified on load (Merkle/full-hash check), signature over
  the manifest binds `role_name → image.hash → grants`. `FileWrite` caps whose
  `path_prefix` intersects `/store` are unmintable (kernel invariant).
- Spawn is **by hash**, not by mutable path: `fuchsia-pkg`-style identity. The existing
  `container_namespace.spl` rootfs-prefix gates (`/containers/`, `/sys/apps/`) extend
  with `/store/` as the only executable-source prefix for sealed roles.
- **Why this closes role-escape**: role behavior = `f(image_hash, cspace)`. There is no
  third input. No on-disk config the instance can edit (its FS authority is nil or
  prefix-scoped away from `/store` and manifests), no in-place binary patching
  (write-once store + no `VmMap`-executable of writable pages in sealed mode = W^X), no
  dynamic code loading (sealed processes, Singularity §2.6). The ticketing instance and
  scheduling instance are bit-identical text; **the pouch is the entire difference**, and
  the pouch is kernel-side and revocable.

### 3.6 Container = C-Space + budget + visible-object namespace

Reframe (§2.7): a SimpleOS "container" is not a new kernel object — it is a *shape* of
C-Space:

```
container(instance) := ( CSpace.slots      — the namespace-of-visible-objects
                       , CSpace.budget     — the cgroup analogue
                       , CSpace.sealed + lane — the boundary strength )
```

- **Namespace-of-visible-objects**: Linux needs mount/pid/net namespaces to HIDE a global
  world; here there is no global world to hide — the label set IS the namespace. "PID
  namespace" degenerates to "which task caps you hold"; "mount namespace" to "which
  path-prefix file caps you hold"; "net namespace" to "which NetConnect/NetListen caps you
  hold". `NamespaceRegistry` (process_isolation.spl) is retained only as a
  *view/debugging* index over slot labels, not as an enforcement mechanism.
- **Budget**: `ResourceBudget` is charged hierarchically at spawn (§3.2 step 3) and
  enforced at the existing scheduler budget hooks (CPU budgets already exist in
  `green_carrier.spl` / `scheduler_algorithm.spl`) plus new allocator (mem_bytes_max) and
  endpoint (ipc_msgs_per_sec) checks. This is `cpu.max`/`memory.max`/`pids.max` semantics
  ([cgroup-v2](https://docs.kernel.org/admin-guide/cgroup-v2.html)) without a separate
  subsystem: the budget lives in the same per-instance record as the authority.
- **IsolationLevel becomes derived, not advisory** (gap 4). The existing boolean struct
  maps to constructive facts:

| `IsolationLevel` | Meaning today (advisory) | Meaning under C-Space (constructive) | Lane |
|---|---|---|---|
| `none()` | full host | unsealed + broad grants + MintAuthority | SIP or ring-3 |
| `namespace()` | hide PIDs | sealed=false, no task-enumeration caps | SIP |
| `container()` | no host fs/net | sealed + prefix-scoped fs caps + budget | SIP (verified) / ring-3 |
| `sandbox()` | everything false | sealed + minimal pouch + hard budget + no ProcessSpawn | SIP (verified) / ring-3 (foreign) |

  `IsolationEnforcer` is rewritten to VALIDATE that a spawn's grant list is consistent
  with the declared level (e.g. `container()` rejects a grant of `FileRead("/")`), making
  the level a checkable summary of the pouch rather than a parallel policy.
- **Isolation without container overhead** (the payoff): for Simple-compiler-verified,
  store-signed images, the lane is **SIP** — same address space, isolation = memory
  safety (proved at compile time) + C-Space (checked per designation) + budget. Expected
  cost profile is Singularity's: <5% vs 25–33% for hardware domains, ~1k-cycle IPC vs
  ~6k, ~2x cheaper task creation (§2.7 numbers). gVisor pays per-syscall interception and
  Firecracker pays per-VM memory *because they cannot trust the code*; SimpleOS's
  compiler manufactures that trust, and the hash+signature on the image carries the proof
  to the loader. Unverified binaries keep hardware lanes: ring-3 separate address space
  (implemented) or a future microVM lane; the C-Space model and injection ABI are
  IDENTICAL across lanes — only the wall thickness changes.

### 3.7 Capability transfer over L4 IPC (filling the CapTransfer stub)

seL4 semantics (§2.4) on the existing types:

- Sender: `caps.send(endpoint_handle, msg, transfer: [handle…])`. Kernel checks each
  handle's slot has `CSLOT_TRANSFERABLE` and the endpoint token carries the **Grant**
  right (new bit in the endpoint cap's rights mask). `IpcHeader.cap_count` = number of
  transferred caps (field already exists in `endpoint_types.spl`).
- Transfer is **move-with-optional-attenuation** (`zx_channel_write_etc` model): the
  message carries per-cap `AttenuationSpec`s; the kernel re-delegates
  (`CapabilityManager.delegate`, depth-1, monotonic-checked) into the receiver's first
  free slots and CLEARS the sender's slots (single ownership — the exchange-heap
  discipline, no aliasing of live authority).
- Receiver: `WaitResult` (existing) gains `caps_received: u16` + the base slot index; the
  arriving message's `badge` (existing `Endpoint.badge`, stamped at endpoint-cap mint
  time) tells the receiver WHICH client sent it — identity without a PID namespace.
- Fast path: `L4InlineMessage64` carries `cap_count <= 2` transfers inline (slot indexes
  resolved during the syscall, still one kernel crossing); larger sets ride
  `L4BufferPool.transfer_4096`.
- Reply caps: `caps.call()` installs a **one-shot reply cap** in the callee (seL4
  GrantReply), so a service can answer exactly once without gaining a persistent line to
  the client.

### 3.8 The LLM orchestration lifecycle

Host: `src/os/services/llm/` — `OsMcpServer` grows two tools (`role_spawn`,
`role_revoke`) beside the existing `process_spawn`. The orchestrator is an ordinary
sealed process holding a BROAD pouch (granted by init from the root task, seL4-style
§2.4): `ipc.tickets` (rw + Grant + delegable), `mem.calendar` (rw + delegable),
`mem.model_weights` (r + map + delegable), `MintAuthority` scoped to LLM-role kinds,
`ProcessSpawn`, a budget pool.

```simple
# ---- orchestrator pseudocode (userland, over the §3.2/3.7 APIs) ----

# 1. LOAD ROLE (immutable: hash-pinned manifest, §3.5)
val role = RoleManifest.load_verified("ticketing_llm")   # binds image hash + recipe

# 2. ATTENUATE — derive the pouch from the orchestrator's own slots (monotonic)
val grants = [
    CapGrantSpec(dst_slot: 3, label: "ipc.tickets",
                 source: DelegateFrom(my.slot("ipc.tickets")),
                 attenuation: AttenuationSpec(rights_keep: WRITE, depth: 0)),  # write-ONLY, no re-delegation
    CapGrantSpec(dst_slot: 4, label: "mem.model_weights",
                 source: DelegateFrom(my.slot("mem.model_weights")),
                 attenuation: AttenuationSpec(rights_keep: READ | MAP, depth: 0)),
]
# scheduling role differs ONLY here:
#   slot 3: "mem.calendar" READ|WRITE depth 0     (and NO ipc.tickets at all)
# summarizer role: "mem.calendar" READ, expiry_ms: task_deadline   (read-only facet)

# 3. SPAWN — same binary, different pouch
val pid = spawn_with_cspace(SpawnSpec(
    image: role.image,                       # blake3:9f3a… llm_worker — IDENTICAL for all roles
    argv: ["--role-prompt=tickets"], envp: [],
    grants: grants,
    isolation: IsolationLevel.sandbox(),
    budget: ResourceBudget(mem_bytes_max: 2*GiB, tasks_max: 0, ...)))?
session.track(pid, role.grants_session_id)

# 4. RUN — the worker's slot 1 ("parent") endpoint is badged with the instance id;
#    all its requests arrive at the orchestrator tagged, no ambient identity needed.

# 5. CROSS-INSTANCE: "scheduling LLM asks ticketing LLM to create a ticket"
#    The scheduler holds NO tickets cap. It sends a REQUEST (data, not authority)
#    up its slot-1 endpoint. Orchestrator policy decides between:
#    (a) PROXY: orchestrator forwards to the ticketing service itself (caretaker
#        pattern — full mediation, one extra ~1k-cycle hop on the SIP lane), or
#    (b) GRANT: mint a single-use attenuated cap and transfer it over IPC (§3.7):
val one_ticket = delegate(my.slot("ipc.tickets"),
                          AttenuationSpec(rights_keep: WRITE, depth: 0, single_use: true))
caps.send(endpoint_of(scheduler_pid), msg_grant_ticket, transfer: [one_ticket])
#    The scheduler's runtime sees a new slot appear (WaitResult.caps_received),
#    writes ONE ticket through it; the kernel clears the slot on use
#    (CSLOT_SINGLE_USE). No standing scheduler→tickets authority ever exists.

# 6. REVOKE — task end or anomaly (prompt-injection detector, timeout):
revoke_transitive(session.root_token_ids(pid))   # existing: parent_token_id worklist
#    kills the instance's grants AND anything it re-delegated (depth should have
#    prevented re-delegation anyway: defense in depth). O(subtree); the bulk
#    alternative is the sibling doc's D.1 generation bump on the backing objects
#    (O(1), revokes ALL holders) and D.4 session-arena teardown by session_id.

# 7. TEARDOWN — reap task; free CSpace slots (slot_gen++ each); refund budget to
#    the orchestrator's pool; audit-log the session's token lineage (the
#    parent_token_id chain is a complete provenance record of who could do what).
```

Why each ocap property earns its keep against LLM threat models:
- **Prompt injection ≠ privilege escalation**: the injected instruction "read the calendar
  and email it" dies at `caps.get("mem.calendar") == nil` — there is no name to attack.
- **Confused deputy blocked structurally**: the ticketing service acts on the cap in the
  MESSAGE (designation=authority), never on ambient caller identity, so the scheduler
  can't launder a request through a more-privileged intermediary.
- **Blast radius = pouch size**, and pouches are per-INSTANCE: two concurrent scheduling
  LLMs for two users hold disjoint calendar-object caps; compromise of one reaches one
  calendar.
- **Post-task authority is provably zero**: revocation is checked (generation equality) on
  every later use, not hoped for.

---

## 4. System-mapping table

| Concept | Capsicum | Fuchsia | seL4 | WASI | SimpleOS (this design) |
|---|---|---|---|---|---|
| Per-instance cap table | fd table + rights | handle table | CSpace/CNodes | fd table (preopens) | `CSpace.slots` |
| Userspace name | fd | handle (u32) | CPtr | fd | `{slot, slot_gen}` u64 |
| Enter zero-ambient mode | `cap_enter()` (opt-in) | by construction | by construction | by construction | `sealed` (manifest-set, default for roles) |
| Injection at start | inherited fds | processargs `PA_*` handles | root task builds CSpace | preopens from fd 3 | auxv `AT_SIMPLE_CSPACE` manifest page + well-known slots 0–2 |
| Discovery scan | n/a | processargs read | BootInfo | `fd_prestat_get` until EBADF | `cap_stat` until `E_NO_SLOT` |
| Attenuate | `cap_rights_limit` (reduce-only) | `zx_handle_duplicate` (strictly lesser) | `CNode_Mint` (subset + badge) | `rights_base/inheriting` subset | `delegate` + monotonic `AttenuationSpec` |
| Transfer | `sendmsg` SCM_RIGHTS | `zx_channel_write_etc` (attenuate-in-flight) | extraCaps + Grant right | (component composition) | `CapTransfer` msg, `IpcHeader.cap_count`, move+attenuate |
| Revoke | close fd | kill handle | `CNode_Revoke` over CDT | drop descriptor | `revoke_transitive` over `parent_token_id` + generation bump |
| Sender identity | n/a | koid | endpoint badge | n/a | `Endpoint.badge` (exists) |
| Role declaration | code structure | `.cml` use/offer/expose | CSpace construction | WIT world imports | `RoleManifest` (SDN) |
| Immutable image | n/a | blobfs Merkle root | n/a | wasm module hash | `/store/<blake3>` write-once + signed manifest |
| Resource budget | rctl | jobs | untyped quota | fuel/store limits | `ResourceBudget` in CSpace (cgroup analogue) |
| Cheap isolation lane | n/a | process | process | in-process sandbox | **SIP** (compiler-verified, Singularity model) |

---

## 5. Implementation plan (phased, mapped to files)

| Phase | Work | Files | Depends |
|---|---|---|---|
| P1 | `CSpace`/`CSpaceSlot`/`ResourceBudget` types; persistent `cspaces` map in `CapabilityManager`; `slot_lookup`; fix `cap_exec_gate` throwaway manager | new `src/os/kernel/ipc/cspace.spl`; `capability.spl`; `capability_types.spl`; `cap_exec_gate.spl` | — |
| P2 | `SpawnSpec`/`CapGrantSpec`/`AttenuationSpec`; `spawn_with_cspace` syscall; replace `CapabilitySet.full()` at `syscall_process.spl:139/654/721` with recipe eval; fork = inherit-attenuated | `syscall_process.spl`, `fs_exec_spawn.spl`, `userlib/process.spl` | P1 |
| P3 | Injection ABI: `AT_SIMPLE_CSPACE` manifest page in `_build_sysv_stack_frame`; `cap_stat` syscall; `userlib/caps.spl` startup scan + `caps.get/read/write/call/map` | `x86_64_fs_exec_ring3.spl`, `arm_fs_exec_spawn.spl`, new `src/os/userlib/caps.spl` | P2 |
| P4 | Sealed mode: `E_SEALED` gate on ambient syscall paths; `caps.seal()`; sealed-prefix `open` translation | syscall dispatch, `userlib` fs shim | P3 |
| P5 | `CapTransfer` runtime: Grant right, move+attenuate, `WaitResult.caps_received`, single-use slots; inline ≤2-cap fast path | `ipc.spl`, `syscall_ipc.spl`, `endpoint_types.spl`, `l4_fast_ipc.spl` | P1 |
| P6 | Budget enforcement: hierarchical charge at spawn, allocator + endpoint hooks (reuse scheduler CPU budgets) | scheduler files, `cspace.spl` | P2 |
| P7 | Immutable store: `/store` write-once + hash-verify on load; `ImageRef`/`RoleManifest` SDN (extend `capability_set_from_sandbox_lowering`); spawn-by-hash; extend `container_namespace.spl` gates | loader, `capability.spl`, `container_namespace.spl` | P2 |
| P8 | `IsolationEnforcer` rewrite: level ⇒ grant-list validation (constructive levels) | `process_isolation.spl` | P2 |
| P9 | Orchestrator: `role_spawn`/`role_revoke` tools; session tracking; the two-role demo | `src/os/services/llm/tool_registry.spl`, `mcp_os_server.spl` | P2–P7 |
| P10 | Compiler `--profile=sealed-role` world check (import-surface allowlist stamped into manifest) | compiler + manifest verify | P7 |

## 6. Verification gates (spec tests)

1. **Two-pouch gate** (the headline): spawn the SAME image twice with ticketing vs
   scheduling recipes; assert (a) ticketing instance: `caps.get("mem.calendar") == nil`,
   calendar syscall by forged handle → `E_STALE/ENOTCAPABLE`; (b) scheduling instance:
   tickets write → `ENOTCAPABLE`; (c) both: any absolute `open` → `E_SEALED`.
2. **Attenuation monotonicity**: recipe asking for rights ⊄ parent → spawn fails `EPERM`;
   `depth 0` cap cannot be re-delegated or transferred onward.
3. **Revocation liveness**: revoke mid-run; the instance's very next use of a granted
   handle fails generation check; transferred single-use caps die with the session.
4. **Transfer**: scheduler→ticket single-use grant flow end-to-end; slot cleared after one
   use; badge correctly identifies sender at the ticketing service.
5. **Budget**: `tasks_max: 0` role cannot spawn; `mem_bytes_max` breach kills only the
   instance; budget refunds on teardown (no leak across 1000 spawn/teardown cycles).
6. **Immutability**: store blob bit-flip → load refused (hash mismatch); sealed role
   attempting `VmMap` writable+executable → refused (W^X).
7. **Default-deny regression guard**: grep-gate that `CapabilitySet.full()` no longer
   appears in any spawn path.

## 7. Open questions / risks

- **SIP-lane trust root**: the SIP lane's isolation is exactly as strong as the Simple
  compiler's safety guarantee + the signature chain on `/store` images. Until the
  compiler's memory-safety story is audited end-to-end (unsafe FFI surfaces, `mmio`
  escape hatches), default sealed roles to the ring-3 lane and treat SIP as an
  optimization gate, not a security assumption. (Singularity had the same caveat: its
  TCB includes the verifier.)
- **Slot-table sizing**: 64 dense slots suffices for LLM roles; services brokering many
  clients need growth or a second-level table (seL4's guarded multi-level CSpace is the
  fallback design if dense arrays hit limits).
- **Expiry enforcement** is lazy (checked at `slot_lookup`); a never-used expired cap
  lingers until session teardown — acceptable (it grants nothing) but audit tooling
  should show it.
- **Revocation of mapped memory** (`SharedDataset` already mapped via `VmMap`): generation
  bump stops NEW maps but an existing mapping needs unmap-on-revoke (TLB shootdown in
  ring-3 lane; SIP lane can drop the reference at the next safepoint). This is the
  hardest revocation case — sibling doc §A.5 (CHERI Cornucopia) is the literature anchor.
- **Orchestrator as single point of authority**: it is deliberately the root of the role
  subtree (auditable choke point), but it must itself run sealed with a scoped pouch —
  init grants it LLM-domain caps only, never `MintAuthority` over device/kernel kinds.

## 8. References

Indexed sources (fetched 2026-07-13):

- WASI preview1 spec — https://github.com/WebAssembly/WASI/blob/main/legacy/preview1/docs.md
- wasi-libc preopen scan — https://github.com/WebAssembly/wasi-libc/blob/main/libc-bottom-half/sources/preopens.c
- WASI design principles (no ambient authority) — https://github.com/WebAssembly/WASI/blob/main/docs/DesignPrinciples.md
- WASI capabilities/interposition — https://github.com/WebAssembly/WASI/blob/main/docs/Capabilities.md
- Component model worlds — https://component-model.bytecodealliance.org/design/worlds.html
- WASI-Virt — https://github.com/bytecodealliance/WASI-Virt
- wasmtime `--dir` — https://docs.wasmtime.dev/cli-options.html
- wasi:filesystem preopens — https://github.com/WebAssembly/wasi-filesystem
- Capsicum paper (USENIX Sec '10) — https://www.usenix.org/legacy/event/sec10/tech/full_papers/Watson.pdf
- cap_enter(2) — https://man.freebsd.org/cgi/man.cgi?query=cap_enter&sektion=2&n=1
- rights(4) — https://man.freebsd.org/cgi/man.cgi?query=rights
- FreeBSD capabilities.conf — https://github.com/freebsd/freebsd-src/blob/master/sys/kern/capabilities.conf
- libcasper — https://man.freebsd.org/cgi/man.cgi?query=libcasper
- Fuchsia handles — https://fuchsia.dev/fuchsia-src/concepts/kernel/handles
- zx_handle_duplicate — https://fuchsia.dev/fuchsia-src/reference/syscalls/handle_duplicate
- zx_channel_write_etc — https://fuchsia.dev/reference/syscalls/channel_write_etc
- Fuchsia program loading (processargs) — https://fuchsia.dev/fuchsia-src/concepts/process/program_loading
- Fuchsia component manifests — https://fuchsia.dev/fuchsia-src/concepts/components/v2/component_manifests
- Fuchsia namespaces — https://fuchsia.dev/fuchsia-src/concepts/process/namespaces
- Fuchsia packages (Merkle/blobfs) — https://fuchsia.dev/fuchsia-src/concepts/packages/package
- Fuchsia secure principle — https://fuchsia.dev/fuchsia-src/concepts/principles/secure
- seL4 capabilities tutorial — https://docs.sel4.systems/Tutorials/capabilities.html
- seL4 IPC tutorial — https://docs.sel4.systems/Tutorials/ipc.html
- seL4 untyped/bootinfo — https://docs.sel4.systems/Tutorials/untyped.html
- seL4 manual — https://sel4.systems/Info/Docs/seL4-manual-latest.pdf
- Capability Myths Demolished — https://papers.agoric.com/assets/pdf/papers/capability-myths-demolished.pdf
- erights capability patterns — http://wiki.erights.org/wiki/Walnut/Secure_Distributed_Computing/Capability_Patterns
- KeyKOS — https://en.wikipedia.org/wiki/KeyKOS ; EROS — https://en.wikipedia.org/wiki/EROS_(microkernel)
- namespaces(7) — https://man7.org/linux/man-pages/man7/namespaces.7.html
- cgroups v2 — https://docs.kernel.org/admin-guide/cgroup-v2.html
- Docker seccomp — https://docs.docker.com/engine/security/seccomp/
- OCI runtime spec — https://github.com/opencontainers/runtime-spec/blob/main/config-linux.md
- OCI image spec (digests) — https://github.com/opencontainers/image-spec/blob/main/manifest.md
- gVisor platforms — https://gvisor.dev/docs/architecture_guide/platforms/
- Firecracker — https://github.com/firecracker-microvm/firecracker
- Firecracker (AWS) — https://aws.amazon.com/blogs/aws/firecracker-lightweight-virtualization-for-serverless-computing/
- Nix derivation outputs — https://nix.dev/manual/nix/2.29/store/derivation/outputs/
- Nix CA derivations — https://releases.nixos.org/nix/nix-2.31.0/manual/store/derivation/outputs/content-address.html
- Singularity OSR'07 (numbers) — https://courses.cs.washington.edu/courses/cse551/15sp/papers/singularity-osr07.pdf
- Singularity sealed processes (EuroSys'07) — https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/EuroSys2007_SealedProcesses.pdf
- Deconstructing Process Isolation — https://www.microsoft.com/en-us/research/publication/deconstructing-process-isolation/
- Theseus (OSDI'20) — https://www.usenix.org/system/files/osdi20-boos.pdf
- MirageOS unikernels (ASPLOS'13) — https://anil.recoil.org/papers/2013-asplos-mirage.pdf
