<!-- Saved verbatim 2026-09-05 from external research (first pass, snapshot 320e6d9). Repo verification and stale-claim list: README_tldr.md in this directory. -->

# Simple Runtime Unification Through SOSIX
## Research, design, implementation plan, and SimpleOS feature requests

**Date:** September 5, 2026  
**Repository:** `ormastes/simple`  
**Inspected source snapshot:** `320e6d99e4b8b8540a65078f68ce8ffca15fd2b6`  
**Status:** proposed design and implementation plan. Source inspection and primary-source research were performed; implementation tests and hardware benchmarks were not run.

The selected architecture unifies OS-service access through SOSIX while preserving one common task/ring contract: async first, no-GC base, explicit synchronous POSIX bindings, typed renderer host services, and a restricted GPU projection. Native GPU-issued hardware queues are separately qualified SimpleOS extensions.

### Contents

[Architecture and design](#architecture) · [Implementation plan](#implementation-plan) · [SimpleOS feature requests](#simpleos-feature-requests) · [Sources and evidence limits](#sources)

---

<a id="architecture"></a>
## Part I — Architecture and design

**Research, architecture, and migration design — 2026-09-05**  
**Status:** proposed implementation contract; source-inspected, not a claim of completed implementation.  
**Inspected repository snapshot:** `ormastes/simple@320e6d99e4b8b8540a65078f68ce8ffca15fd2b6`.  
**Companions:** [implementation plan](#implementation-plan), [SimpleOS feature requests](#simpleos-feature-requests), [source register](#sources).

### 1. Decision

Unify **OS-service access and execution contracts**, not every runtime implementation into one large binary. SimpleOS, hosted applications, the compiler as a host application, the interpreter, JIT, loader, and rendering hosts should consume the same SOSIX service contracts. Providers differ by environment. The existing common task/ring architecture remains the foundation; SOSIX must not create a competing Future, scheduler, or queue ABI. [R3](#r3)

The chosen stack is:

```text
Simple application / compiler driver / interpreter / loader / UI host adapter
                              |
                  SOSIX typed service contracts
             async first; explicit synchronous surface
                              |
          capabilities + operation admission + service policy
                              |
          existing SimpleRing / task / completion contracts
                              |
        hosted native providers           SimpleOS providers
        io_uring / readiness /            IPC / services /
        bounded compatibility pool        drivers / device queues

Trusted exact-ABI synchronous POSIX binding:
    sosix.sync.posix.read -> libc read
    (no Future, ring, scheduler, or rt_read forwarding hop)

GPU projection:
    GPU-local operations, or a bounded SOSIX proxy request,
    or an explicitly admitted device-initiated queue backend
```

"Through SOSIX" means one authoritative contract, authority model, and provider-selection boundary. It does **not** mean every local operation must cross a ring, use a virtual dispatch table, or enter the kernel. A statically selected compatible synchronous provider may compile to the native call itself.

The no-GC base is mandatory for the shared execution substrate. Heap allocation, pre-admitted arena allocation, and genuinely static/no-allocation operation are separate deployment choices. A higher-level GC application may use the base, but cannot make the base depend on GC.

#### 1.1 Requirement traceability

| User requirement | Decision | Main implementation work |
|---|---|---|
| Async Future/Promise first; sync second; no-GC | One canonical operation/task model, async default service names, explicit sync import, no-GC storage policies | WP-02, WP-03 |
| Direct POSIX calls on Linux-like platforms; no direct `rt_*` use | Exact native bindings under SOSIX; adapters only where semantics differ; private legacy ABI retained during migration | WP-01, WP-04, WP-05 |
| Merge rendering host access into SOSIX | Display, input, timer, configuration, library and device-service capabilities; renderer algorithms remain outside SOSIX | WP-06 |
| Sync API resembles POSIX | Raw exact-ABI POSIX submodule plus safe typed sync adapters; no claim that every `rt_*` is an alias | WP-04 |
| Study JS/TS async libraries | Adopt composable awaits, structured lifetime and stream backpressure; do not copy GC ownership or assume native kernel async | WP-03 |
| CUDA/Vulkan/Metal SOSIX subset through host proxy | Same operation semantics; restricted GPU projection; portable batch transport first | WP-07, WP-08 |
| Most GPU work must avoid sync APIs | Host-blocking effects rejected in device call graphs; logical task suspension instead of spin | WP-07 |
| SimpleOS GPU direct hardware queues | Explicit feature backlog with queue grants, DMA lifetime, isolation, reset and real-hardware evidence | FR-SOSIX-DQ-001–012 |

### 2. What the inspected source establishes

This is a focused architecture audit, not a repository-wide count or runtime benchmark. Source comments identify some limitations; executable evidence is still required before declaring a provider production-ready.

| Area | Observed evidence | Consequence |
|---|---|---|
| Hosted SOSIX | `nogc_async_mut/sosix/host_facade.spl` explicitly distinguishes itself from the SimpleOS-internal SOSIX tree. It uses inline pass-throughs and several real adapters. [R1](#r1) | Unification is incomplete; shared vocabulary alone is not a common provider contract. |
| Alias support | The host facade records that renaming re-export syntax failed against the seed. [R1](#r1) | Do not present `export use ... as ...` as a working zero-cost solution. Use same-name exports where supported and explicit external-symbol metadata where necessary. |
| SimpleOS async read/write | `io_rw.spl` performs VFS requests, chunk loops and copies before returning its request ID. [R2](#r2) | "Async" naming does not establish nonblocking submission. Replace this implementation path. |
| SimpleOS sync wrappers | The inspected `sosix_sync_read/write` contain `while ...: continue` completion waits. [R2](#r2) | Remove busy waiting; use admitted native synchronous operations or scheduler/notification waits at legal boundaries. |
| Request storage | That local I/O implementation uses 128 state/result slots, linear allocation and plain request indices. [R2](#r2) | Move to canonical ring identity, slot generation, admission errors and exact wake routing. |
| Rendering transport | One inspected DrawIR adapter serializes SDN text, submits it, then immediately drains and dispatches the queue. [R5](#r5) | This adapter needs separation of submit/completion and a packed production payload path. This observation does not characterize every renderer backend. |
| Runtime linkage | The Rust runtime already has a shared symbol-provider abstraction, ABI versioning and Core/Alloc/Sys/Async/Ext tiers. [R6](#r6) | Extend or generate this registry; do not add an independent loader/interpreter SOSIX registry. |
| Existing enforcement | `raw_rt_access.spl` is a warning-level text-heuristic lint, with sanctioned-provider exceptions. [R7](#r7) | Keep it as an early guard; add semantic call-graph and binding checks, with a migration ratchet. |
| Existing architecture | The common ring/task architecture is explicitly proposed and does not claim all native providers or compiler lowering are implemented. [R3](#r3) | Preserve its contract names, but separately qualify each implementation. |

Two additional correctness investigations belong in the first work package. In the inspected `io_rw.spl`, the serial write branch reports the requested byte count without emitting bytes in that function. The local sync wrappers also map a request-allocation failure sentinel to a bad-descriptor-style result. Reproduce these paths against their actual backend wiring before assigning root cause; add tests that prevent fabricated success and distinguish capacity exhaustion from an invalid handle. [R2](#r2)

The existing renderer-host research already recommends the same boundary: SOSIX owns host access, not DrawIR, scene layout, rasterization or GPU cache state. This document extends that decision to the compiler, interpreter, loader and GPU service projection. [R4](#r4)

### 3. Architectural ownership

#### 3.1 One foundation, several embeddings

| Owner | Owns | Must not own |
|---|---|---|
| Common execution contracts | `SimpleRing`, tokens, admission/completion vocabulary, task polling contract, profile identity | Linux descriptors, GPU command buffers, allocation strategy or OS scheduling implementation |
| No-GC execution library | Task/operation storage, exact wakes, cancellation scopes, bounded combinators, profile-specific executors | A second service authority model |
| SOSIX contracts and policy | Typed service APIs, capabilities, service discovery, operation requirements and admission | Renderer algorithms or compiler IR |
| Hosted providers | Native POSIX bindings, io_uring/readiness translation, platform display/input and library loading | Different Future semantics |
| SimpleOS providers | Service IPC, queue grants, interrupt completion ingress, driver integration | A parallel application task ABI |
| Compiler | Effect/domain analysis, frame lowering, external-symbol mapping and import requirements | Performing runtime service operations while lowering |
| Interpreter/JIT | Their execution representation and checked invocation of the same contracts | A hand-maintained incompatible syscall or completion model |
| Loader | Version/capability checks, dependency activation, symbol resolution and unload safety | Per-I/O scheduling policy |
| Engine2D/render backends | Rendering resources, encoding, raster/compute work and backend synchronization | General application filesystem, process or input policy |

Reuse the existing paths identified by the ring architecture: common contracts under `src/lib/common/contracts/execution`, hosted ring/provider implementation under `src/lib/nogc_async_mut/async_ring`, and no-allocation adapters under `src/lib/nogc_async_mut_noalloc/async`. The exact placement of added SOSIX contract files must follow the repository's capsule/export conventions, not force hosted code to import `src/os` internals. [R3](#r3)

The compiler has **two distinct environments**: the host environment in which it reads sources and launches tools, and the target environment for emitted code. Host SOSIX provider selection must not be changed simply because the compiler is emitting SimpleOS or GPU code. Record host and target independently in manifests and test cross-compilation explicitly.

#### 3.2 What stays outside SOSIX

Local arithmetic, string algorithms, object layout, reference validation, value boxing, compiler IR traversal and local arena/pool operations remain library or private runtime operations. Their eventual acquisition of backing pages may use a SOSIX memory provider; each individual allocation must not become an OS-service request.

Likewise, GPU-local queue manipulation and device-local compute are not host calls. SOSIX authorizes their resources and exposes applicable contracts, but need not execute their local instructions.

Retain compiler-private runtime helper symbols where required by existing binaries. The rule is **no product-level direct raw runtime access**, not "rename every runtime symbol to SOSIX." This distinction is necessary because the inspected runtime's CoreRequired set includes value, string, array and allocator helpers, not only OS calls. [R6](#r6)

### 4. Public API and async semantics

#### 4.1 Naming and source compatibility

Use the following **proposed namespace convention**:

```text
sosix.fs.read_at(...)              -> asynchronous operation
sosix.net.receive(...)             -> asynchronous operation
sosix.input.next_batch(...)        -> asynchronous operation
sosix.display.present(...)         -> asynchronous operation
sosix.time.deadline(...)           -> asynchronous operation

sosix.time.monotonic_now()         -> immediate local/provider snapshot
sosix.input.try_take_batch(...)    -> immediate bounded attempt

sosix.sync.fs.read_at(...)         -> safe typed synchronous adapter
sosix.sync.posix.read(...)         -> exact native POSIX ABI on supported hosts
```

Preserve existing `sosix_*_async` or `sosix_async_*` exports as compatibility entry points until consumers migrate. Do not silently change an existing synchronous function's return type because it happens to reside in an async module.

The examples in this document describe proposed contracts; they are not claims that the exact namespace, generic syntax or new metadata already compiles in every Simple compiler lane. Prefer existing syntax and generated bindings over grammar extensions.

"Async default" applies to naturally deferred service work. It does not require a Future for a bounds check, clock snapshot, cache lookup or nonblocking ring attempt. Future compiler inference may preserve sequential-looking source, but the initial implementation uses the already supported explicit async mechanisms. Compiler inference is a separately gated extension, not a prerequisite for the service migration. [R3](#r3)

#### 4.2 Future, Promise and submission

`Future<T>` is the consumer view of a canonical task result or operation result. A `Promise<T>` is a restricted producer/resolver view. Neither owns a second scheduler. A GPU operation wrapper is another projection of the same operation identity, not an incompatible Future implementation.

Default resource-sensitive Futures are single-consumer and move-owned. Shared observation is explicit and has an admitted observer count and storage budget. Do not add implicit unbounded lists of callbacks or refcount cycles. General compute-task results can use the same observation contract without manufacturing a SOSIX I/O operation.

An I/O convenience API validates and reserves capacity, then commits once. The provider may observe it only after commit. A batch API permits construction and reservation of several operations before an explicit batch commit. Failed admission never secretly submits or drains work to make space.

Illustrative contract shape:

```text
read_at(file: FileReadCapability,
        destination: RegisteredWriteLease,
        offset: u64,
        options: OperationOptions)
    -> Future<Result<ReadReceipt, SosixError>>

try_prepare_read_at(...)
    -> RingAdmission<PreparedRead>

commit(prepared)
    -> Future<Result<ReadReceipt, SosixError>>
```

A fixed-size immediate-result representation must handle validation and admission failures without allocating a task or slot. "Queue full" is a typed admission failure, not an invalid descriptor, a silent retry loop, automatic heap growth, or an implicit flush.

#### 4.3 Continuation behavior and combinators

Public callback-style continuations should run through the owning executor rather than synchronously reentering user code inside a provider completion callback. A ready-value `await` may be optimized inside generated task code only when observable ordering, cleanup and fairness remain valid. Simple is adopting Promise-like composition, not promising exact JavaScript microtask ordering.

The initial library should provide `map`, `and_then`, `join`, bounded `all`, `all_settled`, `race`, `timeout`, and scope-based cancellation. `all` over an input of unknown size must require a concurrency limit or admission budget. `race` does not destroy losing in-flight buffers; losers remain owned until cancellation and retirement finish. Define `all` error policy explicitly: the recommended default requests cancellation of siblings, then performs structured cleanup before scope release.

A `Promise.resolve`-like operation can set a local result but cannot forge a provider completion or release a foreign operation slot. Failed duplicate resolution is observable in diagnostics and rejected by the state machine.

#### 4.4 JS/TS research decisions

| Source | Useful precedent | Adaptation for Simple |
|---|---|---|
| ECMAScript Promise model [E1](#e1) | Composable fulfillment/rejection and queued reactions | Typed results and executor-owned continuation delivery; no requirement for GC-managed Promise graphs |
| Node `fs/promises` [E2](#e2) | Clear awaited I/O facade alongside explicit synchronous functions | Async default SOSIX surface; keep implementation strategy visible in provider metadata |
| libuv design [E3](#e3) | Readiness-driven networking and pool-backed blocking work coexist | One provider interface; bounded compatibility workers, not a second task system |
| Deno API [E4](#e4) | Async functions and explicitly named synchronous counterparts | Clear opt-in sync imports; no accidental blocking based only on module placement |
| WHATWG Streams [E5](#e5) | Backpressure, reader/writer composition and byte-stream specialization | Bounded streams and caller-supplied registered buffers; no hidden growth |
| WHATWG abort model [E6](#e6) | A cancellation signal is separate from the Promise result | Cancellation request and final operation outcome are distinct |
| Effect Scope [E7](#e7) | Resource lifetime and finalizers tied to a scope | Parent-owned no-GC task/resource lifetime and bounded async cleanup |

Node's documentation explicitly states that promise-based filesystem work uses the underlying thread pool. Therefore a Promise return type is not evidence of native kernel asynchronous I/O. [E2](#e2) The SOSIX provider receipt must distinguish native completion I/O, readiness translation and admitted blocking compatibility work.

No Node, Deno, Effect or JavaScript engine dependency is required to implement these ideas. TypeScript typing conventions are ergonomic references, not an ownership or ABI solution for native/GPU Simple.

### 5. Operation lifetime, scheduling and no-GC storage

#### 5.1 Canonical state model

Reuse existing `RingToken` identity, slot and generation rather than defining a new public request-index convention. [R3](#r3)

```text
Unreserved -> Reserved -> Committed -> TerminalResult
                  |                       |
                  +-> Released            +-> Retired -> Reusable

Cancellation: a request affecting an existing lifecycle, not another completion.
Reset: admission stop + quiescence protocol + generation invalidation.
```

`TerminalResult` and `Retired` are distinct facts. Retirement is owner/provider lifetime bookkeeping; adding it must not silently change the frozen public completion encoding or existing ABI. A timeout, device-loss notification or cancellation result does not prove that a driver or DMA engine has stopped using a buffer. Reuse requires both result-lifetime completion and provider retirement. The common public single-shot operation has exactly one terminal result even if the native backend emits several internal notifications.

For a safe borrowed-buffer API, the buffer must not become accessible to its former owner until retirement. The normal convenience API returns a usable completed buffer lease only when this condition is satisfied. An early deadline notification may return control while the resource remains held by the parent scope; it cannot return an unrestricted mutable buffer. Scope shutdown waits for safe retirement or escalates to a documented device-reset/quarantine policy. Physical I/O cancellation is not rollback of already committed writes.

Keep resource epochs, ring generations and module lifetimes separate. A stale token is rejected without waking a new task. Generation wrap is specified and fails closed rather than creating an ABA collision.

#### 5.2 Executor and provider progress

Preserve `poll(frame, context) -> Ready(result) | Pending(wait_token)`. Polling, completion delivery and provider submission must not block. The completion record selects the exact task/waker key; no periodic scan of all Futures. [R3](#r3)

A provider must close the check/register/recheck race when a task subscribes to readiness. Duplicate wakeups may be coalesced, but a wakeup cannot be lost. Notification arming and queue ownership transfer have explicit ordering rules.

The executor uses a finite work budget per turn. Completion floods, microtask-style continuation chains, input bursts and compute tasks must not starve each other. Timer checks, control messages and cancellation receive reserved progress capacity. A full data queue must not prevent the control operation required to drain or reset it.

A native synchronous call is allowed on a thread explicitly admitted for blocking work. It is rejected inside the UI executor, provider completion callback, device task, interrupt handler or other no-blocking context. A synchronous outer application runner may drive the executor it owns; an embedded library must not secretly start a nested event loop or pump arbitrary user callbacks to make a blocking API appear safe.

#### 5.3 Storage profiles

| Profile | Storage decision | Restrictions |
|---|---|---|
| General no-GC hosted | Explicit owned heap/arena/slab allocations; bounded queues | No GC dependency; allocations remain accountable |
| Server no-GC | Pre-admitted task/operation slabs and registered buffers | No unplanned steady-state hot-path allocation |
| `mission_alloc` | Sealed capacity with approved arena/slab allocation | No unrestricted post-admission heap, ISR allocation or hidden growth |
| `mission_pool` | Static/compiler-known bounded storage | No general heap after Ready; bounded task frames, timers, joins and cancellation records |
| Optional GC application | GC objects above a no-GC bridge | Explicit roots/pins/ownership conversion; GC never frees an in-flight DMA buffer |

These profile names preserve the existing ring plan. [R3](#r3), [P1](#p1) A module under a `nogc_*` directory is not, by its name alone, proven allocation-free or safe for interrupts.

Compute the admitted memory bound as:

```text
M = task-frame pools + operation records + ready/control rings
  + provider descriptor/completion storage + registered data buffers
  + stream/event storage + timers + joins/cancellation records
  + optional bounded trace storage + admitted backend-private memory
```

Every term includes alignment, metadata and worst-case concurrency. A native graphics or OS provider whose internal allocations are not controlled cannot be advertised as end-to-end `mission_pool` merely because Simple's own queues are static. State exactly which boundary has the no-allocation guarantee.

Use single-owner pools and rings where practical. Cross-core or CPU/GPU ownership is transferred through explicit ingress. Pool references carry generations; a raw address of a temporary stack buffer cannot escape into deferred work. No-GC scopes must define cleanup on ordinary completion, cancellation, exception/panic boundaries and failed startup.

### 6. POSIX-compatible synchronous calls without a raw runtime hop

#### 6.1 Three categories, not one blanket rename

| Category | Example | Correct implementation |
|---|---|---|
| Exact host ABI and semantics | Raw `read`, `pread`, `write`, selected native clock functions | SOSIX source binding resolves directly to the native libc symbol |
| Safe typed synchronous API | Capability plus registered-buffer `read_at` returning a typed result | Small explicit adapter for capability validation, conversion and error capture |
| Higher-level operation | Read UTF-8 text, capture process stdout/stderr, safe path resolution | Real library/service implementation; not a POSIX alias |

The native raw compatibility surface can use familiar POSIX names. The capability-based API is recommended for normal Simple applications. Do not call a typed result, a different ownership contract or a conversion between `text` and C strings an ABI alias.

POSIX `read` uses the open-file-description offset; `pread` uses an explicit position without changing that offset. They are not interchangeable. [E8](#e8) In particular, do not implement concurrent `read_at` with an unlocked `seek` followed by `read`.

#### 6.2 Binding mechanism

Prefer a same-name module export when the language can already preserve the external symbol. Where a different Simple name is required, attach an external-symbol mapping to the existing binding/ABI registry and lower references to that symbol. No new grammar is required for the first generated-binding implementation.

Illustrative **metadata**, not newly claimed Simple syntax:

```text
logical_export: sosix.sync.posix.read
external_symbol: read
calling_convention: target_c
signature: (c_int, c_void_mut_ptr, size_t) -> ssize_t
execution_domain: host
may_block: true
provider: posix_libc
error_convention: minus_one_and_thread_errno
```

Required AOT result:

```text
caller -> read@libc
```

Not:

```text
caller -> sosix_read_wrapper -> rt_read -> read@libc
```

A true binding alias is a compiler/linkage decision, not necessarily an ELF alias object defined next to libc. Do not rely on platform-specific linker aliases to external definitions as the universal implementation.

The interpreter may still need a checked FFI invocation/marshalling adapter; its overhead is not zero. JIT and AOT should use the shared registry to emit direct external references where legal. Resolve dynamic provider symbols once at load/activation, not by a string lookup per read.

#### 6.3 Conditions for an exact alias

An alias is admitted only when the execution domain, calling convention, parameter and result layout, error convention, ownership, blocking behavior and relevant side effects match. The binding generator must use the actual target's C ABI definitions, not assume `long`, `size_t`, `ssize_t`, `off_t`, `time_t`, `stat` or `timespec` have one universal representation.

Raw POSIX callers retain raw POSIX error behavior. A typed adapter captures `errno` on the thread that executed the native operation before another call or suspension can disturb it. By contrast, the io_uring completion path carries the native result/error in completion data; it must not read the waiting task's unrelated thread-local errno. [E9](#e9)

Classify variadic functions, macro-like APIs and target-specific structures separately. Generate fixed-signature helpers only when necessary and report them as adapters. Do not blanket-retry interrupted close, write or process operations without a per-operation semantic rule.

A direct POSIX binding is not automatically authorized in a sandbox. The raw module requires a trusted-native/unsafe host capability. Sandboxed applications use checked SOSIX capabilities and providers; preventing direct symbol imports is only one part of isolation, not a substitute for OS-enforced protection.

#### 6.4 Legacy compatibility and cycle prevention

Keep existing exported runtime symbols long enough for bootstrap binaries and older modules. New product code uses SOSIX. During migration, choose exactly one dependency direction for each operation:

```text
temporary: new typed adapter -> existing private provider implementation
final:     old exported compatibility symbol -> canonical provider implementation
```

Never allow both directions for the same operation. A generated dependency check rejects `SOSIX -> rt_* -> SOSIX` cycles. Preserve signatures and ABI-major compatibility until an explicit versioned removal.

`@always_inline` is useful for a temporary pass-through but is not proof of zero overhead in every optimization mode or interpreter. Qualify the final native alias with disassembly, relocation and allocation evidence. [R1](#r1)

### 7. Native providers and feature interfaces

#### 7.1 Service contract versus native mechanism

SOSIX is a family of versioned service interfaces, not one ever-growing generic `syscall(opcode, Any)` entry point. Common operation semantics are shared; service-specific request and result types remain statically checkable. Native queue descriptors remain private to the provider.

| Feature family | Required services | Synchronous leaves or controls |
|---|---|---|
| Files and directories | Open/close, explicit-offset I/O, stream I/O, metadata, flush, directory iteration | Trusted exact POSIX bindings; cached metadata only when explicitly a snapshot |
| Network and IPC | Connect/accept/send/receive, bounded channels, notifications | `try_send`, `try_receive`, capability inspection |
| Processes | Spawn, wait, termination request, captured streams | Process identity/configuration snapshots |
| Time | Deadlines, sleep-until, periodic subscriptions | Monotonic clock with documented domain/resolution |
| Memory and buffers | Backing-region acquisition, registration, mapping and retirement | Bounded local pool allocation after admission |
| Libraries/modules | Open, resolve, activate, quiesce, unload | Checked immutable dispatch-table access after activation |
| Display | Session/surface lifecycle, image lease, present and capture/readback | Current surface-state snapshot |
| Input | Keyboard, pointer, text/IME, focus and hotplug event streams | Bounded `try_take_batch` |
| GPU execution | Device/queue/resource capability acquisition, work submission, completion and loss notifications | Capability query and local command preparation |
| Other devices | Typed USB/serial/audio/job extensions with explicit versions | Device-specific nonblocking operations |
| Configuration/diagnostics | Immutable startup configuration, bounded trace/log submission | Snapshot lookup and local trace append |

This is a requested interface inventory, not a statement that all providers exist. Feature absence produces `Unsupported` or an admission failure, never a dummy handle or fabricated successful completion.

Give each feature interface its own version, operation schema and optional capabilities. Avoid a mandatory global vtable entry for every possible device. Statically linked compositions may devirtualize provider selection; dynamic compositions use immutable, checked dispatch tables.

#### 7.2 Provider selection

On Linux, prefer a qualified io_uring provider for operations it actually supports. Readiness-driven nonblocking descriptors and a bounded blocking compatibility pool cover other operations when the profile admits them. Probe actual kernel/operation support and deployment restrictions; do not select purely by OS name. The API can remain async while a provider is classified as translated or blocking-compatible. [E9](#e9)

Other hosted platforms bind their native completion/readiness, window/input and library mechanisms behind the same contracts. Do not wrap every synchronous libc function in a Future and run it inline. Conversely, do not force an exact synchronous POSIX call through an async ring merely to make the internal diagram uniform.

SimpleOS providers use existing service/driver boundaries and native notifications. The kernel scheduler may remain a distinct implementation from a hosted executor, but they obey the same application task and operation semantics. Kernel-private scheduling objects do not become public SOSIX handles.

Provider manifests report supported operation IDs, semantic versions, blocking/allocation behavior, registration limits, cancellation and retirement guarantees, affinity, mapping grade and permitted fallback. Interface presence alone is insufficient for admission.

### 8. Rendering host integration

#### 8.1 Merge the host boundary, not rendering semantics

Keep the existing renderer architecture:

```text
GUI / Web / WM semantics
        -> DrawIR / prepared scene
        -> Engine2D / rendering backend
        -> GPU or CPU rendering
```

Move its environment dependencies to SOSIX:

```text
surface and window lifecycle -> SOSIX display service
keyboard/mouse/text ingress  -> SOSIX input stream
frame timing and deadlines  -> SOSIX time service
capture/files/QMP/processes -> SOSIX file/process/IPC services
backend selection           -> startup configuration snapshot
native library loading      -> SOSIX library service
GPU completion/resource life-> shared SOSIX operation contracts
```

This follows the existing renderer-host research, which already identifies these dependencies. [R4](#r4) The service facade may temporarily implement the old `screen_host`/host-facing interfaces so that UI callers migrate without a flag day. Backend-specific winit, SDL, Cocoa, Win32 or similar types stay private to the provider.

Do not send a host request for each pixel, primitive, CSS property or widget. Submit frame-sized or larger admitted batches, resource deltas and input batches. DrawIR serialization for diagnostics is not the production wire ABI. The text serialization and immediate drain in the inspected DrawIR adapter are explicit migration targets, not behavior to preserve permanently. [R5](#r5)

#### 8.2 Display contract

A surface capability includes an identity and generation. A frame lease identifies the surface generation, frame sequence, image/resource ownership and dependencies. The service supports asynchronous create, resize, acquire, present, readback and close.

Distinguish three facts: **submission accepted**, **rendering finished**, and **presentation/display feedback received**. A queue-submission completion is not proof that pixels were shown. Providers lacking precise presentation feedback must expose that limitation instead of synthesizing a displayed timestamp.

Resize publishes a new generation and resolves outstanding leases under a defined drain/drop policy. Stale frames cannot be presented to a replacement surface. Close stops admission, drains or cancels outstanding operations and retires images before releasing native resources.

Configure maximum frames in flight and explicit overload behavior. Frame dropping may be allowed for replaceable rendering updates; it must not silently drop a capture request or leak a leased image. CPU-rendered and headless providers implement the same lifecycle without pretending to be GPU-backed.

Platform affinity is part of the contract. Operations requiring a platform event thread are marshalled to that thread and completed back to the owning task. The main-thread pump integrates with the chosen application embedding; an arbitrary worker cannot take ownership of a platform window loop.

#### 8.3 Keyboard, mouse and other input

Use one typed event ingress with separate physical-key and text-composition events. Keyboard scancodes/key identifiers are not a substitute for Unicode text or IME composition. Pointer events include the relevant coordinate space, absolute/relative motion, buttons, wheel/scroll units and device identity. Include focus, device add/remove and a stream resynchronization event.

Each source supplies a sequence and timestamp with a declared clock domain. Preserve ordering per source; do not pretend independently timestamped devices have a perfect global physical ordering. Cross-source merge policy is documented.

Motion events may be coalesced under an explicit policy. Key/button transitions, focus loss, composition boundaries and hotplug are not silently discarded. On overflow, report loss, invalidate derived pressed-state as necessary and obtain a fresh state snapshot; otherwise a dropped release can leave a permanently pressed key or mouse button.

GPU consumers receive admitted fixed-layout event batches or a qualified local/mapped queue. They do not directly call the host window library. Variable text payloads use bounded registered storage and a validated encoding/length contract.

USB, serial, gamepad/touch, audio and printer/plotter services are extensions, not untyped `ioctl` forwarding. Real-time audio needs an independent bounded buffer/QoS contract even though it reuses the ring and completion model.

### 9. GPU access: restricted SOSIX projection

#### 9.1 Two directions of GPU integration

Separate **CPU code submitting GPU work** from **GPU code requesting OS services**. They share resource and completion semantics but have different call legality and transports.

A CUDA kernel cannot call a host libc function merely because Simple has a source-level alias. Likewise, a Vulkan or Metal shader's ability to generate device work does not imply an OS syscall ABI. GPU code uses the admitted projection described below. The existing GPU report already establishes this restricted-service approach. [P2](#p2)

#### 9.2 Preserve existing service tiers

| Tier | Meaning | Initial examples |
|---|---|---|
| G0 | GPU-local operation on pre-granted state | Local pool allocation, queue attempt, event-batch consumption, bounded trace append |
| G1 | GPU request serviced by a host/SimpleOS proxy | Pre-opened file `read_at/write_at`, pre-opened socket data, IPC/channel operations |
| G2 | Qualified direct-data or device-initiated provider | Direct storage/NIC data paths; later GPU-initiated dedicated device queues |

Do not merge **direct data transfer** and **device-initiated control** into one capability. NVIDIA GPUDirect Storage documents CPU-issued cuFile APIs even when the data path avoids a CPU bounce buffer. That is useful G2 direct-data support, but is not sufficient evidence of device-initiated operation. [E13](#e13) BaM is a research precedent for GPU-initiated storage access, not proof that SimpleOS currently provides it. [E14](#e14)

Retain the existing profile vocabulary: `CpuReference`, `HybridVectorGpu`, `ResidentGpu`; `StageFallbackPolicy.Forbid/AllowHybrid/AllowCpu`; and `StorageCapabilityTier.Staged/Direct/DeviceInitiated`. Use the previously proposed `GpuIoPreference` values rather than inventing a second fallback vocabulary. A fallback receipt records requested and actual behavior. [P2](#p2), [P3](#p3)

#### 9.3 Initial device API subset

| Operation | GPU disposition |
|---|---|
| Read/write at offset on an authorized open file and registered buffer | G1 first; optional qualified direct-data/device-initiated provider |
| Send/receive on an authorized socket/channel | G1 first; optional qualified NIC path |
| Input batch consumption, trace append, bounded local allocation | G0; ingress/egress transport still qualified |
| Timer/deadline subscription | Proxy operation or calibrated provider mechanism; raw device clock is not automatically host monotonic time |
| Present request for an existing frame/surface lease | Typed extension through the presentation service; normally batched host control |
| Open arbitrary paths, DNS, new sockets/processes or modules | Host control plane in the initial subset |
| `fork`, arbitrary `mmap`, host pthreads/signals, raw `ioctl`, privilege changes | Not part of the initial device projection |
| USB/audio and additional devices | Additive typed extensions after independent lifecycle and bounds design |

The existing GPU report assigns filesystem IDs beginning at `0x0101`, networking at `0x0201` and IPC at `0x0301`; do not reassign those IDs. It also excludes several control-plane operations from its frozen initial subset. This document does not silently broaden that frozen set. [P2](#p2)

#### 9.4 Host proxy architecture

```text
GPU logical task / subgroup aggregator
    -> bounded request batch
    -> transport ownership transfer
    -> host proxy ingress and validation
    -> canonical SOSIX admission
    -> native provider / admitted compatibility worker
    -> provider result and safe-retirement tracking
    -> bounded GPU completion batch
    -> resume GPU logical task
```

The host proxy is a service client and transport adapter, not a separate semantic scheduler. It uses the canonical operations and CPU executor. GPU runnable tasks remain owned by the GPU execution subsystem.

Validate operation/version, queue epoch, capability identity/generation, resource rights, registered buffer identity/generation, access direction, offset/length overflow, deadline class, quota and result capacity. An untrusted GPU record cannot name an arbitrary host pointer, native file descriptor, callable address or resolver.

Aggregate requests per logical task, workgroup or shard rather than per lane wherever possible. Bound each tenant's in-flight count, bytes, completion credits and continuation state. Preserve per-resource ordering when required, while permitting independent operations to overlap. Avoid a single global proxy mutex or one blocking request stalling all other queues.

The proxy may execute a native synchronous provider only in a bounded blocking lane. The requester still observes an asynchronous SOSIX operation. The primary proxy event/completion loop must not call that blocking routine inline.

#### 9.5 GPU suspension, not busy waiting

The portable GPU `await` model is:

```text
save typed live state -> publish operation -> end/deactivate this logical task
completion arrives -> enqueue continuation -> execute a later task/dispatch
```

Start with staged finite kernels and explicit continuation records. They work without claiming device-wide preemption or a permanently resident scheduler. Backend-specific persistent schedulers or device graphs are later optimizations and require proven progress, occupancy bounds and loss recovery.

Do not let GPU lanes spin waiting for a CPU service while occupying resources needed by the next GPU dispatch that will produce their completion. Do not use a grid-wide barrier to wait for a proxy operation unless the entire execution/progress contract has been separately established.

A common **semantic task contract** does not imply identical CPU and GPU frame bytes. Host function pointers and host stack addresses must not appear in device continuation records. Backend lowering supplies device-specific layouts and resumable entry IDs while preserving operation identity, ownership and cancellation semantics.

#### 9.6 Synchronous interface policy

Host callers may use async or admitted sync SOSIX interfaces. A proxy can service a request using an async native provider or a blocking compatibility lane. Neither fact authorizes a GPU caller to block.

GPU code is limited to bounded immediate operations and asynchronous service requests. Functions with a transitive host-blocking effect are rejected in device code, including through aliases, closures and dynamic targets. A source-level sequential operation is allowed only when compiler lowering explicitly turns suspension into a continuation. Never silently redefine a POSIX-compatible `_sync` API to mean something asynchronous in device code.

`try_poll`, `try_take` and a fixed bounded local lookup are synchronous leaves, not the prohibited blocking sync API. A bounded status test is allowed; an unbounded loop around that test is not.

### 10. GPU transport and memory correctness

#### 10.1 Portable baseline

Use **ownership-transferred, fence-delimited batches** as the portable first implementation. Keep logical ring/admission semantics even when a physical native queue or buffer protocol differs. Ring-first does not mean identical lock-free shared memory on every device.

A typical epoch is:

```text
GPU produces request batch
 -> GPU completion and required memory visibility established
 -> host owns/reads batch, invalidating noncoherent mappings when required
 -> proxy admits service operations
 -> host produces result batch, flushing when required
 -> host submits/signals the next device phase
 -> GPU owns/consumes result batch
```

Use at least independently owned input/output regions; choose double/triple buffering from measured overlap and memory budgets. Vulkan barriers, semaphores, fences, queue ownership and host cache maintenance must match the actual resources. A generic CPU release fence is not a replacement for the graphics API synchronization contract.

Vulkan's memory model does not make overlapping host and device atomic operations mutually ordered merely because both are atomic. Host-coherent memory is not proof of a valid concurrent CPU/GPU lock-free ring. [E10](#e10) Therefore do not implement the universal Vulkan transport as ordinary CPU atomics racing shader atomics on one mapped header.

#### 10.2 Optional concurrent mapped transport

A live shared ring is an optimization that requires a backend-specific proof and capability record. For CUDA, qualify the exact memory allocation kind, atomic widths and operations, scopes, hardware attributes and topology against the current CUDA memory model. Mapped or unified memory alone is insufficient. [E11](#e11)

The record includes memory visibility, atomic interoperability, acquire/release protocol, producer/consumer ownership, notification mechanism, initialization/reset and cache-maintenance requirements. A provider unable to prove the complete protocol selects the portable batch transport or rejects a profile that forbids it.

For Metal, shared storage permits CPU/GPU access but still requires synchronization of access. Use command completion and shared-event/ownership mechanisms as supported by the deployment; do not infer a generic persistent host/device atomic ring from unified physical memory. [E12](#e12)

#### 10.3 Backend expectations

| Backend | Initial bridge | Later optimization | Claim explicitly excluded |
|---|---|---|---|
| CUDA | Stream/event-delimited batches and staged continuations | Qualified system-scope live ring; device graph/persistent task scheduling | Every pinned/managed allocation supports the same host-device atomic protocol |
| Vulkan | Host-visible batch buffers plus correct barriers/fences/timeline synchronization | Device-generated work and qualified backend-specific bridge enhancements | Shader invocation can call libc or host atomics are automatically interoperable |
| Metal | Command-buffer/shared-event handoff and finite task phases | Supported indirect work/resource-loading integrations | Shared storage itself makes simultaneous CPU/GPU mutation safe |
| SimpleOS native GPU | Driver-specific batch provider first | Dedicated hardware queues after explicit grants and isolation proof | A working compiler backend implies an available native GPU driver/vendor runtime |

This is the requested implementation direction, not a hardware availability statement. "CUDA on SimpleOS" needs a qualified execution/driver environment; the existence of CUDA code generation does not establish that environment.

#### 10.4 Wire schema and lifecycle

Reuse the existing canonical ring identity and GPU API manifest. The semantic envelope carries operation ID/version, record length, flags, operation token, capability reference, registered-buffer slice, deadline and response routing key. Service payloads use fixed-width fields and explicit serialization/alignment, never raw host pointers or compiler-native `Any` layout.

Do not freeze a universal entry size merely for convenience. Generate layout constants, target bindings and golden binary vectors from the chosen schema. Existing frozen GPU API fields and IDs are preserved; an additional transport-profile description is versioned rather than changing their meaning. The previously proposed `@sosix_api` contract remains the source of GPU legality metadata, not a second unrelated annotation family. [P2](#p2)

Native providers may produce multishot events, extra resource-release notifications or several completions for a composite request. Normalize these into the public stream/single-shot contract and internal retirement tracking. For streams, each `next` request is single-shot; the subscription lifetime is a separately owned resource.

Queue reset stops admission, prevents new device accesses, drains/quiesces or quarantines old resources, then publishes a new epoch. Bumping a generation alone does not stop DMA. Deadlines and cancellations cannot authorize freeing memory still visible to a device.

### 11. SimpleOS direct-device-queue architecture

The desired feature is **capability-granted GPU access to a qualified hardware queue**, not unrestricted device register access. CPU/SimpleOS control services still own discovery, setup, protection, resource registration, exceptional recovery and revocation. The steady-state data/control submission path may become device-initiated after admission.

```text
SimpleOS privileged control service
    -> authorize resource and operation class
    -> allocate/protect queue + register DMA buffers
    -> establish GPU-visible submission/completion/doorbell mechanism
    -> issue bounded queue capability

GPU logical tasks
    -> allowed native commands on granted queue
    -> qualified ordering / doorbell
    -> device completion
    -> canonical result + GPU continuation

SimpleOS remains responsible for revoke / quiesce / reset / accounting.
```

A hardware queue capability records device/queue identity, epoch, owner, admitted operation classes, resource scope, address translation/protection domain, buffer registrations, limits, priority, notification and reset authority. Native queue layout does not replace the SOSIX operation contract above it.

**Isolation must cover commands as well as addresses.** An address-translation boundary alone does not prove that a GPU cannot submit an unauthorized storage command, overwrite another namespace, manipulate another queue or ring a privileged doorbell. A driver must establish hardware-enforced command/resource isolation, or admit only a trusted verified queue producer within the relevant trust boundary. A capability checked once on the CPU is insufficient if untrusted device code can later forge native descriptors.

A direct file path also cannot bypass filesystem consistency. Native storage access requires an exclusively leased raw resource or a filesystem-managed extent lease with pinned mapping, access rights, cache/coherency rules and durability semantics. A pathname-to-LBA lookup performed once is not a safe filesystem API.

Start with one supported GPU/device/topology combination and a narrow queue/resource class, preferably an isolated test storage resource. Qualify descriptor visibility, doorbells, peer DMA, completion ordering, concurrent host access, cancellation, fault recovery and revocation. Until then, SimpleOS uses G1 and reports native direct-queue support as unavailable.

The companion feature-request document specifies twelve implementation-ready requests. They are backlog proposals, not issues already filed or claims of present hardware support.

### 12. Compiler, interpreter, JIT and loader integration

#### 12.1 One manifest and legality model

Extend the existing runtime symbol-provider and ABI machinery rather than adding a manually synchronized SOSIX registry. [R6](#r6) Generate source bindings, native external references, interpreter dispatch entries, loader requirements and GPU API summaries from a canonical schema or a canonical generated view of existing registries.

A manifest entry records logical API identity, service version, native symbol if applicable, signature/layout hash, execution domain, effects, feature requirements and compatibility aliases. Native symbols and GPU operation IDs are different kinds of binding; do not confuse them.

Compile-time checks validate transitive effects and domains, including indirect-call target sets. Required rules include:

| Diagnostic family | Rejected situation |
|---|---|
| Raw provider bypass | Product code reaches unauthorized `rt_*`, libc/OS or raw device entry points, including through aliases |
| Blocking in nonblocking domain | UI task, GPU task, ISR, completion callback or no-block profile calls a blocking path |
| No-GC/noalloc violation | Reachable GC dependency or disallowed allocation after admission |
| Lifetime violation | Borrowed buffer/frame/module can be released before outstanding work retires |
| Missing capability | Operation requires a service/right/feature absent from the composition |
| Unknown dynamic target | Required effect/domain safety cannot be established; reject in strict profiles |
| Invalid alias | Native signature, layout, error convention or semantics differ |

The current warning-level raw-runtime lint remains useful for quick scanning; it is not the final semantic proof. Existing warnings are baselined, new bypasses are denied, and migrated modules progressively become deny-clean. Existing `@runtime_intrinsics` exemptions must be validated against sanctioned ownership rather than becoming a universal escape hatch. [R7](#r7)

#### 12.2 Execution-lane behavior

The interpreter suspends its logical evaluation task and returns to the common executor while an operation is pending. It must not implement `await` by blocking on a Promise. JIT and AOT use task-frame lowering and the same service operation contracts. Backend-specific representation is allowed; differences in cancellation or resource ownership are not.

A minimal first migration can adapt existing Futures at the runtime boundary. Later lowering replaces internal frame representation without changing public service semantics. Keep the CPU reference execution path for correctness comparisons and environments without GPU providers.

At link/load, validate that required APIs, ABI versions, effects and backend capabilities are available. Missing required externs fail explicitly before use; they cannot become `nil`, zero, an empty string or a dummy success. Optional functions are explicitly optional and require a checked branch before invocation.

#### 12.3 Startup and shutdown

Use this dependency-ordered activation sequence:

```text
minimal trusted startup bridge
 -> allocator/backing-memory bootstrap
 -> core runtime and manifest resolver
 -> selected SOSIX providers
 -> executor/event-pump integration
 -> higher-level services and rendering
 -> application or compiler/interpreter entry task
```

The bootstrap bridge is deliberately small and statically available. Loading the SOSIX library must not itself require an already running SOSIX library loader. Native symbol loading and early memory operations remain sanctioned provider responsibilities.

Shutdown runs in reverse dependency order: stop new admission, close child scopes, request cancellation, drain results, establish resource retirement, unregister memory, quiesce/unload providers, then release the core. Partial startup failure uses the same ownership records for rollback.

A dynamically loaded provider or plugin cannot unload while a task frame, function pointer, callback, buffer-retirement record or GPU submission still depends on it. Module pinning and generation-aware handles prevent hot-reload use-after-unload. A timeout may quarantine a module/resource; it does not justify `dlclose` while code is still executing.

Compiler/loader cache keys include the binding schema, effect summaries, service/ABI versions and target-provider requirements. A change to these dependencies invalidates affected compiled artifacts; source text hashing alone is insufficient.

### 13. Minimal end-to-end vertical slices

Before large migration, implement small slices that prove the common contracts across execution modes.

**Slice A — file and timer.** A program acquires a read capability and registered buffer, begins two independent `read_at` operations and a deadline, awaits results, verifies bytes, closes the file and retires the buffer. Run through interpreter, JIT, native hosted and SimpleOS reference providers. Compare payloads and operation semantics, not identical completion ordering where ordering is intentionally unspecified.

**Slice B — rendering and input.** Open a surface, receive a keyboard/mouse batch, update a simple scene, submit a frame, await the correct lifecycle milestone, capture/read back when supported, resize, then close while work is in flight. One input path and one display capability serve CPU and GPU render lanes.

**Slice C — GPU-originated service.** CPU control pre-opens a read-only test resource and registers bounded GPU-visible buffers. A finite GPU task emits requests for selected offsets; the proxy performs SOSIX I/O; another finite task consumes results. Assert that request selection and continuation computation execute on the GPU, while proxy work is honestly reported as host service work.

**Slice D — direct queue experiment.** Replace only Slice C's admitted storage provider with a qualified SimpleOS device-initiated queue. Preserve the application contract and negative tests. Demonstrate the actual device submission origin and data path; a GDS transfer or host-issued queue submission does not satisfy this slice by itself.

### 14. Verification, observability and performance

#### 14.1 Mandatory invariants

Every admitted single-shot operation receives exactly one terminal result. No slot or resource is reused before safe retirement. No stale generation wakes a new task. No forbidden domain blocks. No admitted profile silently grows queues, allocates forbidden memory or falls back to a disallowed provider. No surface/input/device provider fabricates evidence of work it did not perform.

Use deterministic state-machine/model tests for reserve/commit/cancel/complete/reset races and randomized stress for concurrency. Fault injection includes completion-before-wait-registration, duplicate/stale completion, full response queues, partial transfers, deadline races, device loss, delayed DMA and provider unload attempts.

#### 14.2 Differential and platform testing

Compare new provider paths with stable reference behavior for data, errors, offset semantics and resource lifetime. Exact POSIX bindings receive small C-versus-Simple ABI conformance programs. Test both 32-bit and 64-bit target layouts where those targets are supported; unsupported rows are marked blocked rather than extrapolated.

Native graphics testing is independent of QEMU guest correctness. QEMU can prove the selected SimpleOS service and virtual-device behavior; it cannot prove a native Metal/Vulkan/CUDA transport or direct peer-DMA performance. The repository's existing rendering-host research makes the same evidence distinction. [R4](#r4)

#### 14.3 Measurement requirements

Measure direct libc versus SOSIX exact-binding call chains, startup latency, resident memory, per-operation allocation counts, submission/completion latency, p50/p95/p99 latency, throughput, CPU utilization, context switches, bytes copied, queue pressure, GPU occupancy/progress and frame/input latency.

Record cold startup separately from admitted steady state. Measure batch size and queue depth as independent variables. Compare zero instrumentation, bounded counters and detailed tracing; do not claim disabled instrumentation is free without checking generated code and memory behavior.

No universal speedup or overhead percentage is asserted here. The direct native alias gate is structural: no extra wrapper/dispatcher/Future/ring allocation in the admitted exact-ABI path. Async/proxy/typed adapters have real costs, which must be quantified for the actual workload.

For GPU requests, an illustrative latency decomposition is:

```text
T = request formation + publication/handoff + proxy admission
  + provider service + completion handoff + continuation scheduling
```

Batching amortizes fixed costs but may increase waiting latency. Select a bounded batching deadline and priority policy from measurement, not a fixed "always batch everything" rule.

A compact receipt records requested/actual provider, mapping grade, queue/resource generations, operation result, retirement state and fallback reason. Detailed tracing is optional; essential failure/accounting facts must remain observable without per-operation string formatting in the hot path.

### 15. Rollout decisions and rejected alternatives

The implementation plan is additive, evidence-gated and dependency ordered. First freeze manifests and conformance tests; then harden canonical operations; then add providers and migrate consumers. Do not switch an entire runtime to a new provider before a working vertical slice exists.

Rejected alternatives:

| Alternative | Why it is rejected |
|---|---|
| Rename all `rt_*` symbols to SOSIX | Confuses OS services with value/runtime intrinsics and hides semantic changes |
| Implement sync by always waiting on async | Adds avoidable overhead to exact POSIX calls and risks executor deadlock |
| Implement async by calling sync inline and returning a completed Future | Does not provide nonblocking service submission |
| One GPU-specific OS API with its own scheduler/ABI | Recreates the fragmentation this work is intended to remove |
| One concurrent mapped ring for every GPU backend | Assumes cross-domain memory/atomic guarantees not established by the portable APIs |
| Put renderer state and DrawIR semantics in SOSIX | Destroys the existing renderer/host boundary |
| GPU waits indefinitely for CPU completion | Risks occupancy/progress deadlock and wastes device execution resources |
| Expose arbitrary hardware queues after one CPU rights check | Does not prevent forged native commands or unsafe DMA |
| Promise equals GC or one heap object per I/O | Needlessly excludes the requested no-GC/mission profiles |

### 16. Decisions to resolve in the first implementation phase

The architectural direction is selected. The first implementation phase must resolve concrete engineering facts rather than invent them: which same-name exports/native bindings work in every current compiler lane; the exact installed ring/task APIs; ABI-schema generation ownership; the first native GPU/OS combination available for real testing; deployment-specific queue capacities and memory budgets; and the current inventory of remaining raw-runtime consumers.

None of these requires postponing the contract, state-machine tests, hosted provider work or renderer-host separation. Direct device queues remain an explicit later feature requiring its own security and hardware evidence.

**Final architecture:** one common execution contract, one no-GC asynchronous substrate, one SOSIX service authority boundary, exact native sync bindings where valid, and capability-qualified CPU/GPU providers beneath it.

---

<a id="implementation-plan"></a>
## Part II — Implementation plan

**Date:** 2026-09-05  
**Status:** proposed work packages; no repository changes or test passes are claimed.  
**Authority:** [design](#architecture), [source register](#sources), [SimpleOS queue requests](#simpleos-feature-requests).

### 1. Delivery strategy

Deliver additive, independently testable slices. The existing runtime remains usable while new consumers move behind SOSIX. Separate file moves and mechanical import changes from behavior changes. A compatibility shim is acceptable only when its semantic category, ownership and removal condition are recorded.

The first production milestone is **hosted CPU + interpreter/JIT/native parity + rendering host services + portable GPU proxy**. Native SimpleOS GPU-issued hardware queues are a separately qualified extension and must not hold ordinary runtime convergence hostage.

No calendar estimate is assigned: the actual source inventory, compiler binding support and available hardware determine effort. Work packages below have concrete dependencies and acceptance gates so multiple agents can work without changing one another's contracts.

#### 1.1 Dependency map

```text
WP-01 inventory / schemas / baselines
  |-- WP-04 exact POSIX bindings ----------------------+
  |-- WP-02 ring/lifetime/storage -- WP-03 async libs -+-- WP-05 execution lanes
  |                         |                        |          |
  |                         +-- WP-09 SimpleOS -------+          |
  |                                                             |
  +------------------ frozen service contracts -----------------+
                                      |                         |
                                   WP-06 rendering           WP-07 GPU bridge
                                                                |
                                                            WP-08 backends
                                                                |
                           WP-09 + hardware prerequisites -> WP-10 direct queues

WP-11 conformance/enforcement/performance starts with WP-01 and gates each slice.
WP-12 cleanup/release follows qualified milestones, not unimplemented optional features.
```

The graph expresses implementation prerequisites, not a requirement to wait for every file in a predecessor package. Agents can develop against frozen types and deterministic reference providers while native implementations are underway.

### 2. Work packages

#### WP-01 — Inventory, semantic classification and canonical metadata

**Owner pair:** runtime architecture + compiler/loader ABI.  
**Dependencies:** none.  
**Risk:** high leverage; moderate implementation complexity.

Inventory direct `rt_*`, native OS and renderer-host calls across compiler, interpreter, loader, libraries, tools, rendering and SimpleOS. Classify every migrated symbol as an exact native binding, a typed adapter, a high-level operation or a private runtime intrinsic. Record current signature, caller domain, native symbol, ownership, blocking/allocating behavior and compatibility consumers.

Inspect the actual current seed/self-hosted/native binding behavior. Reproduce the host-facade renaming-export limitation rather than assume either that it persists or that it is fixed. Confirm the exact common ring/task implementation and the runtime registry integration points. Preserve the existing registry and GPU operation IDs.

**Deliverables:** machine-readable migration ledger, binding schema, service-interface versions, conformance fixtures, baseline error/latency/allocation data, and one approved mapping for each priority operation.

**Acceptance:** every selected symbol has an explicit semantic category and owner; missing knowledge is marked unknown, not filled with a guessed alias. No duplicate IDs or signature-incompatible aliases pass validation. Baselines contain actual commands, commit/build identity and execution lane.

#### WP-02 — Canonical operation lifetime and no-GC storage

**Owner pair:** execution-runtime layer + lifetime/assurance feature.  
**Dependencies:** WP-01 contract freeze.

Use the existing common execution vocabulary and hosted/noalloc roots. Implement or complete bounded reserve/commit/release, generation-safe tokens, exact wakes, cancellation requests, terminal-result uniqueness and separate provider retirement. Add admission errors for capacity, unsupported features and invalid resources.

Provide explicit scope ownership for in-flight buffers, module pins and cancellation state. Add a fixed-size immediate result path that does not allocate on rejection. Define fair ready/completion/control processing and prevent lost wakes. Qualify static storage separately from a preallocated heap wrapper.

**Acceptance:** deterministic race/model tests pass; delayed completion after reset cannot affect a new slot; timeout cannot expose a live DMA buffer; full queues do not block control progress; no forbidden allocation or task-table scan occurs in the tested profile.

#### WP-03 — Future/Promise, scopes, streams and sync boundary

**Owner pair:** standard-library async layer + application ergonomics.  
**Dependencies:** WP-02 stable task/operation API.

Adapt existing Future implementations to canonical result observation. Add bounded combinators, parent cancellation, shared observation only with explicit storage, and asynchronous cleanup. Introduce async-first service naming without silently changing old synchronous APIs. Build typed byte/event streams with backpressure and caller-supplied buffers.

Implement an explicit outer runner and blocking-lane adapter. Reject nested executor blocking. Legacy Monoio/libuv/other mechanisms, when retained, act as providers rather than redefining the task model. A provider completion cannot synchronously reenter arbitrary user continuations.

**Acceptance:** no inline blocking in "async" calls; `race` and timeout do not leak or prematurely free losing operations; capacity-limited `all` respects its bound; producer overload reaches the caller; existing APIs work through documented compatibility adapters.

#### WP-04 — Exact native POSIX bindings and hosted providers

**Owner pair:** native ABI/platform layer + I/O semantics.  
**Dependencies:** WP-01; typed async provider integration also uses WP-02.

Start with a small signature-verified set such as read/pread/write, close and selected clock operations. Use native target C layouts. Add direct external-symbol mapping through the existing compiler/runtime registry, not a chain of renamed wrappers. Provide separate capability-typed adapters and explicit error capture.

Connect Linux asynchronous provider choices with capability probing and bounded fallback. Keep offsets, stream ordering, partial transfer behavior and thread-local error capture correct. Place blocking compatibility work off the executor. Do not promise libc-equivalent behavior for high-level text/process helpers.

**Acceptance:** C/Simple ABI comparison tests pass; disassembly/relocations show direct native references for exact aliases; no task/Future/ring allocation appears on that path; typed adapters reject invalid capabilities; read/pread cursor tests and interrupted/partial-I/O tests pass.

#### WP-05 — Compiler, interpreter, JIT and loader convergence

**Owner pair:** compiler/interpreter layer + ABI/lifetime feature.  
**Dependencies:** WP-01, WP-02, WP-03 and WP-04's binding interface.

Generate or unify external binding tables and operation requirements. Migrate compiler host I/O independently of its compilation target. Make interpreter await suspend its logical task; integrate native/JIT lowering with the same operation model. Add domain/effect summaries and strict missing-extern errors.

Implement staged provider activation, minimal trusted bootstrap, failed-startup rollback and module pinning through completion/retirement. Include schema/effect/provider identities in caches. Preserve old runtime symbols and their ABI while new code consumes SOSIX.

**Acceptance:** Slice A from the design behaves consistently across interpreter/JIT/native; host-versus-target cross-compilation tests pass; missing required bindings fail before invocation; no silent default result; unload with active work is blocked or safely deferred; the compiler can build its next stage without a provider dependency cycle.

#### WP-06 — Rendering host-service migration

**Owner pair:** UI/Engine2D layer + SOSIX display/input feature.  
**Dependencies:** common service contracts, WP-02, WP-03 and relevant hosted providers.

Adapt existing screen/host interfaces to SOSIX capabilities. Move environment selection to an immutable startup owner, timers to deadline services, and capture/QMP work to file/process/IPC services. Unify keyboard/mouse/text/focus ingress. Move surface lifecycle, presentation and readback behind typed operations while keeping renderer resource/algorithm ownership intact.

Replace the inspected DrawIR text-payload/immediate-drain production path with a packed, admitted submission path and independently observed completion. Retain text diagnostics and actual-versus-requested provenance without placing formatting on the normal fast path.

**Acceptance:** Slice B passes for the CPU reference and a real native render provider; resize/close races are safe; input overflow produces resynchronization; key/button releases are not silently lost; presentation acceptance is not mislabeled displayed; no raw host dependency remains outside sanctioned provider modules in the migrated closure.

#### WP-07 — GPU SOSIX subset, wire contract and proxy scheduler

**Owner pair:** GPU execution layer + service-security feature.  
**Dependencies:** WP-02, WP-05 metadata and frozen service contracts.

Implement existing GPU API metadata as a projection of canonical operations. Preserve API IDs, rights/capability separation and existing fallback profiles. Add versioned request/result schema generation, fuzzable ingress validation, per-tenant quotas, completion credits and fair host proxy service.

Implement finite-kernel continuation records first. The device checker rejects host-blocking paths transitively, including aliases and indirect calls. A legacy synchronous native service runs only in a bounded host blocking lane and remains asynchronous to the GPU requester.

**Acceptance:** malicious record fuzzing cannot reach an arbitrary host address/fd/function; stale generations and oversized buffers fail; device call graphs containing blocking APIs fail compilation/admission; Slice C runs with a deterministic reference transport; no lane spins waiting for host service.

#### WP-08 — CUDA, Vulkan and Metal transport qualification

**Owner pair:** backend-specific implementer + memory-model reviewer.  
**Dependencies:** WP-07; independent backend subpackages may run in parallel.

Implement ownership-transferred batch transport for each available backend, with documented fences/events/barriers/cache maintenance and resource-affinity rules. Integrate GPU work completion with canonical operations. Make unsupported host/device combinations explicit.

Optional concurrent mapped transports have their own capability probes, memory-model design review and stress tests. They do not replace the portable path until independently qualified. Record actual staging/direct-data mode and required-versus-actual fallback.

**Acceptance:** native hardware runs Slice C under stress; request/result visibility is correct across repeated ownership handoffs; queue saturation and device loss do not deadlock; a provider without a proved atomic protocol cannot select the live-ring mode; each PASS identifies real device/driver/backend details.

#### WP-09 — SimpleOS service/provider migration

**Owner pair:** SimpleOS kernel/service layer + canonical async feature.  
**Dependencies:** WP-01, WP-02; may develop parallel to hosted work.

Replace the local `io_rw.spl` immediate-work/request-slot and busy-wait paths with canonical admission and service completion. Route IRQ/notification completion into exact task wakeups. Correct error classification and verify actual serial/VFS effects. Preserve offset/ownership semantics instead of merely renaming APIs.

Implement the required display/input/time/file/process provider contracts on supported SimpleOS devices. Enforce no ISR allocation and bounded completion work. Do not import hosted runtime dependencies into the native noalloc path.

**Acceptance:** virtual/native SimpleOS tests cover zero length, partial transfer, pool exhaustion, concurrent offset access, cancellation and reset; serial writes require observed output; idle waits sleep/use notifications; the same conformance fixtures run against the SimpleOS provider.

#### WP-10 — SimpleOS device-initiated queue pilot

**Owner pair:** GPU/device-driver layer + protection/DMA-lifetime feature.  
**Dependencies:** WP-07, qualified WP-08 execution environment, WP-09 and FR-SOSIX-DQ prerequisites.

Select one concrete, controllable GPU/device/topology and an isolated resource. Implement queue grant, memory mapping, descriptor/doorbell ordering, completion routing, rate limits and revocation. Establish command/resource isolation in addition to address isolation. Raw storage or filesystem extent leases must prevent consistency violations.

**Acceptance:** all applicable direct-queue feature gates pass on actual hardware, including hostile-descriptor and delayed-DMA tests. Slice D proves GPU-issued native work. `DeviceInitiatedRequired` fails rather than substituting a CPU-issued proxy path. This package may remain experimental without blocking hosted runtime release.

#### WP-11 — Enforcement, conformance and performance qualification

**Owner pair:** test/CI layer + correctness/performance feature.  
**Dependencies:** begins with WP-01; accompanies all work packages.

Build shared conformance suites, binding/generation fixtures, fault injection and evidence collection. Ratchet existing raw-runtime warnings: block new violations immediately, then require deny-clean migrated closures. Add semantic alias/call-graph tests, not only filename/prefix checks.

Measure exact aliases, typed sync adapters, native async, compatibility pools, render batching, GPU proxy and direct queues separately. Keep cold/startup and admitted steady-state measurements separate. Report unsupported/blocked rows honestly.

**Acceptance:** correctness gates pass before optimization claims; benchmark evidence records configuration and actual provider; no silent regression is hidden by fallback or mock results; overhead budgets are approved from measured baselines rather than invented percentages.

#### WP-12 — Compatibility retirement and release

**Owner pair:** release/build layer + API migration feature.  
**Dependencies:** qualified milestones and their required WP-11 gates.

Remove old implementation duplication only after consumers and ABI manifests prove parity. Keep required old symbols forwarding in one direction until the documented support window ends. Remove broad provider exceptions from migrated directories. Update requirements, architecture, design, guides, examples and reverse references together.

**Acceptance:** full supported build/test closure passes, bootstrap lanes remain viable, compatibility fixtures load correctly, migration ledger has no unexplained forwarding cycles, and release notes distinguish completed providers from experimental/blocked features.

### 3. Path-level migration map

Paths marked **existing** were observed directly or identified by the inspected repository architecture. Proposed locations must be checked against current capsule/export conventions before creation. [R1–R7 in the source register]

| Location | Status | Action |
|---|---|---|
| `src/lib/common/contracts/execution` | Existing architecture owner | Reuse task/ring values; add only compatible extensions |
| `src/lib/common/contracts/sosix` | Proposed location | Platform-neutral service values/manifests; relocate if an existing canonical owner already exists |
| `src/lib/nogc_async_mut/async_ring` | Existing architecture owner | Canonical hosted bounded operation storage/provider integration |
| `src/lib/nogc_async_mut_noalloc/async` | Existing architecture owner | Qualify genuinely noalloc task/storage adapters |
| `src/lib/nogc_async_mut/sosix/host_facade.spl` | Existing inspected file | Migrate legacy host helpers through classified bindings/adapters |
| `src/lib/nogc_sync_mut/sosix` | Proposed location | Explicit typed sync surface and exact POSIX binding projection |
| `src/os/sosix/io_rw.spl` and related SOSIX modules | Existing inspected owner | Replace local request semantics and busy waits |
| `src/os/async`, `src/os/drivers` | Existing architecture owners | Native provider/IRQ/device integration |
| `src/lib/common/ui/screen_host.spl` | Existing in renderer research | Preserve facade role; delegate host operations to SOSIX |
| `src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl` | Existing inspected file | Split submission/completion; separate packed production payload from text evidence |
| `src/compiler/00.common`, `20.hir`, `50.mir` | Existing architecture owners | Effects, suspension/frame lowering and external binding metadata |
| `src/compiler/35.semantics/lint/raw_rt_access.spl` | Existing inspected file | Warning baseline plus semantic-enforcement migration |
| `src/compiler_rust/common/src/runtime_symbols.rs` | Existing inspected file | Preserve shared symbol/ABI ownership; generate compatible projections |
| Interpreter/JIT/loader binding call sites | Inventory required | Find via WP-01; do not guess filenames or create another registry |

### 4. Acceptance matrix

| Test group | Required evidence | Prevented failure |
|---|---|---|
| Binding/ABI | C reference, native relocation/disassembly, layout hashes | "Alias" actually changes types or adds a hidden runtime hop |
| Admission | Full pools, batch partial/all-or-fail tests, reserved control credits | Growth, overwrite or hidden flush on full queues |
| Lifetime | Cancel/result/reset permutations; delayed DMA; module unload attempts | Use-after-free, stale wake or callback into unloaded code |
| Task progress | Completion-before-registration, duplicate wake, saturated completion stream | Lost wake, busy loop or starvation |
| File semantics | read/pread cursor distinction, partial I/O, EOF, error transport | Incorrect offset behavior or fabricated successful bytes |
| Async library | Bounded all/race/timeout, cleanup failures, stream backpressure | Leaked losers, unbounded fanout or implicit reentrancy |
| Rendering/input | Resize/close/present races, focus/overflow/IME, real pixel/readback oracle | Stale surface access, stuck input or false display evidence |
| GPU proxy | Wire fuzzing, quotas, nonblocking domain checks, staged continuations | Arbitrary service access or CPU/GPU progress deadlock |
| Backend transport | Native memory-visibility stress with exact device/driver identity | Universal-mapped-ring assumption |
| SimpleOS direct queues | Command isolation, DMA bounds, revoke/reset, origin-of-submit evidence | Privilege/resource escape or false device-initiated claim |
| Compatibility | Old module load, bootstrap phases, cross-target compilation | A refactor that prevents the compiler building itself |
| Performance | Cold and steady-state data, allocations/copies/latency by provider | Unsupported "zero overhead" or GPU-only claims |

### 5. Parallel-agent and integration rules

Assign one schema owner for public operation IDs, manifests, profiles and ABI changes. Other agents implement provider/consumer projections against that contract. Each package has a layer expert and a feature reviewer; reviewers challenge cross-layer ownership rather than only local function behavior.

Use separate branches/worktrees per package. Commit pure moves/import rewrites separately from behavior changes. Each pull request states its contract dependency, affected execution lanes, migration-ledger changes, added tests, native evidence, fallback changes and rollback path. A provider cannot approve its own new authority exception without a boundary reviewer.

Run the full relevant compile closure initially to enumerate errors, rather than stopping after the first error where the compiler supports recovery. During fixes, rebuild changed/error-dependent units and rerun failing tests first; then rerun the complete affected suite. Before release, run the full required bootstrap/build/test matrix. A fast local green subset is not a substitute for full compatibility verification.

Rollback selects a previously qualified provider or compatibility facade at composition boundaries. Never mix old and new slot-generation or task-frame layouts inside an active queue. In-flight work must drain before a provider change; otherwise restart the composition safely.

### 6. Definition of done

The core unification milestone is complete when migrated compiler/interpreter/loader/application and rendering-host code no longer owns independent OS-service semantics; all required async paths use canonical admission/lifetime/wakes; exact native sync aliases pass ABI and code-generation tests; no-GC guarantees are measured at their stated boundary; and GPU proxy support is truthful about transport and CPU participation.

The direct-device-queue extension is complete only when its separately declared hardware/protection/lifetime requirements pass. Documents, wrappers, generated kernels or a mocked queue do not count as that evidence.

---

<a id="simpleos-feature-requests"></a>
## Part III — SimpleOS GPU-device-queue feature requests

**Date:** 2026-09-05  
**Status:** proposed backlog; these requests have not been filed as repository issues.  
**Parent:** [runtime design](#architecture), especially sections 9–12; [WP-10 implementation plan](#implementation-plan).  
**Principle:** host/SimpleOS setup and recovery remain permitted; qualified steady-state operations may be initiated directly by GPU tasks.

### Scope and qualification states

This extension provides a restricted native device-queue backend for existing SOSIX operations. It does not expose a generic privileged `ioctl`/MMIO interface or promise that CUDA, Vulkan or Metal automatically runs on SimpleOS.

Each device/backend combination is tracked as **Proposed**, **Reference-tested**, **Native-experimental**, **Qualified**, or **Unsupported/Blocked**. Reference tests are useful but do not constitute hardware qualification. A provider manifest names the exact GPU, target device, topology, native driver/backend, memory protocol and isolation assumptions.

The source design preserves G0/G1/G2 and existing `GpuIoPreference`/storage-tier vocabulary. Direct-data transfers and device-initiated control are different features. CPU-issued cuFile operations, for example, do not by themselves satisfy device-initiated control. [P2, E13 in the source register]

### FR-SOSIX-DQ-001 — Native execution and topology qualification

**Priority:** prerequisite. **Owner:** GPU platform/driver. **Dependencies:** none.

SimpleOS must discover and validate an actual execution path for the selected GPU and target device. Record GPU code execution support, queue-memory placement, permitted peer-DMA paths, doorbell reachability, completion visibility and relevant protection domains. Do not infer availability from a compiler target or device marketing capability.

**Acceptance:** a native test kernel executes and exchanges a bounded request/completion with an isolated test device/resource; unsupported combinations are rejected with a specific reason. Hosted emulation and QEMU evidence are labelled separately.

### FR-SOSIX-DQ-002 — Typed queue grants

**Priority:** prerequisite. **Owner:** SOSIX capability service + device driver. **Dependencies:** 001.

Create a typed queue-grant operation. A grant contains device/queue identity, owner and protection domain, epoch, allowed operation classes, resource scope, queue capacity, registered-buffer set, maximum transfer/in-flight limits, notification mechanism and permitted reset/revoke actions. The GPU receives only the restricted projection it needs.

**Acceptance:** grants cannot be forged, transferred or widened without authorization. Cross-owner, stale-epoch and wrong-operation-class attempts fail. Administrative queues and unrelated doorbells are not mapped by a data-queue grant.

### FR-SOSIX-DQ-003 — Command and address isolation

**Priority:** security gate. **Owner:** kernel protection + device-security reviewer. **Dependencies:** 001, 002.

Establish isolation for both DMA addresses and command semantics. Use supported hardware address/protection facilities where they actually enforce the relevant boundary. Separately prevent unauthorized opcodes, resource/namespace identifiers, queue control or device-administrative commands.

An address translation mechanism alone is not a command filter. When hardware cannot enforce the command/resource boundary, native queue access is limited to a trusted producer admitted under an explicit kernel-loader/code-integrity policy. Untrusted code must not be able to access or modify that producer's native queue descriptors or doorbell mapping. Otherwise retain G1 proxy validation.

**Acceptance:** negative tests attempt out-of-range DMA, another tenant's resource, unauthorized commands, descriptor modification and unauthorized doorbell writes. A build-time type check alone is not accepted as the protection boundary for arbitrary untrusted binaries.

### FR-SOSIX-DQ-004 — Registered GPU/DMA memory leases

**Priority:** prerequisite. **Owner:** memory manager + DMA driver. **Dependencies:** 001–003.

Support registration, pinning/mapping, accounting, direction-specific access and retirement of GPU-visible data and queue memory. Record allocation type, actual visibility/coherency properties, address translation and required cache maintenance. Registration fails when the requested profile's guarantees cannot be established.

**Acceptance:** overflows, stale registrations and invalid directions fail; buffers stay inaccessible to their previous mutable owner while leased; cancellation, process exit and GPU reset cannot free memory still used by DMA; quotas include pinned memory and metadata.

### FR-SOSIX-DQ-005 — Qualified descriptor and doorbell protocol

**Priority:** correctness gate. **Owner:** native device backend + memory-model reviewer. **Dependencies:** 004.

Define the exact producer/consumer protocol for each supported native queue: descriptor layout, ownership, capacity, publication ordering, doorbell operation, completion visibility, cache maintenance and epoch initialization. Integrate native requests with canonical SOSIX operation identities.

For storage, expose either an exclusively leased raw resource or filesystem-controlled extents with stable mappings and consistency rules. Do not translate a file capability into unrestricted raw LBAs. Filesystem caching, extent remapping and durability remain governed by the owning service.

**Acceptance:** long native visibility stress, wraparound, queue-full, concurrent access and malformed-descriptor tests pass. A reviewed protocol is tied to the actual backend, not assumed valid for every GPU/device pair.

### FR-SOSIX-DQ-006 — Completion and continuation integration

**Priority:** required. **Owner:** async runtime + interrupt/GPU scheduling. **Dependencies:** 005.

Route native completions into the canonical single-shot or stream contract and safe-retirement tracking. Support the qualified completion notification path: device-visible completion, interrupt-to-service notification, or an explicitly described hybrid. GPU continuation records use IDs and device layouts, not host function pointers.

**Acceptance:** duplicate or stale completion cannot awaken a new operation; completion-before-subscription is not lost; interrupts perform bounded work without allocation; waiting GPU tasks release execution resources or use a separately proven bounded resident-scheduler mechanism.

### FR-SOSIX-DQ-007 — Admission, budgets and fairness

**Priority:** required. **Owner:** scheduler/policy service. **Dependencies:** 002, 006.

Enforce in-flight operations, outstanding bytes, queue depth, continuation storage, completion credits and per-owner service budgets. Reserve capacity for cancellation, revocation and error reporting. A queue grant must not allow one GPU tenant to exhaust all device or proxy progress resources.

**Acceptance:** saturation never overwrites descriptors or grows an unapproved pool; another admitted owner still progresses under the configured policy; control/recovery remains possible when data queues are full; timeout and overload are reported rather than hidden by retries.

### FR-SOSIX-DQ-008 — Revocation, quiescence and reset

**Priority:** safety gate. **Owner:** lifecycle service + native driver. **Dependencies:** 004–007.

Implement stop-admission, producer quiescence, doorbell/mapping revocation, in-flight drain or abort, resource quarantine where necessary, and epoch replacement. A revoked grant cannot continue submitting through a stale device mapping. Generation increments reject stale software events but do not substitute for stopping actual DMA.

**Acceptance:** revoke while GPU work is active, delayed completion after reset, process death and hot-unplug/device-loss cases do not produce use-after-free. Failure to prove quiescence retains/quarantines memory and marks the device unavailable instead of reusing unsafe storage.

### FR-SOSIX-DQ-009 — Error, cancellation and durability semantics

**Priority:** required. **Owner:** SOSIX operation layer + storage/device semantics. **Dependencies:** 006, 008.

Translate device errors into typed SOSIX outcomes with partial-progress information when meaningful. Keep cancellation request, logical result, resource retirement and storage durability separate. Retrying a write after a timeout requires an operation-specific idempotency/recovery policy; it is not a generic runtime response.

**Acceptance:** cancellation races yield one logical terminal result; partial transfers are represented correctly; an acknowledged submission is not reported as durable storage; timeout never implies a committed write was undone; fault injection preserves the owning filesystem or raw-resource recovery contract.

### FR-SOSIX-DQ-010 — Capability negotiation and strict fallback

**Priority:** required. **Owner:** loader/composition + provider admission. **Dependencies:** 001–009.

Manifest negotiation declares staged, direct-data and device-initiated support independently, including operation subsets. Repeat checks at deployment against actual hardware/driver/resource state, not only at compile time.

`DeviceInitiatedRequired` fails when only a host proxy or CPU-issued direct-data path exists. `DirectPreferred` may select a permitted weaker mode with an explicit receipt. Changing providers for active work requires drain/retirement rather than silently reinterpreting in-flight tokens.

**Acceptance:** forced missing features and incompatible topologies produce a clear admission failure or explicitly permitted fallback; requested-versus-actual path is visible in tests and telemetry.

### FR-SOSIX-DQ-011 — Bounded diagnostics and provenance

**Priority:** required for experimental release. **Owner:** diagnostics + scheduler. **Dependencies:** 006, 010.

Record queue/resource epoch, owner, operation identity, requested/actual mode, submission origin, result and retirement state. Provide bounded trace storage and low-cost counters without mandatory per-command text formatting. Keep detailed data payloads out of ordinary telemetry.

**Acceptance:** evidence distinguishes GPU-issued native requests from CPU-issued proxy/direct-data requests. Diagnostic overload does not block device progress or allocate outside the profile. Failure reasons remain recoverable when detailed tracing is off.

### FR-SOSIX-DQ-012 — Native evidence and promotion gate

**Priority:** qualification gate. **Owner:** independent test/assurance. **Dependencies:** all applicable requests.

Promote each backend/resource combination only after native correctness, isolation, lifetime and progress suites pass. Measure p50/p99 latency, throughput, CPU participation, copies, queue occupancy and GPU progress against the same operation workload on the G1 reference path.

**Acceptance:** retained evidence includes repository revision, binary/schema/profile hashes, device/firmware/driver identifiers, topology, exact workload, results and limitations. Unsupported cases remain blocked. Synthetic queues, emulator results and theoretical performance estimates cannot qualify a native direct-device provider.

### First experimental milestone

Use a pre-authorized read-only resource, fixed registered buffers and a small bounded queue. A GPU task chooses read offsets, publishes actual native requests, consumes resulting data and continues computation. CPU/SimpleOS control handles setup and exceptional recovery but does not issue each operation on the GPU's behalf.

After this passes the security and retirement gates, add writes on an isolated disposable resource, then concurrency, revocation and recovery stress. Add network or other devices only with their own descriptor, isolation and resource semantics. No blanket "GPU can access all SOSIX hardware queues" capability is introduced.

---

<a id="sources"></a>
## Part IV — Sources and evidence limits

**Research date:** 2026-09-05.  
**Repository snapshot used for direct source inspection:** `320e6d99e4b8b8540a65078f68ce8ffca15fd2b6`.

The repository was read through the connected GitHub source. Earlier relevant design reports were retrieved from saved files. External technical claims use standards, official project/vendor documentation, or the original research paper. No compiler build, benchmark, hardware experiment or test suite was executed as part of authoring these documents.

A source file proves that the inspected implementation or comment exists at that snapshot; it does not prove all reachable paths work. An architecture/research document establishes a previous design decision, not completion. All work packages and feature requests in this deliverable are proposals.

### Repository evidence

<a id="r1"></a>
#### R1 — Hosted SOSIX facade

[Source: `src/lib/nogc_async_mut/sosix/host_facade.spl`](https://github.com/ormastes/simple/blob/320e6d99e4b8b8540a65078f68ce8ffca15fd2b6/src/lib/nogc_async_mut/sosix/host_facade.spl)

Full file inspected. Establishes the host-versus-SimpleOS distinction, inline pass-through policy, recorded renaming-re-export limitation, and examples of real value/behavior adapters. The seed failure is reported by the source comment; it was not independently rerun here.

<a id="r2"></a>
#### R2 — SimpleOS SOSIX read/write implementation

[Source: `src/os/sosix/io_rw.spl`](https://github.com/ormastes/simple/blob/320e6d99e4b8b8540a65078f68ce8ffca15fd2b6/src/os/sosix/io_rw.spl)

Full file inspected. Establishes inline VFS request/chunk work, local 128-slot request storage, busy-loop sync wrappers, the serial-write branch needing investigation, and request-allocation failure handling. This is evidence for specific migration/test targets, not a runtime reproduction of their effects.

<a id="r3"></a>
#### R3 — Canonical ring/task architecture

[Source: `doc/04_architecture/simple_ring_async_base.md`](https://github.com/ormastes/simple/blob/320e6d99e4b8b8540a65078f68ce8ffca15fd2b6/doc/04_architecture/simple_ring_async_base.md)

Inspected status, invariants, ownership/path map, value contracts, admission/lifetime, profiles, compiler boundary and OS/SOSIX/provider sections. The document explicitly distinguishes proposed architecture from implemented compiler/native-provider evidence. Later portions were not needed to establish the design used here.

<a id="r4"></a>
#### R4 — Existing rendering-host migration research

[Source: `doc/01_research/local/sosix_wm_renderer_host_interface.md`](https://github.com/ormastes/simple/blob/320e6d99e4b8b8540a65078f68ce8ffca15fd2b6/doc/01_research/local/sosix_wm_renderer_host_interface.md)

Full research document inspected. Dated 2026-08-11. Supports the host-service/renderer boundary, interface inventory, proposed migration order and native-versus-QEMU evidence distinction. Its list of other renderer files is historical research evidence, not a fresh line-by-line audit of every listed file.

<a id="r5"></a>
#### R5 — Observed DrawIR runtime queue adapter

[Source: `src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl`](https://github.com/ormastes/simple/blob/320e6d99e4b8b8540a65078f68ce8ffca15fd2b6/src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl)

Inspected through the requested first 200 lines, including the adapter implementation and exports. Establishes SDN/text payload creation, submission followed by immediate drain/dispatch in this path, and existing requested-versus-actual provenance reporting.

<a id="r6"></a>
#### R6 — Existing runtime symbol and ABI registry

[Source: `src/compiler_rust/common/src/runtime_symbols.rs`](https://github.com/ormastes/simple/blob/320e6d99e4b8b8540a65078f68ce8ffca15fd2b6/src/compiler_rust/common/src/runtime_symbols.rs)

Lines 1–175 inspected. Establishes ABI version checks, `RuntimeSymbolProvider`, runtime tiers/classification and the beginning of the CoreRequired symbol set. This inspection does not claim every later symbol or every consumer was audited.

<a id="r7"></a>
#### R7 — Raw-runtime access lint

[Source: `src/compiler/35.semantics/lint/raw_rt_access.spl`](https://github.com/ormastes/simple/blob/320e6d99e4b8b8540a65078f68ce8ffca15fd2b6/src/compiler/35.semantics/lint/raw_rt_access.spl)

Lines 1–180 inspected. Establishes warning-level/text-heuristic scope, provider allowlisting, runtime-intrinsic marker handling and cautious replacement hints. It does not prove whole-program call-graph enforcement.

### Previously saved reports

<a id="p1"></a>
#### P1 — `simple_ring_async_architecture.md`

Retrieved from the user's saved file Library. Used for earlier decisions on one task ABI, shared rings, explicit blocking compatibility, specialized executors, and mission allocation modes. Relevant host/OS migration and task-ABI sections were retrieved. The report is contextual design evidence, not a newly executed status audit.

<a id="p2"></a>
#### P2 — `simple_sosix_gpu_api_extension_final_report.md`

Retrieved from the user's saved file Library. Used for G0/G1/G2 service tiers, restricted device API, frozen `@sosix_api` schema/flags, existing operation IDs, rights versus deployment capabilities, backend manifest and existing fallback/profile vocabulary. Those contracts are preserved instead of silently replaced.

<a id="p3"></a>
#### P3 — `simple_gpu_scheduler_sosix_resident_rendering_design_2026-09-05.md`

Retrieved from the user's saved file Library. Used for coarse renderer/SOSIX services, GPU logical suspension, exact-alias restrictions, and the distinction between portable ownership-transferred batches and optional qualified live mapped rings. Its repository snapshot differs from the pinned snapshot inspected for this deliverable.

### External primary sources

<a id="e1"></a>
#### E1 — ECMAScript 2025 Promise model

[ECMAScript 2025: Control Abstraction Objects](https://tc39.es/ecma262/2025/multipage/control-abstraction-objects.html)

Reference for Promise state/reactions and composition. Simple's proposed no-GC ownership and fairness rules are design adaptations, not claims of exact ECMAScript runtime compatibility.

<a id="e2"></a>
#### E2 — Node.js filesystem promises

[Official Node.js filesystem API](https://nodejs.org/api/fs.html)

Reference for promise/callback/synchronous API separation and the explicit statement that filesystem Promise APIs use the underlying thread pool. This source is not used to claim a particular Simple provider implementation.

<a id="e3"></a>
#### E3 — libuv architecture

[Official libuv design overview](https://docs.libuv.org/en/v1.x/design.html)

Reference for event-loop/readiness and worker-pool separation. Adopting libuv as a dependency is not required or selected by this plan.

<a id="e4"></a>
#### E4 — Deno API naming

[Official Deno API reference](https://docs.deno.com/api/deno/)

Reference for async APIs with explicit synchronous counterparts, including file operations. This is an ergonomic precedent, not a native ownership design.

<a id="e5"></a>
#### E5 — Streams and caller-supplied buffers

[WHATWG Streams Standard](https://streams.spec.whatwg.org/)

Reference for stream backpressure, reader/writer ownership and BYOB byte readers. Simple's hard admission caps and registered-buffer rules are stronger, explicitly proposed constraints rather than a claim that web-stream high-water marks enforce fixed memory bounds.

<a id="e6"></a>
#### E6 — Cancellation signaling

[WHATWG DOM: Aborting ongoing activities](https://dom.spec.whatwg.org/#aborting-ongoing-activities)

Reference for AbortController/AbortSignal being separate from built-in Promise semantics. Native DMA retirement and cancellation safety are additional Simple requirements.

<a id="e7"></a>
#### E7 — Structured resource scope

[Effect: Scope](https://effect.website/docs/v3/resource-management/scope)

Reference for scope-bounded resources and finalization. This cited page is the explicitly versioned v3 documentation; the plan does not depend on it being the newest Effect release or require running Effect in Simple.

<a id="e8"></a>
#### E8 — POSIX `read` and `pread`

[The Open Group: read/pread](https://pubs.opengroup.org/onlinepubs/9799919799/functions/read.html)

Reference for the distinction between shared-offset reads and explicit-position reads. The authoritative page's indexed text was available; a subsequent direct open returned an error. No unsupported platform-specific behavior is inferred from that retrieval failure.

<a id="e9"></a>
#### E9 — Linux io_uring interface

[Linux man-pages project: io_uring(7)](https://man7.org/linux/man-pages/man7/io_uring.7.html)

Reference for submission/completion queues and completion-carried result/error information. The design deliberately normalizes native provider details rather than equating every native completion one-to-one with a public single-shot result.

<a id="e10"></a>
#### E10 — Vulkan host/device memory model

[Khronos Vulkan specification: Memory Model](https://docs.vulkan.org/spec/latest/appendices/memorymodel.html)

Reference for the lack of mutual ordering between overlapping host and device atomic operations absent the required synchronization. The proposed portable batch transport follows from this constraint; it is not a claim that no specialized platform can ever support a stronger bridge.

<a id="e11"></a>
#### E11 — CUDA system-scope atomic requirements

[NVIDIA CUDA Programming Guide: CUDA C++ Memory Model](https://docs.nvidia.com/cuda/cuda-programming-guide/05-appendices/cuda-cpp-memory-model.html)

Reference for memory-kind, scope and hardware-property conditions, including managed/mapped/system allocations and atomic-operation distinctions. The design requires complete backend qualification instead of applying one attribute to every allocation or atomic width.

<a id="e12"></a>
#### E12 — Metal CPU/GPU synchronization

[Apple: Synchronizing CPU and GPU work](https://developer.apple.com/documentation/metal/synchronizing-cpu-and-gpu-work)  
[Apple: Shared storage mode](https://developer.apple.com/documentation/metal/mtlstoragemode/shared)

References for synchronized CPU/GPU resource access. Apple's documentation is partly dynamically rendered; no exact code recipe or unverified cross-domain atomic guarantee is claimed from it.

<a id="e13"></a>
#### E13 — GPUDirect Storage control versus data path

[NVIDIA: GPUDirect Storage Overview Guide](https://docs.nvidia.com/gpudirect-storage/overview-guide/index.html)

The Functional Overview states that the documented cuFile APIs are issued from the CPU. The guide also describes direct data paths and compatibility/staging behavior. These distinctions support separate direct-data and device-initiated capability requirements.

<a id="e14"></a>
#### E14 — GPU-initiated storage research

[Original BaM paper, HTML: GPU-Initiated On-Demand High-Throughput Storage Access in the BaM System Architecture](https://arxiv.org/html/2203.04910v3)

Original research precedent for GPU-initiated storage. No paper-specific speedup is transferred to Simple, and the paper does not establish SimpleOS driver, isolation or hardware support.
