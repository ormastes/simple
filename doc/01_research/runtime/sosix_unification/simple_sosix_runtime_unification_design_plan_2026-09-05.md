<!-- Saved verbatim 2026-09-05 from external research. Repo verification and stale-claim list: README_tldr.md in this directory. -->

# Simple runtime unification through SOSIX

## Research, architecture, migration design, and implementation plan

**Date:** 2026-09-05  
**Repository:** `ormastes/simple`  
**Inspected revision:** `27f1973cc1548fa7cfd0994032d6186f77bcf593`  
**Status:** Proposed design. Selected source files and existing plans were inspected; no compiler build, runtime conformance test, hardware benchmark, or repository modification is claimed.  
**Companion:** [SimpleOS GPU/device-queue feature requests](simple_os_gpu_queue_feature_requests_2026-09-05.md).

## Executive decision

Unify **the operating-environment contract**, not every implementation, into SOSIX. Simple applications, the compiler, interpreter, loader, rendering stack, and SimpleOS should share the same service contracts, operation semantics, capabilities, and provider discovery. They must not acquire a second scheduler, Future ABI, ring ABI, renderer, or loader in the process.

The proposed composition is:

```text
Simple application / compiler / interpreter / loader / UI
                      |
             SOSIX service contracts
               /                  \
      async-first API          explicit sync API
             |                    |          \
 canonical task + SimpleRing      |     POSIX-compatible raw view
             |                    |          |
 platform/service provider <------+     native libc symbol
             |
       OS / driver / GPU
```

On a native POSIX host, an exact synchronous alias resolves directly to the libc function; it does **not** visit the ring or an `rt_*` forwarding function. An asynchronous call uses an appropriate completion/readiness provider and the canonical task contract. SimpleOS implements the same service contracts with its own service/driver providers. GPU code sees an explicitly restricted projection of SOSIX, normally asynchronous and host-proxied.

### Decisions to adopt

| ID | Decision |
|---|---|
| D01 | SOSIX is the sole portable host-service boundary. Platform functions and legacy `rt_*` OS entry points are implementation or compatibility details, not application imports. |
| D02 | Latency-bearing services are asynchronous by default. Proven synchronous leaves remain direct; not every function returns a Future. |
| D03 | The base is no-GC. General no-GC, bounded-pool, and truly no-allocation profiles remain distinct. |
| D04 | Preserve `SimpleRing<Op,Cpl>` and `poll(frame, context) -> Ready(result) / Pending(wait_token)` as the existing canonical contracts. |
| D05 | Preserve exact POSIX semantics in a raw synchronous projection; offer capability-safe typed services separately. Only exact matches qualify as aliases. |
| D06 | Merge rendering **host access** into SOSIX; retain DrawIR, Engine2D, layout, rasterization, and GPU resource algorithms with their current owners. |
| D07 | Reuse the existing SOSIX-G operation IDs and checked API metadata. GPU implementations are backend-qualified providers, not unrestricted POSIX in shaders. |
| D08 | Separate admission, logical completion, and physical retirement. Cancellation or timeout alone never authorizes buffer reuse, DMA unmapping, or provider unloading. |
| D09 | Preserve compiler-driver and loader public boundaries during migration. Host-platform selection must not constrain the compiler's target platforms. |
| D10 | Add SimpleOS direct GPU/device queues as an experimental, explicitly authorized capability, not a baseline promise for CUDA, Vulkan, or Metal. |
| D11 | Generate bindings, legality metadata, compatibility routes, and conformance inventories from one authoritative SOSIX operation registry. |
| D12 | Claim zero wrapper cost, nonblocking behavior, device execution, or direct I/O only with the corresponding artifact/runtime evidence. |

### Coverage of the requested work

| Request | Resolution | Main sections |
|---|---|---|
| Async Future/Promise first; sync second; no-GC | One nonblocking operation model, owned task storage, explicit sync views | 3–6 |
| Direct POSIX calls through aliases, without direct `rt_*` | Exact symbol aliases plus a separate safe adapter class | 5, 15 |
| Renderer host interface merged into SOSIX, including GPU and input | Display/input/time/configuration/library services; existing GPU submit owner retained | 8–9 |
| Sync SOSIX mostly POSIX-compatible | Raw POSIX projection preserves ABI/errno; typed projection deliberately differs | 5 |
| Learn from JS/TS libraries | Promise ergonomics, paired sync APIs, structured task lifetime, cancellation, bounded streams | 6 |
| CUDA/Vulkan/Metal access through a host proxy; avoid device blocking | Shared SOSIX-G semantics, transport-specific continuation models | 10–12 |
| SimpleOS direct device hardware queues from GPU | Gated feature backlog with isolation, queue leases, reset, and evidence requirements | 13 and companion |

---

## 1. Repository baseline and integration gaps

This is a targeted source review, not a repository-wide completion audit. A checked-in plan establishes intended ownership, not native execution. Historical bug reports are labeled as such rather than presented as freshly reproduced failures.

| Inspected evidence | What it establishes | Required treatment |
|---|---|---|
| `src/lib/nogc_async_mut/sosix/host_facade.spl` [R01] | The hosted façade explicitly distinguishes itself from SimpleOS-internal `src/os/sosix`; it contains process/environment forwarding and real adapter bodies. | Extract shared service contracts; keep hosted and SimpleOS implementations behind them. An `async` directory name is not evidence that each function suspends. |
| Renaming re-export bug report, filed 2026-09-03 [R02] | The report records `export use m.orig as aliased` being accepted but not bound in the tested seed. Four façade functions use inline forwarding instead. | Repair and test alias resolution before claiming structural zero-wrapper cost. Do not describe this report as a new reproduction. |
| `src/os/sosix/core/operation.spl` [R03] | Existing slot/generation identity, progress, cancellation, timeout, and release transitions are available. The inspected owner does not itself model hardware retirement. | Adapt to canonical ring identity and add/enforce retirement ownership at the integrating owner. This observation does not by itself prove an existing use-after-free. |
| `src/os/sosix/fs/operation_adapter.spl` [R04] | Positioned operations already have IDs `0x0101` and `0x0102`, capability and buffer references, offsets, lengths, and deadlines. Zero-length transfers are rejected by this descriptor constructor. | Preserve operation IDs. Define public zero-length behavior separately, and distinguish descriptor validation from authority/buffer-bound validation. |
| Ring/async architecture [R05] | The common task/ring vocabulary and ownership are frozen. It explicitly limits current evidence to a bounded pure-Simple reference in that lane. | Reuse the contracts; track compiler lowering and native-provider acceptance separately. |
| SOSIX renderer host-interface research [R06] | The existing boundary already assigns display/input/time/file/process/library access to SOSIX while retaining renderer semantics. | Complete this migration rather than create a parallel host interface. |
| `SimpleCompilerDriverV1` source [R07] | A coarse fixed-width driver descriptor and handle-based boundary already exist. | Keep the outer ABI; inject SOSIX services inside the implementation. |
| SMF module-loader source [R08] | Lazy service ownership, compiler SFFI, executable-memory helpers, and generation/lifecycle integration already exist. | Route OS memory/library/file operations through SOSIX while preserving lazy loading and loader semantics. |
| Interpreter extern registry and SFFI generator spec [R09][R10] | Legacy `rt_*` bindings and a generator seam already exist. The file-I/O spec includes allocating whole-file/text APIs, not merely libc-compatible calls. | Reuse generation infrastructure. Do not mechanically rename high-level `rt_file_read_text` into POSIX `read`. |

### Reconcile prior reports

The saved ring/async plan, SOSIX-G plan, compiler kernel/plugin plan, and September 5 GPU rendering plan were retrieved and used as prior design inputs [L01–L04]. They remain proposals or dated evidence where not corroborated by current source.

This document preserves their architectural choices: one task/ring model, typed capabilities, optional GPU-resident scenes, generation-pinned providers, and lazy startup. It does not silently promote the earlier implicit-await proposal, GPU checker proposal, or full scene offload proposal to implemented status.

---

## 2. Ownership and layering

### 2.1 What SOSIX owns

SOSIX owns service semantics, capability checks, operation identities, admission/cancellation/deadline contracts, service discovery, and the portable boundary for external effects. It selects or reaches providers for files, networking, processes, clocks, virtual memory, libraries, display, input, device access, and GPU-facing host services.

It does **not** own string representation, language object layout, arithmetic lowering, AST/HIR/MIR, renderer algorithms, shader compilation, or the internal GPU memory-leveling policy. Those components may request memory or I/O through SOSIX but retain their semantic ownership.

### 2.2 Proposed module placement

Existing roots are retained. New roots below are proposals, to be confirmed by the repository's MDSOC/module ownership checks before creation.

| Owner/root | Responsibility | Dependency restrictions |
|---|---|---|
| Existing `src/lib/common/contracts/execution` | Canonical ring/task values and versions | No OS, allocator, compiler-private, or vendor descriptors |
| Proposed `src/lib/common/contracts/sosix` | Service IDs, operation signatures, rights, portable error vocabulary, service-query contracts | Dependency-light values; imports canonical execution contracts, never copies them |
| Existing `src/lib/nogc_async_mut/sosix` | Default ergonomic async façade and hosted composition seam | No new executor or duplicate operation table |
| Proposed `src/lib/nogc_sync_mut/sosix` | Explicit typed sync façade and raw POSIX-compatible projection | Blocking effects visible to compiler/profile checks |
| Existing `src/lib/nogc_async_mut/async_ring` | Hosted storage and canonical ring adapters | No platform semantics in public contract |
| Existing `src/lib/nogc_async_mut_noalloc/async` | Static/pool execution and storage integration | Must not pull in a heap-growing hosted implementation |
| Proposed hosted provider capsules | libc, Linux completion/readiness, Windows, Darwin/BSD, browser providers | Platform-private ABI and scheduling integration remain inside provider |
| Existing `src/os/sosix`, `src/os/async` | SimpleOS capability/policy and native provider adapters | Consume common contracts; no second Future ABI |
| Existing `src/os/drivers` | Hardware queue ownership, interrupts, DMA and reset | No application task-frame manipulation |
| Compiler / interpreter / loader | Language semantics and execution, using granted SOSIX services | No portable direct OS extern imports after migration |
| Engine2D / rendering providers | Rendering and native GPU queue execution | SOSIX for host interaction; no per-primitive OS requests |

A shared contract must not import `os.kernel.errno` or raw SimpleOS syscalls. Conversely, pulling the entire hosted runtime into SimpleOS is not unification.

### 2.3 Composition rather than a monolithic runtime

A runtime instance consists of a contract-compatible service table, an executor policy, storage policy, admitted providers, and an authority set. Multiple isolated instances may exist in one process. They share implementation code where safe, not a mandatory process-global mutable handle table.

Static composition resolves known providers without runtime lookup. Dynamic composition validates and caches an operation table once per admitted provider generation. Cross-process and GPU transports marshal typed requests; in-process native aliases do not.

Do not confuse three axes:

```text
host platform: where the compiler/interpreter process runs
compilation target: where generated code will run
execution domain: host CPU / device GPU / SimpleOS service / sandbox
```

A Linux-hosted compiler targeting Windows, SimpleOS, or GPU code still uses the Linux SOSIX provider for its own files and processes. It emits the target's imports and requirements for the compiled program.

---

## 3. Async-first and no-GC semantics

### 3.1 Default API policy

Potentially deferred operations default to asynchronous results: file and socket transfer, process wait, timers, display presentation/readback, GPU execution, asynchronous device transfer, and service RPC.

Cheap local observations remain synchronous: reading an immutable configuration snapshot, checking a completed operation, consuming an already available local event with `try_take`, validated handle comparison, and reading an appropriate local clock. Creating an object may be synchronous when entirely local; opening a resource or initializing a backend may require deferred work.

The rule is **do not block an executor**, not **wrap every operation in a Promise**.

### 3.2 Future and Promise are two sides of one operation

Use existing language/library names; the following describes required semantics rather than a new concrete syntax:

```text
Future<Result<T, SosixError>>
    consumer view: await / nonblocking poll / cancellation request

Promise<Result<T, SosixError>>
    completion authority: settle exactly once through the operation owner

AsyncTaskFrame
    compiler/interpreter continuation owned by an executor

RingToken
    identity of committed provider work and its exact wake target
```

A Future does not require a heap object or tracing GC. It can reference a frame/result slot in owned, pinned, or static storage. A Promise is not an untrusted public ability to complete arbitrary operations. Completion authority belongs to the provider adapter that owns the token.

The default consumer is affine: move or consume it once. Shared-result behavior is explicit and requires an ownership strategy appropriate to the profile. Host reference counting may be an implementation option; cyclic ownership is not silently made safe by calling the API no-GC.

### 3.3 Define when work begins

A successful low-level `reserve -> commit` starts a hot I/O operation: the provider may run it without the caller awaiting it. A failed reservation neither starts work nor creates a completion obligation.

A higher-level async function may build a lazy task frame until scheduled, following the language's existing semantics. Its contained I/O starts only when that frame commits it. Document this distinction; never allow different providers to disagree about whether the same operation is submitted twice or waits for a second poll.

Ordinary async façades may suspend while waiting for admission credits, but only through a bounded, admitted waiter. Low-level `try_submit` always returns `Full`/`Unavailable` rather than allocating an unbounded waiting list. Mission profiles may reject instead of waiting.

### 3.4 Source ergonomics and compiler scope

Keep explicit async/await working first. The earlier expected-type-driven implicit-await design may be layered on later, gated by actual parser/type/effect/lowering support [L01][R05]. Runtime unification does not depend on inventing new grammar.

Conceptual example—API names and ownership notation below are proposed:

```simple
# Default service view: deferred I/O.
val pending = sosix.fs.read_at(file, owned_buffer, offset)
val outcome = await pending

# Explicit synchronous capability-safe view.
val outcome = sosix.sync.fs.read_at(file, borrowed_buffer, offset)

# Raw POSIX-compatible view: exact fd/pointer/count/errno semantics.
val count = sosix.posix.pread(fd, raw_ptr, count, offset)
```

A function's effect summary distinguishes `may_suspend`, `may_block`, allocation domain, required service rights, and execution domain. An asynchronous return type alone does not prove nonblocking implementation.

### 3.5 Allocation profiles

| Profile | Task/operation storage | Runtime allocation | Blocking policy |
|---|---|---|---|
| General no-GC | Owned frames, arenas or explicit heap allocations | Allowed under ownership/accounting policy | Only explicit blocking boundary or worker |
| `mission_alloc` | Bounded/admitted ownership domains | Allowed only where the profile admits it | No executor or interrupt blocking |
| `mission_pool` | Preallocated frames, registered buffers, bounded queues | No growth after Ready | Deterministic/bounded waits and overload policy |
| True no-allocation composition | Statically provisioned storage throughout its declared scope | None in that scope | Explicitly qualified services only |
| GC-enabled application | GC may manage application objects | GC stays outside the SOSIX no-GC core | Same executor nonblocking rules |

A `mission_pool` label must not conceal allocations in adapters, completion callbacks, error strings, or spill queues. Vendor drivers and host libraries may allocate internally; report that separately instead of claiming the entire platform is allocation-free. Vulkan explicitly exposes host allocation concepts, which reinforces the need to distinguish application and driver scopes [E15].

Core hot-path errors use compact enums/codes and bounded diagnostic records. Formatting text and exporting diagnostics are optional outer operations. Static/pool memory sizing should reuse the existing command/DI allocation-plan work rather than create a second allocator planner.

---

## 4. One operation lifecycle, with safe retirement

### 4.1 Canonical state ownership

Use the canonical ring owner to decide admission and completion. Map existing `SosixOperationId` slots to its identities through a checked adapter; do not run two independent completion state machines that can disagree.

```text
Unreserved
  -> Reserved
       -> ReleasedBeforeCommit
       -> Committed
            -> provider execution
            -> one logical terminal result
            -> physical retirement confirmed
            -> payload/slot/provider-generation released
```

Physical retirement can precede or coincide with logical completion. The important rule is that reuse requires both the relevant consumer ownership transition and a provider retirement guarantee. A timeout may produce a logical outcome first, while provider work still owns resources.

The current SOSIX operation source immediately records canceled/timed-out states and permits terminal-slot release; it also restarts wrapped generations at one [R03]. Integrators must prove that an outer owner already enforces the stronger rules, or amend that owner. A state-machine helper alone is not proof that device access has stopped.

### 4.2 Cancellation contract

Distinguish:

| Event | Meaning |
|---|---|
| Reservation released | Provider never saw the work; no terminal CQE is owed |
| Cancellation requested | A request was sent; side effects may still occur |
| Operation canceled before effect | Provider confirms the operation stopped with the declared side-effect status |
| Operation completed despite cancellation | Successful/failed completion won the race |
| Consumer deadline elapsed | The consumer no longer wishes to wait; not a rollback guarantee |
| Physical retirement | Provider, DMA engine, and device can no longer access the leased resources |

A cancel request can have its own receipt; that is not a second terminal completion of the original request. Maintain one terminal outcome for each committed single-shot operation. Streaming/multishot operations explicitly permit intermediate events and one final termination.

Dropping a Future must not release an in-flight buffer. An explicit owner/supervisor retains the operation until cleanup. Mission profiles disallow uncontrolled detached cleanup: reserve cleanup capacity during admission.

For a safe borrowed-buffer API, the language borrow must remain live until retirement. An early timeout cannot return mutable access to that buffer. Prefer owned/registered buffer leases when early consumer deadlines are required; provide a separate retirement/join operation before handing ownership back.

### 4.3 Resource and generation invariants

Every request is tied to instance/ring identity, slot, generation, resource rights, provider generation, and registered-buffer range. Preserve the existing wire representation where it already encodes these facts. Do not add an incompatible universal descriptor to replace typed rings.

Generation exhaustion fails closed: retire the identity or advance a separately qualified epoch after full quiescence. Do not wrap into a token value that an old request could still carry. A stale completion must never wake a reused task.

Admission reserves enough result/retirement capacity for accepted work. Keep a dedicated bounded cancellation/reset/control path so that a full data SQ cannot prevent recovery. One mutable owner per shard/ring is the default; GPU lane aggregation may use provider-private multi-producer mechanisms before publishing a bounded batch.

### 4.4 Memory visibility

A provider protocol specifies publication, observation, payload visibility, completion visibility, and retirement—not only head/tail atomics. CPU release/acquire operations do not automatically establish GPU or device visibility. Each provider must prove the required cache maintenance, native barriers/events, and DMA ordering for its transport [E10][E11][E14].

---

## 5. Synchronous SOSIX and direct POSIX aliases

### 5.1 Three distinct classes

| Class | Contract | Implementation on native POSIX | Wrapper claim |
|---|---|---|---|
| Raw POSIX-compatible alias | Same ABI, pointers, counts, flags, error behavior, ownership, and effects | Resolve directly to target libc symbol | Structurally no SOSIX/`rt_*` wrapper |
| Typed safe SOSIX operation | Capability handles, bounded buffer leases, typed errors | Validate/adapt, then native call or selected provider | Real adapter; inline only what is semantically redundant |
| High-level convenience operation | Whole-file text, decoding, aggregate results, retries | Compose lower-level SOSIX operations | Not a POSIX alias |

The user-facing objective is supported: callers use SOSIX vocabulary while eligible calls link directly to POSIX functions. It does **not** require pretending a capability object has the ABI of an integer file descriptor or that `Result<T,E>` is an `ssize_t`.

### 5.2 Exact-alias candidates

`read`, `write`, `pread`, `pwrite`, `close`, and other libc interfaces can be exposed under a raw SOSIX POSIX view when signatures and semantics match the selected host ABI. Target definitions for `size_t`, `ssize_t`, `off_t`, structures, calling convention, and constants must come from a verified platform binding, not assume LP64 everywhere.

Variadic functions and macros require special care. A fixed-arity safe `open` helper is an adapter, not automatically the variadic libc symbol. A macro-only facility cannot be treated as an exported ELF symbol. Pointer-returning or thread-local facilities need their actual ABI handling.

A source import alias is not necessarily a linker-created alternate exported symbol. The former is sufficient for zero-wrapper internal calls. Exporting an alternate symbol from a library is a separate ABI requirement and must be tested as such.

### 5.3 Fix the alias mechanism before removing forwarders

The recorded resolver gap [R02] is a first-class compiler task. Desired behavior:

```simple
# Target syntax after alias-resolution conformance passes.
export use platform.posix.pread as sosix_pread
```

Both names resolve to the same canonical declaration and effect/extern metadata. There is no generated wrapper function. The test must cover ordinary imports, public re-exports, chained aliases, overload/signature identity, visibility, interpreter resolution, native code generation, and SMF serialization/reload.

Until this passes, retain named compatibility forwarders and mark the zero-wrapper goal as unproven. `@always_inline` is an optimization request, not the structural guarantee requested here. The current report does not establish that existing forwarders are slow [R01][R02].

### 5.4 Preserve POSIX semantics deliberately

The raw projection preserves partial transfers, interruption, EOF, offset semantics, descriptor behavior, and thread-local `errno`. Do not make it retry everything, read exactly, decode text, or translate errors into another return representation. `pread`/`pwrite` must not be emulated with shared-offset seek/read/restore [E01].

The typed projection converts native errors immediately at the provider boundary into `SosixError { kind, native_domain, native_code, ... }`. Never read another thread's `errno` after an await. An io_uring CQE's result convention is decoded by that provider rather than misread as a libc return/errno pair [E02].

The current wire constructor rejects zero-length file transfers [R04]. Keep its V1 semantics during compatibility. Define safe public zero-length operations as locally completable only after the documented resource validation, or version the contract deliberately. The raw POSIX view must retain POSIX's own zero-count/error behavior, not force the descriptor constructor's rejection on it.

### 5.5 Sync execution by environment

```text
Native POSIX raw sync call -> libc directly
Native POSIX safe sync call -> bounded adapter -> libc/provider
Hosted async call -> native async/readiness provider or explicit worker
SimpleOS async call -> canonical service/driver provider
SimpleOS POSIX sync compatibility -> allowed outer wait over service completion
GPU service request -> asynchronous device operation, even if host worker uses sync
```

Do not construct `async -> sync wrapper -> block_on(async)` cycles. A synchronous adapter must never pump an unrestricted nested event loop while holding application invariants. Blocking calls on the UI thread, CQ pump, interrupt context, or a nonblocking executor are errors unless a narrowly specified integration mechanism permits them.

Native compiled aliases can remove wrapper overhead. An interpreter still performs interpretation and FFI marshalling; do not call that total path zero-overhead.

---

## 6. Lessons from JavaScript and TypeScript libraries

The useful lesson is an ergonomic asynchronous service surface—not a requirement for a JavaScript VM or garbage collector.

| Source | Relevant mechanism | Adopt for Simple | Do not copy blindly |
|---|---|---|---|
| ECMAScript Promise [E03] | One settled outcome and composable asynchronous reactions | Familiar Future composition; explicit completion authority | Arbitrary thenable assimilation, unbounded reaction allocation, and JS-specific job ordering outside a JS-compatibility layer |
| Node `fs/promises` [E04] | Promise API with work performed off the event loop through the documented filesystem threadpool | Keep application interface separate from implementation strategy | A Promise return type is not proof of kernel-native asynchronous I/O |
| Deno file-system API [E05] | Async/sync pairs and caller-supplied buffers | Clear sync projection and reusable buffer ownership | Whole-file allocation as the only API |
| WHATWG Streams [E06] | Backpressure and byte-stream/BYOB concepts | Bounded streams, explicit credits and provided buffers | An unbounded queue hidden behind an ergonomic stream |
| AbortController/AbortSignal [E07] | Explicit cancellation signaling to cooperating operations | Parent cancellation and cancellation reason | Treating an abort signal as proof of rollback or physical retirement |
| Effect for TypeScript [E08] | Structured fibers and parent/child lifetime management | Task scopes, typed failure, service lifetimes | Importing a second runtime/task ABI alongside Simple's own |

### 6.1 Composition rules

`join_all` starts or joins explicitly admitted work and returns ordered results. A fail-fast variant states whether siblings are merely signaled or canceled-and-joined. Do not assume first failure means all other side effects stopped. `race` returns a winning result but retains losing operations until the chosen cleanup policy is satisfied.

A stream admits a bounded number of outstanding events or byte buffers. Consumers replenish credits; producers cannot grow a hidden list. Input motion may have a declared coalescing policy, while file data cannot silently disappear to relieve pressure.

Structured task scopes own child frames, result slots, and outstanding leases. Scope exit either joins normal completion or performs cancellation plus retirement-aware cleanup. Mission scopes reserve these resources up front.

### 6.2 Continuation scheduling

A provider completion marks the exact task ready; it does not run arbitrary user continuations inline. An already-ready value may be consumed within the current task according to Simple's language semantics, but callback registration must not unexpectedly reenter unrelated application code.

For a real JS/TS compatibility lane, preserve its observable Promise/job semantics through an adapter. The native SOSIX core is not obliged to reproduce all ECMAScript scheduling behavior.

EOF, stream termination, cancellation, timeout, and transient lack of readiness remain distinct typed outcomes. A generic `nil`/empty string/zero fallback must not erase those distinctions.

---

## 7. Host, SimpleOS, and embedded providers

### 7.1 Provider selection

| Deployment | Default deferred-operation strategy | Explicit fallback | Qualification boundary |
|---|---|---|---|
| Linux hosted | io_uring for supported, admitted operations; readiness integration where appropriate | Bounded worker for operations without a suitable nonblocking path | Probe actual kernel features and deployment policy; do not select only by version |
| macOS / BSD hosted | Platform event/readiness facilities, native callbacks, appropriate worker-backed operations | Bounded worker with declared blocking effects | Thread affinity, API availability, buffer visibility and cancellation semantics |
| Windows hosted | Native completion/event mechanisms for supported handle types | Bounded worker for genuinely synchronous APIs | Handle type and operation must actually support selected mode |
| SimpleOS | Existing SOSIX service/driver adapters using canonical operation contracts | Deliberate software/reference provider or unsupported result | Real trap/service/driver path versus model-only evidence |
| Embedded / firmware | Static/pool frames, bounded device queues, interrupt-driven exact wake | No hidden heap/worker fallback | Memory, interrupt, queue and overload bounds |
| Browser / WASM, when selected | Browser asynchronous service adapter | Unsupported where the browser exposes no equivalent | No raw POSIX import promise; browser permissions and event-loop rules |

These are proposed provider strategies, not claims that all are implemented. The Linux ring interface supplies submission/completion queues, but provider-specific behavior still matters [E02].

An unavailable io_uring capability can select a permitted readiness/worker provider before admission. A `direct_required`, `nonblocking_required`, or mission profile fails closed instead of silently falling back. Record mapping grade and reason using the existing `RingMappingGrade` vocabulary.

### 7.2 Scheduler integration

Use the existing executor's ready ingress, timers, task ownership, and notification mechanisms. The provider publishes a completion and the exact wake key. No global Future scan, per-I/O thread, or unrelated second event loop is introduced.

Separate the completion pump, UI-affine work queue, blocking-worker pool, and CPU compute pool. A slow file operation in the worker pool must not stop GPU completions or input ingress. Apply bounded admission, fairness, deadlines, and quotas per instance/service.

Readiness is not completion. A readiness-backed socket provider attempts the operation, handles partial progress, and rearms appropriately when it would block. It must not spin until all bytes are transferred unless the request explicitly means `write_all`, whose implementation itself suspends between opportunities.

### 7.3 Process, environment, and early runtime behavior

Capture configuration/environment needed in hot paths into an immutable startup snapshot. Put process spawn, pipe I/O, exit notification, cancellation and cleanup behind one process service. Avoid the current façade's process-statistics shell command in a mandatory hot path; retain it only as an explicitly labeled compatibility implementation until a proper provider exists [R01].

Do not assume an inherited asynchronous runtime survives `fork` unchanged. Define reinitialization or restrict fork-and-continue in multithreaded compositions; prefer a qualified spawn path. Child capabilities, registered memory and provider generations are explicitly reconstructed or rejected.

Early boot and panic paths need a small static service set: diagnostic output, minimal clock where available, and explicitly permitted memory/device operations. They must not require a heap, normal scheduler, dynamic loader or filesystem merely to report why initialization failed.

---

## 8. SOSIX service extensions for rendering and general I/O

### 8.1 Preserve the existing rendering boundary

The prior renderer research already specifies the correct separation [R06]:

```text
WM / GUI / Web semantics
          |
   DrawIR / Engine2D / GPU execution provider
          |
   SOSIX display / input / timer / file / library services
          |
   platform window system / driver / SimpleOS
```

SOSIX must not become an alternative scene graph, CSS engine, DrawIR encoding, texture cache, or renderer memory manager. It exposes host capabilities and a shared completion model. Existing renderer-private resources can be referenced through generation-safe handles without exposing their private representation.

### 8.2 Extension families

The following service names are proposed façades over the existing contracts and providers. Allocate interface/operation IDs through the canonical registry; do not independently assign numbers in each backend.

| Family | Representative operations | Ownership / async policy |
|---|---|---|
| Display session | Open session, enumerate outputs, create/resize/close surface | Host-affine control operations; deferred where necessary |
| Presentation | Acquire usable image/surface lease, present, readback, request presentation feedback | Async; clear release/completion milestones |
| Input | Subscribe, next event, `try_take`, focus/capture request, device lifecycle | Async stream plus local nonblocking observation |
| Text input | Composition updates, committed UTF-8 text, caret/IME state | Separate from physical keyboard events |
| Time | Deadline, frame pacing, local monotonic observation | Waiting suspends; observation stays direct |
| GPU host service | Device/session discovery, queue capability grant, submit existing execution payload, wait for timeline, registered transfers | Delegates to the existing execution provider; does not duplicate its queue owner |
| File / asset | Positioned reads, metadata, watching, evidence capture | Async default; registered buffers for hot paths |
| Library / executable memory | Open admitted library, query symbols, map/protect/publish executable region | Startup/control plane; cached calls after admission |
| General device I/O | HID, USB endpoint transfer, serial, audio buffers, device event streams | Typed endpoint rights; bounded asynchronous transfers |
| Process / IPC | Spawn, wait, pipe/message exchange, QMP/control protocols | Async with bounded deadlines |
| Configuration | Snapshot selection and admitted runtime policy | Immutable local reads after capture |

A backend may support only a subset. Discovery distinguishes interface presence, operation support, deployment capability, resource authority, and current availability. Returning fabricated success for an unsupported display/input/GPU service is prohibited.

### 8.3 Keyboard, mouse, touch, and other input

An input event carries source/device identity, device generation, monotonically ordered source sequence, timestamp plus clock domain, event kind, and typed payload. Physical key identity, logical key meaning, modifier state, and committed text are separate facts. Mouse coordinates, relative movement, wheel units, touch contacts, gamepad axes, and HID reports must not be collapsed into one untyped integer array.

Preserve ordering for key/button/focus/device events. Coalesce only declared coalescible motion-like events, maintaining a documented sequence range. On overflow or device loss, publish a loss/resynchronization event and restore authoritative key/button state so a dropped release cannot leave the UI permanently pressed.

OS event pumping stays with the platform owner and honors its affinity requirements. GPU code may consume admitted normalized input batches; it does not call platform event-pump functions directly. Focus/capture/clipboard/IME configuration remains authority-checked control-plane work, not a per-lane service request.

### 8.4 Presentation and buffer lifecycle

Use `(surface generation, frame sequence)` for frame identity. Resize or surface recreation invalidates the previous generation. Old GPU work can still need retirement; invalidating a handle does not instantly stop it.

Expose distinct milestones:

```text
request admitted
-> render work submitted
-> GPU rendering finished
-> present request accepted
-> image released / reusable
-> optional displayed-time feedback
```

The portable API promises only milestones it can observe. A queue submission completing is not a universal proof that a frame reached scanout. Vulkan submission and presentation are separate interfaces, and their native synchronization requirements must be honored [E12][E13].

Readback completes only when the selected buffer is valid for the consumer's execution domain. Registered-buffer ownership, native synchronization, and cache maintenance precede visibility to CPU or GPU consumers.

### 8.5 Migration mapping from the existing host interface

| Existing dependency described in the repository research | Target |
|---|---|
| `screen_host.spl`, hosted display adapters | Typed display/session façade, retaining compatibility adapters during cutover |
| `hosted_input_backend.spl`, `hosted_input_sdl2.spl` | Input provider feeding one SOSIX event stream |
| `frame_pacer.spl`, `perf_counters.spl` | Timer service plus synchronous local clock observation |
| `qemu_capture.spl` | Process/IPC/file services with bounded deadline |
| `backend_factory.spl`, `host_compositor_bootstrap.spl` | One startup configuration snapshot and provider admission |
| `hosted_backend*`, `gui_renderer.spl` platform calls | Provider-private platform code, not duplicated in portable renderer logic |
| GPU submission/readback | Shared operation completion over the existing Engine2D execution owner |

This mapping is derived from the checked-in audit, not a claim that every named file remains unmigrated [R06]. Phase P0 resolves exact current paths and consumers before editing.

---

## 9. Compiler, interpreter, loader, and runtime integration

### 9.1 Separate language runtime from OS services

Classify every current runtime function before migration:

| Category | Examples | Destination |
|---|---|---|
| OS service | File, socket, process, time wait, display, device I/O | SOSIX service/provider |
| Language intrinsic | Tagged values, string/array representation, arithmetic helper, closure call | Language runtime/compiler lowering; not renamed into a syscall |
| Memory policy | Arena/pool allocation, object placement | Existing allocation owner, obtaining backing memory through SOSIX as required |
| Native vendor binding | Vulkan/Metal/CUDA driver entry, library-specific ABI | Provider-private typed FFI |
| Compatibility export | Old compiled artifact expects `rt_*` symbol | Versioned shim that forwards in one direction to canonical ownership |

The explicit ban is on **new portable consumers directly calling legacy OS `rt_*` entry points**. It is not a blind deletion of every symbol beginning with `rt_`. A language intrinsic can retain an internal ABI name while staying outside the OS-service namespace.

### 9.2 Compiler responsibilities

The compiler imports immutable SOSIX contract metadata. It resolves aliases to canonical symbol identity; checks execution domain, effects and required capabilities; and emits the target's service/extern imports. It does not schedule I/O while compiling an effect summary.

The compiler itself uses granted host SOSIX services for source/cache/artifact reads, file watching, diagnostic sinks, subprocesses, and target-tool invocation. Parsing, optimization and code generation remain compute tasks. Their pure work need not traverse SOSIX.

Preserve `SimpleCompilerDriverV1` and its coarse handle interface during refactoring [R07]. Supply a versioned host-service context behind the existing in-process adapter, or add an explicitly compatible queryable extension. Do not insert native Rust/Simple trait objects or compiler-private structures into the fixed-width ABI.

A module's dependency manifest records SOSIX interface/schema versions and needed execution capabilities. Changing a Linux provider implementation should not invalidate language parsing caches or rebuild unrelated GPU/VHDL/Lean backends when their contracts are unchanged.

### 9.3 Interpreter responsibilities

A single authoritative generated dispatch description maps SOSIX operations to an interpreter bridge and native/provider implementation. Reuse the SFFI generator seam [R09][R10]. Do not preserve an indefinitely independent hand-maintained semantic implementation of every OS function.

When interpreted execution awaits an operation, store a continuation and return `Pending` with the exact task/waker key. Resume from provider completion. The interpreter bridge must not call a blocking `.wait()` inside its nonblocking poll path.

Legacy `rt_file_read_text` and similar APIs need value conversion and ownership handling, since they return runtime values rather than libc byte counts [R10]. Keep temporary bridges explicit and test their errors, partial results and resource lifetime. Unsupported externs fail with diagnostics, not a fake zero or `nil` interpreted as success.

Use differential tests across seed interpreter, self-hosted interpreter where available, native compilation, and SMF-loaded execution. Different engine representation is acceptable; externally visible SOSIX results and lifecycle must agree.

### 9.4 Loader responsibilities and bootstrap cycle

Preserve the existing SMF loader, compiler SFFI, lazy service cells, cache/lifecycle owners, and provider-generation machinery [R08][L03]. Change the host-service dependency, not the module format or every caller at once.

```text
Stage A: static bootstrap service capsule
    minimal allocation backing, diagnostics, file/mapping access as needed

Stage B: loader core
    validate artifact -> map data -> resolve admitted imports

Stage C: optional provider admission
    verify identity/ABI/capabilities -> initialize -> publish generation

Stage D: execution
    instantiate only the required interpreter/compiler/rendering services
```

The bootstrap capsule cannot require dynamic discovery of the same SOSIX provider needed to load it. It has no dependency on a fully initialized compiler, renderer or ordinary task executor.

Route file mapping, memory protection, executable-region publication and library operations through SOSIX where they are host effects. Instruction invocation and relocation interpretation remain loader/backend responsibilities. JIT publication uses an explicit executable-memory authority and platform policy: write/relocate under writable permissions, perform required cache maintenance, publish executable access, and avoid writable/executable exposure beyond an explicitly admitted mechanism.

Admission and initialization are distinct. Mapping an artifact must not publish a partially initialized service. Resolve thread-affine or potentially blocking initializer work through the appropriate startup owner, without holding the global admission lock across arbitrary plugin code.

A provider generation remains pinned by operation leases, callbacks, active frames and executable references. Unload requires quiescence and retirement, not just absence of public handles. A failing new generation leaves the old admitted generation usable. Cold `--help` and prebuilt-native execution must not eagerly load the compiler, interpreter, GPU stack or every optional service.

### 9.5 Embedded and NVMe firmware compatibility

Keep the existing firmware protocol, FTL/NAND state machines, queue owners and memory pools. Bind their waits/completions to the common contracts; do not force a hosted event loop or GC into firmware. Interrupt paths publish bounded completion records and wake exact tasks without allocation or global scanning.

A NAND/FTL operation may be asynchronous even when a small register access is synchronous. Existing hardware protocol ordering, durability and reset ownership take precedence over cosmetic API symmetry.

---

## 10. GPU-accessible SOSIX: the preferred architecture

### 10.1 A restricted projection, not another operating system API

Preserve the earlier SOSIX-G architecture [L02]. The same operation semantics are projected into host and GPU execution domains with different legal capabilities and transports.

```text
GPU task / kernel
    |
    | checked SOSIX-G request using registered handles
    v
backend-specific device submission transport
    |
    v
host or SimpleOS SOSIX proxy
    | validate authority, generation, ranges, quotas
    | submit through normal SOSIX provider
    v
canonical completion -> device transport -> continuation becomes ready
```

The proxy is a service integrated with the existing runtime/executor. It is not a new global scheduler. GPU request production, host service scheduling, and native GPU submission scheduling are separate responsibilities with one completion/ownership contract.

### 10.2 Reuse the existing tiers

| Tier | Meaning | Typical services | Important distinction |
|---|---|---|---|
| G0 | Device-local after setup | Poll an available completion, append bounded trace, consume admitted input batch, allocate from granted pool | No host operation per call |
| G1 | Host/SimpleOS-proxied service | Authorized positioned I/O, queue/message operation, cancellation, later selected network/device operations | GPU submits; proxy validates and performs service work |
| G2 | Qualified direct-data or device-initiated path | Storage-to-GPU DMA, NIC/GPU data path, future GPU-owned device queues | Direct data and device-initiated control are independently reported |

NVIDIA's GDS documentation explicitly distinguishes its direct data path from the CPU-run control path. BaM is a research precedent for GPU-initiated storage rather than proof that arbitrary GPU platforms expose POSIX/device queues [E16][E17].

### 10.3 Keep source contracts compatible

Retain existing operation IDs such as `SOSIX_FS_READ_AT = 0x0101` and `SOSIX_FS_WRITE_AT = 0x0102` [R04]. Preserve the frozen `@sosix_api` keys and value validation from the earlier SOSIX-G design [L02]. The following is its design pattern, not a claim that all compiler enforcement is implemented:

```simple
@sosix_api(
    id: 257,
    version: 1,
    domains: "host|gpu",
    gpu_transport: "host_proxy_ring",
    effects: "fs|async",
    backend_caps: "gpu_sosix_ring|gpu_system_atomics",
    flags: "cancellable|batchable|partial_progress|registered_buffer"
)
fn sosix_fs_read_at_async(...) -> GpuOperation<ByteCount>
```

`GpuOperation<T>` is a device projection of the canonical operation/future semantics, not a second independent scheduler ABI. A shorter default-async façade name may alias the canonical declaration after the alias fix; it does not create a new wire operation.

The shown system-atomic requirements belong to the earlier live-ring profile. Do not advertise them on a Vulkan/Metal transport that does not provide them. Introduce a separately versioned execution/transport profile through the registry and provider manifests while preserving operation meaning. Do not silently reinterpret a frozen capability bit or add unknown decorator keys.

### 10.4 GPU-callable subset

| Operation class | Initial device policy | Later expansion condition |
|---|---|---|
| Bounded trace append, completion observation, granted-pool operations | G0 allowed | Storage and overflow policy proven |
| `read_at`, `write_at` on pre-opened resource with registered buffer | G1 first vertical slice | Rights, bounds, lease, cancellation and retirement tests |
| Cancellation request | G1 supported through reserved control capacity | Must not require free data-ring slots |
| Input consumption | G0 on admitted normalized batches | Event ordering, generation, overflow/resync validated |
| GPU dependency/timeline request | Nonblocking local/provider dependency | Backend has an appropriate synchronization/continuation mechanism |
| Existing render work submission request | GPU-produced batch consumed by existing execution owner | No duplicate renderer or native queue owner |
| Selected network, IPC and USB operations | Deferred from initial storage slice | Explicit per-operation authority and backpressure contract |
| Open arbitrary path, spawn process, dynamic library load | Host-only by default | Separate explicitly granted control-plane profile, not automatic expansion |
| Raw POSIX pointer/fd calls; arbitrary MMIO/admin queue | Rejected | Not enabled merely by a generic GPU capability |
| Blocking host wait inside device code | Rejected by default | A separately qualified experimental profile would require forward-progress evidence; not part of this plan's baseline |

### 10.5 Supporting synchronous and asynchronous host implementations

A GPU caller remains asynchronous in both cases:

```text
GPU request -> proxy -> native asynchronous SOSIX provider -> completion
GPU request -> proxy -> bounded blocking worker -> native sync call -> completion
```

Thus the scheduler can reach both sync and async host implementations without teaching GPU kernels to block on POSIX. If no worker credit exists, admission waits nonblockingly or rejects according to profile. The completion pump never performs the blocking call itself.

A GPU local `try_poll`, small pure computation or bounded granted-pool operation can remain synchronous. The prohibition concerns waiting for host/device progress while occupying execution resources indefinitely.

### 10.6 Compiler legality

Use resolved symbol identities and whole-call-graph summaries. An alias inherits the original operation's effects and domain restrictions; renaming a host-only API cannot make it GPU legal. Check finite trait/indirect-call target sets transitively. Reject unresolved dynamic dispatch or unknown externs in strict device profiles.

The compiler checks legality and required capabilities; the loader verifies the actual provider; the proxy validates each request's authority. All three are necessary. Source annotations and a name-based scanner alone are insufficient.

---

## 11. CUDA, Vulkan, and Metal transport design

### 11.1 Common semantics, different transport mechanisms

| Backend | Portable/conservative starting point | Optional advanced path | What is not assumed |
|---|---|---|---|
| CUDA | Batched registered request/result buffers, kernel boundaries or explicitly synchronized handoff | Live host/device ring on qualified memory/atomic capabilities; device graph continuation where supported | Mapped memory alone guarantees the required CPU/GPU atomic protocol |
| Vulkan | GPU writes request batch; dispatch completion and explicit memory handoff; host proxy consumes; completion upload/visibility; continuation dispatch | Qualified external synchronization, indirect/device-generated work | Shader can call `vkQueueSubmit2`, POSIX or arbitrary host functions |
| Metal | GPU writes mailbox/batch; command completion/shared-event handoff; host service; subsequent GPU work consumes results | Indirect commands and qualified event-driven continuation | Unified memory eliminates synchronization or lets a shader call host Metal APIs |
| SimpleOS native GPU provider | Same request/continuation semantics over a qualified native driver | Authorized device-initiated hardware queue | Hosted CUDA/Metal stacks automatically exist on SimpleOS |

CUDA's memory and atomic requirements are deployment-specific; qualify the exact system-scope operations and memory allocation type [E09]. Vulkan defines explicit memory scopes and synchronization rather than treating shared addressability as sufficient [E10][E11]. Metal provides shared-event mechanisms for CPU/GPU synchronization [E14].

### 11.2 Dispatch-boundary baseline

For portable Vulkan/Metal, use bounded alternating batches:

```text
1. GPU produces a request batch and records continuation state.
2. GPU dispatch ends or signals a qualified native boundary.
3. Provider establishes CPU visibility and transfers batch ownership.
4. Proxy validates and submits operations through SOSIX.
5. Ready results are packed into bounded completion storage.
6. Provider establishes GPU visibility and schedules continuation work.
7. GPU consumes ready results and advances the corresponding tasks.
```

Double/triple buffering can overlap independent batches. It does not authorize both domains to mutate the same slots concurrently. Every batch records generation, count, bounds, and ownership transition. Host-visible buffers may require staging or cache maintenance; preserve correctness even when that costs more than a live CUDA ring.

This is still an asynchronous ring/batch projection. It is not a requirement to keep every CPU and GPU polling the same memory at the same time.

### 11.3 CUDA live-ring extension

Enable a live host/device ring only after proving publication and completion ordering for the selected allocations and atomic operations. Use bounded polling/adaptive notification policies, aggregate requests per warp/block where useful, and record polling CPU/GPU cost.

No persistent kernel may wait for a host action whose implementation requires another GPU kernel that cannot obtain execution resources. Reserve a proven progress path or return to a dispatch boundary. A timeout detector diagnoses deadlock; it is not a proof that the cyclic dependency is safe.

Per-lane file access should be transformed into coalesced operation batches where semantics allow. Do not simply expose a POSIX-shaped API and issue one host request per lane.

### 11.4 Scheduling and fairness

The proxy has per-client/service credits and bounded completion work. Prioritize completion/retirement/control progress over unbounded new submission. A client that produces many requests cannot exhaust all cancellation or input capacity.

GPU scheduling assurance is explicitly declared: best effort, bounded cooperative dispatch, or a stronger hardware-qualified level. OS-level hard real-time claims must not be inferred from a cooperative polling loop or a successful short test.

Collect separate counters for application CPU, proxy CPU, driver-facing CPU, GPU execution, staged transfers, host submissions, and presentation calls. A short CPU `main()` is useful ergonomics, not proof of zero host overhead.

---

## 12. Stable registry, ABI, and capability negotiation

### 12.1 One authoritative registry

Extend an existing suitable SOSIX/SFFI registry owner after the P0 inventory; do not keep another manually maintained list. Conceptually each entry supplies:

```text
stable operation/interface identity and version
canonical signature and typed result/error contract
execution domains and effects
required resource rights
cancellation/partial-progress/retirement semantics
supported transport profiles
raw POSIX alias eligibility and native binding identity, where applicable
buffer direction, bounds, alignment and lifetime requirements
conformance case IDs
```

This is registry metadata, not a proposal to add every field as new source syntax. Generate host declarations, interpreter dispatch adapters, device stubs, loader requirements, schema validators, documentation tables and missing-implementation tests from it.

One canonical declaration can have several source names. An alias never gets a separate operation ID simply because its name differs.

### 12.2 Version boundaries

Service ABI, typed operation schema, task/ring contract, transport protocol and provider implementation have separate version identities. A new input operation can be additive without changing filesystem wire layout. A changed field meaning requires a genuine schema/contract version.

Native POSIX ABI remains target-specific and is not used as the cross-GPU or cross-process wire ABI. Wire values use explicit widths, bounds, endian/packing rules and registered offsets/handles—not native pointers, `text`, runtime objects or arbitrary function pointers.

Preserve prior SOSIX-G wire structures where adopted. An adapter may translate to a backend's private command buffer, but it must not replace stable IDs or silently truncate offsets/generations.

### 12.3 Capability checks at three boundaries

| Boundary | Check |
|---|---|
| Compile time | Is the operation legal for the execution domain and profile? |
| Admission/load time | Does this provider/hardware implement the required interface and transport safely? |
| Per request | Does this client own the right resource, operation rights, valid generation and registered-buffer range? |

A deployment capability such as direct DMA says what the platform can do. A file-read or display-session capability says what this caller may do. Keep these distinct even in an in-process optimized composition.

Static composition may eliminate redundant checks only when it proves the corresponding invariants. Crossing a trust boundary still requires validation.

---

## 13. SimpleOS feature direction: direct GPU/device queues

Add this as a gated G2 feature family, with a separate backlog in the companion file. The default remains G1 until the selected GPU, endpoint, bus topology, driver and isolation mechanism are qualified.

The design follows a protected control-plane/direct-data separation, for which Arrakis is a systems precedent, while BaM motivates investigation of GPU-initiated storage [E17][E18]. Neither establishes that SimpleOS currently implements the necessary drivers or protection.

```text
SimpleOS control plane
    validate client -> grant queue lease -> register DMA memory
    -> map allowed queue/doorbell resources -> admit device program
                           |
                           v
GPU/device fast path: submit -> DMA -> completion
                           |
                           v
SimpleOS lifecycle plane: revoke -> quiesce -> drain/reset -> retire
```

### Non-negotiable authority limit

An IOMMU can constrain DMA addresses; it does not by itself constrain every storage command's LBA, opcode or namespace. A software proxy's validation also does not protect a raw hardware queue that an untrusted GPU can later modify.

Direct queues therefore require hardware-enforced device/function/resource isolation, or a deliberately trusted and admitted producer within a documented trust model. Where neither is available, retain a validating intermediary. Raw administrative queues and unrestricted MMIO are excluded.

Direct file operations additionally require stable authorized mapping/extent leases, filesystem coherence, invalidation and durability semantics. A direct block-queue prototype is not automatically a safe `read_at(file)` implementation.

GPU peer-to-peer DMA also depends on topology and platform support; qualify supported routes rather than assume all PCIe devices can directly reach each other [E19].

The companion backlog defines control-plane grants, DMA registration, queue transport, revocation, scheduler liveness, filesystem integration, and end-to-end evidence independently so that unsupported hardware does not block the general SOSIX unification.

---

## 14. Migration strategy and release boundaries

### 14.1 No flag-day rewrite

Use an adapter-first migration. Freeze semantics and evidence, introduce the common contract, migrate one production vertical slice, and retire old routes only after parity. Keep file moves/renames separate from semantic changes where feasible.

Compatibility is directional:

```text
old caller -> legacy ABI shim -> canonical SOSIX service -> selected provider
new caller -------------------> canonical SOSIX service -> selected provider
```

A new caller must not depend on a legacy shim that eventually calls back into the new façade. Every route is assigned one implementation owner and one retirement condition.

Profiles may select the old provider temporarily, but the selection is explicit and reported. Do not dual-execute side-effecting writes, process spawns or device commands to compare implementations. Differential testing uses isolated resources or recorded inputs, and read-only shadowing is permitted only when it preserves semantics.

### 14.2 Minimal first vertical slice

Complete this before expanding the service catalog:

```text
same positioned file-read contract
   -> exact raw POSIX alias on native host, where explicitly selected
   -> safe synchronous adapter
   -> asynchronous Linux provider
   -> interpreter bridge and native/SMF-loaded caller
   -> cancellation + retirement + no-GC pool test
```

Use a small immutable input file and a registered buffer. Verify partial reads, offset preservation, error mapping, zero-length contract, admission exhaustion, cancellation races, and buffer ownership. This slice proves the integration mechanism without involving a window system or experimental hardware.

Then add a second vertical slice:

```text
input event -> application/scene update -> Engine2D render
            -> SOSIX present -> completion/retirement
```

Finally expose the already-working service contract to a GPU producer through a qualified transport. Do not debug basic filesystem semantics, a new scheduler, shader lowering, and DMA isolation simultaneously.

### 14.3 Exit boundaries

Define three releases rather than one indefinite completion target:

| Boundary | Required scope | Not required |
|---|---|---|
| Core runtime unification | Shared contracts, exact aliases, async/sync host path, compiler/interpreter/loader integration, baseline SimpleOS adapter, compatibility ownership | Every GPU backend, all devices, direct queues |
| Rendering and SOSIX-G integration | Display/input/timer migration, one real rendering backend, one real GPU-proxy I/O path; remaining backends tracked separately | GPU-initiated hardware queues or standards-complete GPU web semantics |
| Qualified direct-device extension | One specific proven GPU/endpoint/isolation configuration plus reset/authority evidence | Generic support for all GPUs and all SimpleOS targets |

---

## 15. Implementation work packages

### 15.1 Dependency-ordered plan

| Phase / ID | Deliverable and concrete scope | Dependencies | Acceptance gate |
|---|---|---|---|
| P0 / RU-001 | Census service declarations, `rt_*` OS calls, native POSIX imports, Future implementations, host render calls, interpreter dispatch, loader imports and provider ownership. Produce a versioned route manifest. | None | Every in-scope symbol has category, signature, callers, owner, route, profile and migration disposition; unresolved entries stay visible. |
| P1 / RU-010 | Common SOSIX service contract capsule beside existing execution contracts; reconcile existing SOSIX-G metadata and SFFI registry. | RU-001 | No OS-private imports in common; no duplicate operation IDs; schema/version and module-boundary tests. |
| P1 / RU-011 | Repair renaming re-export identity through seed/native/interpreter/SMF paths; preserve original effects and ABI. | RU-001 | Same declaration identity, no generated wrapper, correct diagnostics; existing callers unaffected. |
| P2 / RU-020 | Canonical operation adapter, retirement leases, cancel/control capacity, generation exhaustion and exact wake integration. | RU-010 | State-machine/property tests plus adversarial delayed-completion tests pass. |
| P2 / RU-021 | Future/Promise compatibility over canonical tasks; owned/static/pool result/frame storage. | RU-020 | No hidden blocking or hot-path growth in qualified pool profile; old API parity maintained. |
| P3 / RU-030 | Native POSIX raw alias bindings and safe sync façade; platform ABI/errno tests. | RU-010, RU-011 | Calls resolve to intended libc symbols without `rt_*` OS forwarding; safe adapters retain validation. |
| P3 / RU-031 | Linux asynchronous filesystem/timer baseline with explicit readiness/worker fallback policy. | RU-020, RU-021 | Real provider evidence, bounded worker/queue exhaustion, correct errors and buffer lifetime. |
| P4 / RU-040 | Generate interpreter/native dispatch from one registry; migrate file-I/O vertical slice and extend by family. | RU-030, RU-031 | Same contract results in seed/interpreter/native/SMF tests; no unknown extern success fallback. |
| P4 / RU-041 | Inject SOSIX host services behind compiler-driver boundary; source/cache/process/diagnostic routing. | RU-040 | Multi-target compile tests; host/provider changes do not force unrelated backend rebuilds. |
| P4 / RU-042 | Loader bootstrap capsule, memory/library service integration, lazy provider generation lifecycle. | RU-020, RU-030, RU-040 | No bootstrap cycle; W^X-policy tests; in-flight unload blocked; cold optional loads remain zero. |
| P5 / RU-050 | Display/input/time/configuration service extensions and compatibility adapters over existing host interfaces. | RU-010, RU-020 | Headless/model contract tests; input loss/resync and surface-generation tests. |
| P5 / RU-051 | Migrate one real host rendering path, preferably Vulkan-enabled rendering, to SOSIX host services. | RU-050, RU-031 | Native input/render/present/readback evidence; no per-primitive host requests or duplicate submit owner. |
| P5 / RU-052 | Add Windows and Darwin/BSD provider parity, including affinity and native completion bridges. | RU-050, host infrastructure | Separate native-host acceptance rows; unavailable hosts remain blocked, not inferred from Linux. |
| P6 / RU-060 | GPU legality/profile metadata and generated device stubs; reuse existing API IDs/contract. | RU-010, RU-020 | Transitive forbidden-call, alias laundering, missing-capability and malformed-request negatives. |
| P6 / RU-061 | G1 proxy storage slice: bounded trace, positioned read/write, cancellation, registered buffers, one queue pair per admitted client/shard. | RU-031, RU-060 | Real device-produced request and independently verified file/buffer effect; spoofed completions rejected. |
| P6 / RU-062 | Vulkan dispatch-boundary transport and continuation; rendering/input composition integration. | RU-051, RU-061 semantics | Native barriers/visibility and continuation tests under randomized delays; no fake live-ring capability. |
| P6 / RU-063 | CUDA transport and qualified optional live-ring profile. | RU-061 semantics | Memory/atomic/liveness qualification per allocation/platform; persistent-kernel cycles rejected or avoided. |
| P6 / RU-064 | Metal event/command-boundary transport and continuation. | RU-061 semantics, Darwin provider | Real Metal execution, visibility, cancellation and device-loss evidence. |
| P7 / RU-070 | SimpleOS service provider integration and static/pool embedded/firmware adapters. | RU-020, RU-021, RU-040 | Actual trap/service/driver execution; bounded ISR wake, no hidden heap; preserve existing firmware semantics. |
| P8 / RU-080 | Optional SimpleOS direct GPU/device queues, following companion GQ backlog. | RU-060, RU-070, qualified hardware | Authority, DMA, retirement, reset and no-proxy steady-state evidence for the specific admitted setup. |
| P9 / RU-090 | Retire migrated portable `rt_*` OS routes and duplicate host façades; keep only declared legacy artifact shims. | Accepted core/render service families | Symbol/import graph gates, old artifact compatibility window, no dead reverse dependency. |

P9 is incremental by family and does not wait for P8. Experimental direct queues must not hold the rest of the runtime migration hostage.

### 15.2 File-level starting points

| Work area | Verified existing starting points | Proposed changes |
|---|---|---|
| Hosted façade | `src/lib/nogc_async_mut/sosix/host_facade.spl` | Replace wrapper-only architecture with shared contracts and explicit adapter/alias classes; preserve exports during cutover |
| Common execution | `src/lib/common/contracts/execution` | Reuse existing names; add SOSIX service contracts in a dependency-safe sibling capsule |
| SOSIX operation lifecycle | `src/os/sosix/core/operation.spl` | Adapt legacy identity/state to canonical ring owner; enforce retirement and generation-exhaustion policy at owning boundary |
| File operations | `src/os/sosix/fs/operation_adapter.spl` | Preserve IDs and validate public-to-wire semantic adaptation; use existing VFS/provider owners |
| Future compatibility | `src/lib/nogc_async_mut/async_ring/future_compat_adapter.spl` | Extend the nonblocking adapter direction, not another Future implementation |
| Compiler service injection | `src/compiler/80.driver/driver_provider_contract_v1.spl` | Preserve outer descriptor; supply context through compatible implementation seam |
| Interpreter registry | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` | Generated SOSIX bridge registration and explicit legacy imports |
| SFFI generation | `src/compiler/90.tools/sffi_gen/specs/file_io.spl` | Separate low-level binding spec, high-level helper composition and legacy value conversion |
| Loader | `src/compiler/99.loader/loader/module_loader.spl` and imported service/lifecycle owners | Route host effects through service context; retain lazy semantic/JIT/module ownership |
| Renderer migration | Files classified by `doc/01_research/local/sosix_wm_renderer_host_interface.md` | Resolve exact current paths in P0, migrate by dependency family, retain Engine2D ownership |
| Tests / guards | Existing `test/01_unit`, integration/system roots, and `scripts/check` conventions | Add route/alias/effect/lifetime/actual-provider evidence gates, then wire them into real workflows |

The table deliberately avoids inventing a current path for an uninspected implementation. New capsule names and tool commands below are proposals until admitted into the repository's conventions.

### 15.3 Parallel-agent ownership

Use paired ownership: one layer/contract reviewer plus one feature/backend implementer. Each implementation agent works on a separate branch/worktree and a bounded file set. Contract/schema changes require the contract owner's review before consumers land.

| Workstream | Primary responsibility | Can proceed in parallel after |
|---|---|---|
| A: Contract/ABI | Registry, common values, versioning, alias semantics | P0 |
| B: Lifecycle/no-GC | Retirement, task adapters, static/pool storage | Contract draft freeze |
| C: Host providers | POSIX alias path, Linux provider, worker policy | Signature/lifecycle freeze |
| D: Language tools | Interpreter, compiler-driver service injection, loader bootstrap | Shared service test provider available |
| E: UI/renderer | Display/input extensions, native provider migration | Service contracts and completion integration available |
| F: GPU transports | Checker/proxy shared tests; CUDA/Vulkan/Metal adapters | Stable G1 semantics and host provider |
| G: SimpleOS | Native service integration, embedded pools, optional direct queue backlog | Common contracts and lifecycle tests |
| H: Verification | Differential tests, route census, native evidence, performance | Starts at P0; independent of implementation ownership |

All streams share generated fixtures and contract tests. They must not each implement their own handle allocator, cancellation enum, Future, renderer queue or provider manifest.

---

## 16. Verification and acceptance tests

### 16.1 Mandatory test matrix

| ID | Test | Required evidence |
|---|---|---|
| V01 | Alias resolution through re-export chains | Same canonical symbol and inherited effects in each supported engine |
| V02 | Native exact-alias code generation | Object/IR inspection shows libc import, no SOSIX/`rt_*` forwarding body for the tested alias |
| V03 | POSIX ABI correctness | Target widths, calling convention, structure layouts and symbol declarations validated per platform |
| V04 | Raw POSIX behavior | Partial I/O, EINTR/error/EOF/zero-count semantics and positioned offset preservation |
| V05 | Safe façade validation | Invalid/stale capability, incorrect rights and out-of-range buffer rejected before effect |
| V06 | Async nonblocking behavior | Delayed I/O does not block unrelated tasks, input or completion progress |
| V07 | Reserve/commit transaction | Failed reservation has no side effect/CQE; committed single-shot work has one terminal outcome |
| V08 | SQ/CQ/control exhaustion | Bounded rejection or admitted waiting; no overwrite/growth; cancellation/reset still progresses |
| V09 | Duplicate/stale/cross-ring completion | No wrong wake, double settle or reused-slot corruption |
| V10 | Cancellation race | Every ordering of cancel/start/partial effect/complete produces a permitted outcome |
| V11 | Deadline versus retirement | Early timeout cannot release buffer, mapping, callback or provider generation still in use |
| V12 | Generation exhaustion | Fail-closed/quarantine path; old tokens never regain validity |
| V13 | No-GC / pool allocation | Allocation instrumentation for declared scope shows no GC dependency and no pool-profile growth after Ready |
| V14 | Future drop / scope exit | Cleanup retains resources until safe, with bounded supervisor/mission behavior |
| V15 | Interpreter/native/SMF parity | Same service semantics and diagnostics across actual selected execution engines |
| V16 | Loader bootstrap | Minimal service capsule can start without loading itself recursively |
| V17 | Loader generation unload | In-flight callback/frame/operation blocks unload; new-generation failure preserves old generation |
| V18 | Compiler host/target independence | Host services correct while compiling multiple non-host targets |
| V19 | Input ordering and loss | Key/button transitions, text composition, motion coalescing, overflow and device removal behave correctly |
| V20 | Surface resize/loss | Stale presents rejected; old resources retired before reuse; no deadlock on recreate |
| V21 | Presentation milestones | Render-complete, image-reusable and optional displayed-time facts not conflated |
| V22 | Real rendering execution | Native input-to-frame path, independent pixel/readback oracle and actual backend identity |
| V23 | GPU legality | Transitive host calls, alias-based bypass, unknown externs and missing profile capabilities rejected |
| V24 | G1 request provenance | Request actually produced by GPU; host effect and device result independently verified |
| V25 | GPU memory handoff | Randomized host/device delays and native barriers expose no stale payload/completion |
| V26 | GPU forward progress | No wait cycle between resident kernel, host proxy and required continuation kernel |
| V27 | Device/proxy loss | Reset/revoke drains or quarantines safely; stale completion cannot mutate a new generation |
| V28 | SimpleOS real service route | Guest program traverses actual capability/trap/service/driver path, not host mock |
| V29 | Firmware/static profile | ISR has bounded publication, no allocation/global task scan; protocol/durability tests unchanged |
| V30 | Direct-queue authority | Forbidden DMA target, queue, opcode or block/namespace access rejected or unreachable in admitted hardware trust model |
| V31 | Direct path truthfulness | Independent control-path/data-path counters and payload evidence; no hidden CPU proxy/copy under direct-required policy |
| V32 | Compatibility sunset | Every retained legacy import belongs to declared artifact compatibility; new consumers cannot introduce direct legacy OS calls |

A test runner should collect all independent failures rather than stop after the first compile error. After a fix, rerun the affected failing scope first, then the relevant broader regression suite. A final release still requires the full declared suite; selective reruns are an iteration optimization, not a substitute.

### 16.2 Native evidence rules

A PASS record identifies source revision, artifact digest, provider identity/generation, OS/kernel, CPU/GPU/device/driver, profile, test inputs, executed test count, output/trace digest, and observed route. Missing hardware or a missing feature binary is `BLOCKED`, not PASS.

Separate evidence levels:

```text
source contract / model test
interpreter or software provider execution
native CPU/provider execution
real GPU execution
real SimpleOS guest service/driver execution
qualified real device direct-queue execution
```

Do not count a test of a comparator, a generated manifest, an emulator, or a source scanner as hardware execution. QEMU can prove the tested guest behavior; it cannot establish native Metal/Vulkan/CUDA performance or actual GPU-to-NVMe DMA.

Guards must be wired into an actual workflow or explicitly classified as manually invoked hardware gates. A passing guard with zero discovered or executed relevant tests is rejected.

---

## 17. Performance, memory, and observability

### 17.1 Structural budgets first

Before choosing numeric regression thresholds, establish repeatable baselines. The following are architectural budgets, not invented speed claims:

| Scenario | Structural target |
|---|---|
| Exact native POSIX alias | No additional forwarding function, heap allocation, Future or queue |
| Synchronous pure/local leaf | No task/frame creation or scheduler visit |
| Warm in-process service | No repeated symbol lookup or full provider validation |
| Async request | Bounded admission and exact wake; no global Future/task scan |
| Mission-pool steady state | No pool growth or undeclared allocation in the declared scope |
| Cold help / prebuilt-native startup | No optional compiler/interpreter/GPU provider initialization |
| Rendering | Host requests at event/frame/resource-batch scale, not per pixel/primitive |
| GPU proxy | Batched requests; separate measured proxy and driver-facing CPU use |
| G2 direct-required | No silent staging or proxy fallback where forbidden |
| Instrumentation disabled | No optional tracing allocation or polling worker solely for tracing |

### 17.2 Measurements

Measure latency distribution, throughput, CPU time by owner, wake/kick counts, SQ/CQ occupancy, batch size, allocation counts/bytes, high-water storage, staging bytes, native submissions, and retirement delay. Include startup cold/warm differences and both tiny and throughput-oriented workloads.

Compare the direct POSIX baseline to the alias using the same optimization, linking, and instrumentation configuration. Inspect generated objects as well as timings; kernel/service latency can hide a wrapper cost. Report any PLT/dynamic-linking costs that also exist in the baseline rather than attributing them to SOSIX.

Compare async providers against appropriate synchronous/worker alternatives, not only against the previous implementation. More asynchronous machinery or more GPU offload is not automatically faster. Backend selection is policy and evidence driven.

### 17.3 Optional instrumentation

Reuse existing bounded tracing/profiling and provider identity mechanisms. Keep always-available summaries inexpensive; fine-grained dynamic instrumentation and recompiled tracing are separate compositions. No claim that a disabled feature is free is accepted without inspecting its code/data/startup effects.

Logical timeout versus physical retirement delay is a first-class metric: a system can report quick cancellations while retaining large amounts of pinned memory. Expose that condition rather than hiding it in generic queue latency.

---

## 18. Risks, deliberate exclusions, and completion criteria

| Risk | Mitigation |
|---|---|
| SOSIX becomes a monolithic OS/renderer/runtime | Common contracts plus separate owners; reject renderer/compiler-private types crossing service ABI |
| "Async" wrappers secretly block | Effect checks, delayed-operation concurrency tests and explicit worker metadata |
| Alias rename loses type/effect/extern identity | Resolver/SMF/engine parity tests before wrapper retirement |
| No-GC label conceals allocation or leaks | Owned frame/lease lifecycle and profile-scoped allocation evidence |
| Cancellation frees resources too soon | Retirement leases and provider-generation pins |
| GPU mailbox works accidentally on one device | Backend-specific visibility/liveness qualification and dispatch-boundary baseline |
| GPU direct queues bypass authority | Hardware/trusted-producer model or validated intermediary; no unrestricted raw queue grant |
| Cross-platform parity claimed from a single host | Separate native-provider acceptance records |
| Compatibility lasts forever | Route manifest with owner, consumer set, deprecation scope and release exit condition |
| Migration weakens bootstrap reliability | Static recovery capsule and unchanged outer compiler/loader boundary |

This plan does not promise a POSIX syscall ABI inside a shader, a complete GPU browser, a universal SimpleOS CUDA/Metal runtime, zero driver allocation, or hard-real-time GPU scheduling on unqualified hardware. These are different capabilities with different proof requirements.

**Core completion means** portable in-scope consumers use canonical SOSIX contracts; native exact aliases are verified; asynchronous work uses the shared task/ring lifetime model; interpreter/native/loader behavior agrees; SimpleOS has an accepted provider path; and remaining legacy exports are explicitly bounded compatibility, not active parallel architectures.

**Rendering/GPU completion means** the relevant real backend has passed its own acceptance gates. One backend's success does not complete the others. **Direct-queue completion means** one declared hardware/trust configuration passes the companion requirements, not that all SimpleOS devices acquire the capability.

---

## 19. Source ledger

Repository links are pinned to the inspected revision. External specifications/documentation were consulted on 2026-09-05; their live content may change. References support baseline facts and design precedents, not a claim that the proposed Simple implementation is already complete.

### Repository evidence

- **[R01]** Hosted SOSIX façade and its declared limitations: [host_facade.spl](https://github.com/ormastes/simple/blob/27f1973cc1548fa7cfd0994032d6186f77bcf593/src/lib/nogc_async_mut/sosix/host_facade.spl).
- **[R02]** Recorded renaming re-export resolver gap: [September 3 bug report](https://github.com/ormastes/simple/blob/27f1973cc1548fa7cfd0994032d6186f77bcf593/doc/08_tracking/bug/no_renaming_re_export_blocks_zero_cost_facade_alias_2026-09-03.md).
- **[R03]** SOSIX operation lifecycle source: [operation.spl](https://github.com/ormastes/simple/blob/27f1973cc1548fa7cfd0994032d6186f77bcf593/src/os/sosix/core/operation.spl).
- **[R04]** Positioned file operation IDs and constructor: [operation_adapter.spl](https://github.com/ormastes/simple/blob/27f1973cc1548fa7cfd0994032d6186f77bcf593/src/os/sosix/fs/operation_adapter.spl).
- **[R05]** Canonical ring/task ownership and implementation-status limits: [Simple Ring and Async Base Architecture](https://github.com/ormastes/simple/blob/27f1973cc1548fa7cfd0994032d6186f77bcf593/doc/04_architecture/simple_ring_async_base.md).
- **[R06]** Existing rendering-host/SOSIX boundary: [WM and Renderer Host Interfaces](https://github.com/ormastes/simple/blob/27f1973cc1548fa7cfd0994032d6186f77bcf593/doc/01_research/local/sosix_wm_renderer_host_interface.md).
- **[R07]** Compiler's fixed-width outer provider contract: [driver_provider_contract_v1.spl](https://github.com/ormastes/simple/blob/27f1973cc1548fa7cfd0994032d6186f77bcf593/src/compiler/80.driver/driver_provider_contract_v1.spl).
- **[R08]** Loader public surface and lazy service ownership, inspected lines 1–160: [module_loader.spl](https://github.com/ormastes/simple/blob/27f1973cc1548fa7cfd0994032d6186f77bcf593/src/compiler/99.loader/loader/module_loader.spl).
- **[R09]** Interpreter extern registration seam, inspected search excerpts: [interpreter_extern/mod.rs](https://github.com/ormastes/simple/blob/27f1973cc1548fa7cfd0994032d6186f77bcf593/src/compiler_rust/compiler/src/interpreter_extern/mod.rs).
- **[R10]** Existing SFFI file-I/O generator definitions, inspected lines 1–140: [file_io.spl](https://github.com/ormastes/simple/blob/27f1973cc1548fa7cfd0994032d6186f77bcf593/src/compiler/90.tools/sffi_gen/specs/file_io.spl).
- **[R11]** Existing nonblocking Future-to-ring adapter, inspected search excerpt: [future_compat_adapter.spl](https://github.com/ormastes/simple/blob/27f1973cc1548fa7cfd0994032d6186f77bcf593/src/lib/nogc_async_mut/async_ring/future_compat_adapter.spl).

### Retrieved prior design documents

These saved documents were consulted for continuity; they are not substituted for current source or hardware evidence.

- **[L01]** `simple_ring_async_architecture.md`: shared rings, async-default ergonomics, allocation profiles and firmware/OS migration.
- **[L02]** `simple_sosix_gpu_api_extension_final_report.md`, dated 2026-08-11: SOSIX-G tiers, API metadata, capability distinction and compiler checking design.
- **[L03]** `simple_compiler_kernel_plugin_bootstrap_refactor_plan.md`: retained outer driver ABI, provider generation lifetime and lazy startup.
- **[L04]** `simple_gpu_scheduler_sosix_resident_rendering_design_2026-09-05.md`, inspected revision `0aed33b8e84f5e6dbe080386e36358fdf0cb4ea6`: renderer ownership, GPU-resident scene versus render-only lanes, and backend-specific evidence.

### External primary sources

- **[E01]** The Open Group, POSIX.1-2024 [`read` / `pread`](https://pubs.opengroup.org/onlinepubs/9799919799/functions/read.html).
- **[E02]** Linux man-pages, [`io_uring(7)`](https://man7.org/linux/man-pages/man7/io_uring.7.html).
- **[E03]** TC39, [ECMAScript control abstraction / Promise specification](https://tc39.es/ecma262/multipage/control-abstraction-objects.html).
- **[E04]** Node.js, [File system APIs](https://nodejs.org/api/fs.html).
- **[E05]** Deno, [File-system APIs](https://docs.deno.com/api/deno/file-system/).
- **[E06]** WHATWG, [Streams Standard](https://streams.spec.whatwg.org/).
- **[E07]** WHATWG, [DOM: aborting ongoing activities](https://dom.spec.whatwg.org/#aborting-ongoing-activities).
- **[E08]** Effect, [Structured concurrency and fibers](https://effect.website/docs/v3/concurrency/fibers).
- **[E09]** NVIDIA, [CUDA advanced kernel programming](https://docs.nvidia.com/cuda/cuda-programming-guide/03-advanced/advanced-kernel-programming.html) and [unified-memory requirements](https://docs.nvidia.com/cuda/cuda-programming-guide/04-special-topics/unified-memory.html).
- **[E10]** Khronos, [Vulkan memory model](https://docs.vulkan.org/spec/latest/appendices/memorymodel.html).
- **[E11]** Khronos, [Vulkan synchronization and cache control](https://docs.vulkan.org/spec/latest/chapters/synchronization.html) and [synchronization examples](https://docs.vulkan.org/guide/latest/synchronization_examples.html).
- **[E12]** Khronos, [`vkQueueSubmit2`](https://docs.vulkan.org/refpages/latest/refpages/source/vkQueueSubmit2.html).
- **[E13]** Khronos, [`vkQueuePresentKHR`](https://docs.vulkan.org/refpages/latest/refpages/source/vkQueuePresentKHR.html).
- **[E14]** Apple, [`MTLSharedEvent`](https://developer.apple.com/documentation/metal/mtlsharedevent) and [synchronizing CPU/GPU work](https://developer.apple.com/documentation/metal/synchronizing-cpu-and-gpu-work).
- **[E15]** Khronos, [Vulkan memory allocation](https://docs.vulkan.org/spec/latest/chapters/memory.html).
- **[E16]** NVIDIA, [GPUDirect Storage overview](https://docs.nvidia.com/gpudirect-storage/overview-guide/index.html).
- **[E17]** BaM research paper, [GPU-Initiated On-Demand High-Throughput Storage Access in the BaM System](https://arxiv.org/abs/2203.04910).
- **[E18]** Peter et al., [Arrakis: The Operating System Is the Control Plane](https://www.usenix.org/conference/osdi14/technical-sessions/presentation/peter), OSDI 2014.
- **[E19]** Linux kernel documentation, [PCI peer-to-peer DMA support](https://docs.kernel.org/driver-api/pci/p2pdma.html).
