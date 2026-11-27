# Simple XRay: final design and staged implementation plan

**Date:** 2026-11-03
**Revision:** 1.0 — design and qualification plan, not a declaration of production support
**Repository:** `ormastes/simple`
**Sequence:** 1. Linux / LLVM XRay → 2. Linux / Simple-owned XRay-like implementation → 3. Windows / Simple-owned implementation
**Primary constraint:** one public interface and event contract across all three stages; minimal Windows build impact during stages 1 and 2.

## 1. Final decision

Proceed with this sequence. Put a **Simple-owned, backend-neutral V1 interface in front of LLVM XRay from the beginning**. Keep the Linux LLVM implementation as a private adapter, replace its internals with the Simple implementation in stage 2, and add the Windows host and ABI implementations in stage 3. Applications, aspects, profilers, readers, and tools must not call LLVM XRay directly.

The design is feasible without adding language exceptions, implementing hot unload, or making a Windows port of LLVM's complete XRay runtime a prerequisite. A Simple-owned implementation can use stock LLVM to produce objects while owning its instrumentation, metadata, patching, collection, and session logic. Small ISA-specific assembly/intrinsic leaves remain necessary; “pure Simple” here means **no dependency on LLVM's XRay runtime**, not that machine-specific instructions disappear.

The responsible meaning of “risk free” is:

> No known unmitigated correctness defect in an explicitly qualified configuration; unsupported configurations are rejected before activation; failures do not expose partially initialized instrumentation. Evidence and release gates determine which configurations are enabled.

It does **not** mean that finite tests prove every CPU, optimizer transformation, application, or operating-system version safe. The work already includes native Windows execution, not research alone. It also found a real vector-state defect in the first prototype. This document records that defect, its bounded remedy, and the conditions still required for production.

### Non-negotiable decisions

1. Freeze the public interface, statuses, capabilities, metadata, and event schema before stage 1 ships.
2. Preserve current application/AOP behavior unless dynamic observation is explicitly selected.
3. Keep Windows tracing off by default through stages 1 and 2. Do not add Linux XRay dependencies to its build graph.
4. Distinguish atomic patch-site switching, callback lifetime, and exact entry/exit pairing. They are separate correctness problems.
5. Keep instrumentation code, maps, handler shims, and referenced generations resident until process exit. Hot unload is not part of this project.
6. Use raw, transition-marked events as the common guarantee. Exact paired spans are a separately advertised capability with stronger admission conditions.
7. Start with conservative, explicitly supported ABI/ISA profiles. Reject unsupported state rather than silently corrupting it.
8. Instrumentation is observer-only. Arbitrary around-advice, return-value replacement, and function replacement continue to use their separate mechanisms.

## 2. Scope and exclusions

### In scope

- Linux x86-64 first, then qualified Linux AArch64.
- Native Windows x64 and Windows ARM64; qualify the two independently.
- Function entry, ordinary exit, and tail-exit observation of emitted machine functions.
- Dynamic enable/disable of selected instrumentation and resident observer providers.
- Function/site maps, concurrent control requests, bounded collection, session boundaries, normal process shutdown, and explicit loss reporting.
- A shared Simple core over SOSIX POSIX-backed and Windows-backed host leaves.
- Compiler/object/linker integration and tests of real generated binaries.
- Host configuration that permits the requested memory operations, as assumed by the user.

### Not prerequisites

- Simple language exceptions or SEH-based patching.
- Unwinding through the instrumentation trampoline, exception propagation through callbacks, or reliable asynchronous stack walking through every trampoline instruction.
- DLL/module/provider unloading and executable-memory reclamation while the process runs.
- Changing system-wide security policy or bypassing a denied policy.
- Windows x86-32, ARM32, ARM64EC, kernel tracing, arbitrary third-party binary rewriting, and instrumenting unknown calling conventions.

In this document, **x64 means x86-64**, not 32-bit x86. The existing tests do not establish x86-32 support.

Excluding unwind does not exclude ordinary ABI correctness, stack alignment, stack probing, platform-reserved registers, control-flow protection, or normal return behavior. A foreign exception, `longjmp`, cancellation, or forced thread termination crossing an admitted exact span is unsupported unless a later explicit integration supplies the necessary boundary handling.

## 3. Evidence: what has actually been checked

### 3.1 Pinned repository inspection

Source inspection used:

- Main: `97700b29e10675867891503f1e634b50a192356d`.
- Release: `2425a95cc1772b5e4c4b1a4d45474f1feac4ad2d`.
- Native prototype: [draft PR #5962](https://github.com/ormastes/simple/pull/5962), deliberately unmerged.

These are snapshots, not a claim that every feature described below exists in the current application runtime.

### 3.2 Native Windows patching evidence

[Run 41443090162](https://github.com/ormastes/simple/actions/runs/41443090162), prototype commit `dd76b9e173f19a77371c0a17d2cf2164bd6b3a1b`, passed on actual Windows x64 and ARM64 runners.

| Observation | Windows x64 | Windows ARM64 |
| --- | --- | --- |
| Native object generation, assembly, link, execution | Passed | Passed |
| Runner | `windows-2025` | `windows-11-arm` |
| Process CFG query | Enabled | Enabled |
| x64 CET shadow-stack query | Enabled, compatibility mode; strict = 0 | Not applicable; query error 50 |
| Statically enabled scalar function | 50,000 entries and 50,000 exits | 50,000 entries and 50,000 exits |
| Concurrent pair-state transition iterations | 15,000 | 15,000 |
| Worker calls overlapping the transition period | 1,712,839,200 | 1,722,441,816 |
| Raw entry / exit callbacks during transitions | 1,463,895 / 1,456,558 | 716,384 / 706,894 |
| Incorrect result / incorrect function ID | 0 / 0 | 0 / 0 |

Each transition iteration updates entry and exit sites separately; it is not one atomic two-site transaction. Most of the very large worker-call totals traverse disabled instrumentation. They are **not** billions of recorded callbacks and are **not** an instrumentation-overhead benchmark.

This fixture tests one scalar addition function and four workers. Unequal raw entry/exit counts during switching are expected. The result establishes practical feasibility for this fixture, not complete register-state preservation, generic nested-span correctness, full Simple compiler integration, or a universal instruction-fetch proof.

### 3.3 ABI and compiler regression evidence

A deterministic local test executed the Windows x64 calling convention on a Linux x86-64 host. Its callback is a conforming ordinary Windows x64 callee that changes volatile vector state and MXCSR status.

| Test | Observed outcome | Meaning |
| --- | --- | --- |
| Original x64 trampoline, entry and exit | All 16 upper YMM halves lost; MXCSR changed from `0x1f80` to `0x1fa0`; tested lower halves and RFLAGS preserved | A real defect for an unrestricted handler, not merely an unknown risk |
| Bounded replacement, entry and exit | YMM0–15, MXCSR, tested RFLAGS, ID, kind, and callback counts preserved | Concrete remedy for the tested state profile |
| LLVM 20 verifier: hook between `musttail` and `ret` | Rejected as invalid IR | This insertion strategy is wrong |
| LLVM 20 verifier: tail-exit hook before `musttail` | Accepted | Correct placement direction; native tail semantics still need tests |

The bounded x64 fixture saves a `0x230`-byte area for shadow space, YMM registers, MXCSR, and padding, in addition to its integer/flags saves. It does not claim AVX-512, AMX, APX, x87/MMX, or special-calling-convention coverage.

The same expected-defect/remedy regression subsequently **passed on native Windows x64**, first in run `41553846630` and again in the final successful run `41554579305`. See section 19 for the pinned commit, jobs, and mitigation results. This upgrades the remedy from local `ms_abi` evidence to native Windows evidence for its bounded profile; it does not qualify the Linux SysV profile or the entire Simple runtime.

### 3.4 Additional native qualification

Additional ABI and process-isolated enforcement probes were added to the same draft PR. Their exact results are recorded in the final qualification addendum at the end of this document. A green aggregate job must never be substituted for per-feature results: the enforcement probe explicitly distinguishes `ENFORCEMENT_PASS`, `UNAVAILABLE_NOT_PROVEN`, and an unclassified failure.

### 3.5 Evidence that must not be overstated

- A previous flat-function test with one thread-local token does not prove recursive, nested, or migrating-fiber span consistency.
- Executing PAC/BTI instruction encodings is not proof that the corresponding protection is enforcing.
- Cross-compiling ARM64 on an x64 Windows host proves compilation/linking properties, not native ARM instruction-fetch or mitigation behavior.
- The existing repository job named “Windows ARM64 Cross-Compile” was not sufficient native ARM evidence in the inspected snapshot; the dedicated native runner is the relevant evidence here.
- Standalone LLVM IR/assembly fixtures are not a completed implementation in the Simple source-to-binary pipeline.

## 4. Repository integration: reuse the right parts

Paths in this table exist in the inspected repository. New file names proposed later are not represented as implemented.

| Existing path | Finding | Required action |
| --- | --- | --- |
| `src/lib/common/plugin/aspect_params.spl` | `AspectParamsV1` already has a versioned header and extension array | Add a named trace extension; preserve old field ordinals and semantics |
| `src/compiler/80.driver/driver_pipeline_aop.spl` | AOP weaving and debug-trace routes are distinct | Add opt-in dynamic observer planning; do not silently replace either route |
| `src/compiler/50.mir/mir_debug_trace_injection.spl` | Current helper emits direct zero-argument trace calls, with no complete dynamic-site map | Add semantic site intent separately; this is not already an XRay emitter |
| `src/lib/nogc_sync_mut/replay/semantic/trace_writer.spl` | Existing replay writer is unsuitable for a nonallocating hot callback | Use bounded native records and deferred conversion into replay format |
| `src/lib/common/aspect_dynload_lifecycle_v1.spl` | Explicitly requires external lifecycle serialization; no standalone thread-safety claim | Reuse lifecycle vocabulary, not an assumed concurrency proof |
| `src/compiler/99.loader/joinpoint_slots.spl` | Indirect function-pointer data cells, not instruction-stream sleds | Keep separate; do not conflate pointer publication with code patching |
| `src/os/sosix/host/library_capability_adapter.spl` | Pure capability/callback seam, not an installed effectful memory provider | Implement narrowly scoped effectful host leaves |
| `src/os/port/llvm/compiler_rt_cmake.cmake` | SimpleOS freestanding builtins-only configuration intentionally disables XRay | Leave it unchanged; create a separate hosted Linux dependency path |
| `.github/workflows/windows-build.yml` | Owns the existing Windows toolchain/build settings | No tracing-driven toolchain bump or unconditional dependency change in stages 1–2 |

The SOSIX dynload/memory route manifest also identifies missing effectful-provider/lifetime integration. This is implementation work, not evidence that SOSIX already supplies every primitive required here. See the pinned repository references in section 18.

## 5. Frozen public V1 contract

### 5.1 Boundary

Expose a Simple tracing/observation facade. LLVM function IDs, LLVM callback signatures, LLVM log formats, patch functions, ELF details, Win32 types, and native pointers remain private.

The following is a **proposed interface contract**, not a claim of currently accepted Simple syntax. Freeze its actual spelling and generated ABI in work package W0.

| Operation | Stable contract |
| --- | --- |
| `capabilities()` | Supported events, targets, ABI profiles, patch modes, exact-span modes, limits, and backend diagnostics |
| `prepare(config, selection)` | Validate schema, resolve immutable selections/maps, allocate bounded resources; no partially active session on failure |
| `start(prepared)` | Activate a new generation according to the requested consistency mode; return its session handle |
| `request_stop(session)` | Close admission without blocking the calling hook; idempotent |
| `drain(session, deadline)` | Wait for this generation's admitted work and buffered output; return completion or an explicit timeout/state |
| `poll(session, output)` | Read canonical events without exposing backend records |
| `flush(session, deadline)` | Request bounded delivery of already collected records; separate from stopping execution |
| `stats(session)` | Counts, loss, transitions, unsupported sites, queue high-water marks, and errors |
| `release(session)` | Release a drained logical handle; never imply executable/provider unload |

Use opaque handles with incarnation/generation checks. For a cross-language ABI, provide fixed-width scalars, explicitly sized/versioned structures, reserved fields, and validated caller buffer lengths. Do not export a compiler-dependent struct layout merely because its fields happen to be the same today.

Baseline: one process-wide capture session. A conflicting request returns `Busy`; readers may share the session according to the ownership contract. Multiple concurrent independent sessions are not needed to complete these stages.

Stable failure classes include `UnsupportedTarget`, `UnsupportedProfile`, `UnsupportedConsistency`, `InstrumentationAbsent`, `InvalidMap`, `Busy`, `ResourceExhausted`, `TimedOut`, and `BackendFailure`. Disabled/unsupported instrumentation must not report a misleading successful capture.

### 5.2 What “no interface changes” means

| Surface | Stage 1 | Stage 2 | Stage 3 |
| --- | --- | --- | --- |
| Application imports and calls | Simple V1 | Same | Same |
| Aspect trace extension and selectors | V1 | Same | Same |
| Session/status semantics | V1 | Same | Same |
| Canonical event/metadata format | V1 | Same | Same |
| Backend implementation | LLVM adapter, Linux only | Simple native, Linux | Simple native, Windows |
| Platform leaves | POSIX | POSIX | Win32 |
| Emitted sled/object format | LLVM-private | Simple-private | Simple-private / COFF |

The source API and event contract stay unchanged. **Existing binaries need not contain interchangeable sled encodings.** Changing the emitter/backend may require rebuilding instrumented objects. The build ID and private sled-ABI version detect a mismatch instead of trying to patch incompatible bytes.

Changing a capability result from unsupported to supported is expected evolution, not an interface change. Existing `AspectParamsV1` fields remain intact; carry the new configuration in a named, versioned extension, for example `simple.trace/observer-v1`.

### 5.3 Configuration and backend selection

Use the repository's SDN configuration machinery; freeze names during W0. Illustrative keys:

| Key | Meaning | Conservative default |
| --- | --- | --- |
| `trace.instrumentation` | `off`, `dynamic`, or explicitly supported always-on mode | `off` for release and Windows stages 1–2 |
| `trace.backend` | `auto`, `llvm`, `simple`, `none` | Target-resolved at build time |
| `trace.events` | Entry, exit, tail-exit and separately declared typed events | Function events only |
| `trace.consistency` | `raw_edges` or qualified `paired_spans` | `raw_edges` |
| `trace.patch_mode` | `quiescent` or qualified `live` | `quiescent` for unqualified native targets |
| `trace.abi_profile` | Compiler-emitted state-preservation profile | Reject if not qualified |
| `trace.buffers`, `trace.max_depth` | Bounded storage and invocation bookkeeping | Explicit limits; no hidden unbounded growth |

Backend selection occurs before backend-specific imports/dependencies are evaluated. Runtime capability discovery does not require linking every platform backend into every binary.

### 5.4 Canonical event and identity rules

Records contain a schema version/record size, event kind, flags, session generation, module instance, dense local function/site ID, logical execution-context ID, sequence, timestamp, and a reserved span-token field. The span token is present in V1 from stage 1 and is zero/invalid in raw mode. Predeclare paired, transition, loss, unmatched-edge, and truncation variants in the V1 tagged-record format; later capability enablement must not silently append fields. Cold metadata describes clocks and canonical source/function identities; avoid repeating long hashes/names on every event.

Separate:

- **Build identity:** exact executable/module build and instrumentation format.
- **Module instance identity:** one resident loaded image in this process; never just a pathname.
- **Local function/site identity:** compact, checked index into that module's manifest.
- **Canonical semantic identity:** module/namespace, symbol/signature, generic instantiation, and relevant source identity for cross-build analysis.

XXH3-128 can accelerate lookup, but equality must be checked against canonical data when collision matters. Never equate a hash collision with the same function. LLVM IDs remain adapter-private and are translated once into the canonical map.

The default observable entity is a **physical emitted function**, not every source-level call erased by inlining. An optimized-out or inlined function may have no independent boundary. Report coverage honestly. A later source-inline tracing mode must be an explicit capability, not a silent semantic change between stages.

Use explicit transition, loss, unmatched-edge, truncated-span, and unsupported-site records. Provide per-context order; do not invent a total order across cores from unrelated raw timestamp counters. The common clock layer defines conversion and monotonicity guarantees.

## 6. Shared core and SOSIX split

| Component | Shared responsibility | Platform/ISA-specific portion |
| --- | --- | --- |
| Facade and schema | V1 calls, validation, statuses, canonical records | None |
| Selection planner | Resolve pointcuts, module/function sets, directory/layer metadata | None |
| Session engine | Generations, admission, bounded resources, drain states | Atomic/park primitives underneath |
| Collector | Reentrancy guard, fixed-size records, bounded rings, loss accounting | Fast context/clock access where required |
| Native patch manager | Plans, ownership, map validation, failure state machine | Atomic instruction switch, cache synchronization, protection leaves |
| Trampoline | Common callback semantics | ISA, OS ABI, saved state, call/return protocol |
| Module-map provider | Validated manifest model | ELF or PE/COFF relocation/registration |
| SOSIX host leaves | Stable internal service contract | POSIX calls or Windows calls |

The native runtime/core should live in Simple's `nogc` substrate. Only irreducible assembly/intrinsics and OS bindings remain leaves. The Linux and Windows implementations must not duplicate pointcut evaluation, event encoding, generation logic, or ring-buffer algorithms.

Proposed internal host services cover page-range validation, protection transactions, instruction-stream synchronization, module registration, atomics, waiting, context hooks, and monotonic time. They are not general-purpose unvalidated arbitrary-address patch APIs exposed to application code.

POSIX and Windows leaves may have different implementations. `mprotect` alone is not a universal instruction-cache synchronization operation. Windows code modification uses `FlushInstructionCache`, checking its result. An existing x86 no-op cache helper elsewhere in the repository is not sufficient evidence for the new cross-platform code-patching contract. [S5]

Preserve observable thread error state such as `errno` and Win32 last-error if the callback can touch it. Prefer a collector that calls no OS service on the hot path; initialize buffers/context before admitting the workload.

## 7. Stage 1 — Linux LLVM XRay behind the frozen facade

### Deliverables

1. V1 facade, canonical metadata/events, bounded collector, and common session tests.
2. A private Linux LLVM-XRay adapter with a pinned, qualified compiler/runtime combination.
3. Simple compiler attributes/selection lowering that generate LLVM XRay instrumentation where supported.
4. An explicit Linux-only hosted runtime dependency; no change to SimpleOS's builtins-only compiler-rt configuration.
5. Target-profile and error handling before a session is admitted.

LLVM XRay provides compiler instrumentation plus runtime handler/patch interfaces; its documented build options and attributes are the stage-1 integration point. Use its instrumented function map privately. A basic/FDR log is not the public Simple log contract. [S1]

### Handler policy

The handler registered with LLVM is an internal adapter/shim, not an arbitrary application callback. It performs the qualified preservation work and writes a bounded canonical event. It must not recursively instrument itself, allocate, format strings, acquire loader locks, invoke arbitrary aspects, or flush files.

Do not assume the upstream trampoline preserves every possible extended CPU state. The reviewed x64 source saves XMM state, not a general YMM/ZMM/FP-environment snapshot. One implementable no-fork remedy is a profile-specific assembly handler shim that saves additional state before entering C/Simple code and restores it afterward. Qualify the complete pinned upstream path, including instructions executed before the shim; a shim cannot recover state already destroyed before it is entered. [S2]

This remedy is a stage-1 implementation task. The native Windows prototype's vector regression is not evidence that this Linux LLVM-handler shim has already been implemented or tested.

### Stage-1 completion gate

- Real Simple-generated Linux binaries run through the facade, not only C fixtures.
- Mapping, event semantics, error/status behavior, recursion suppression, loss accounting, and normal shutdown pass.
- Each admitted ABI/ISA profile passes argument/return/FP-state tests with an adversarial conforming handler.
- The selected upstream patch path is qualified for its platform; otherwise expose only startup/quiescent activation.
- Windows default compile commands, imports, dependencies, and tracing-off artifacts remain equivalent to baseline.

Linux AArch64 is a separate qualification target. A passing Linux x86-64 adapter does not automatically qualify it.

## 8. Stage 2 — Linux Simple-owned implementation

Replace only the adapter and instrumentation backend. Keep the facade, event schema, metadata model, selection planner, collection, and session semantics from stage 1.

### Required ownership

- Simple owns its sled/descriptor ABI and emitter integration.
- Simple owns patch planning, activation, generation state, and collection.
- Simple owns trampolines and the supported preservation profiles.
- Linux uses SOSIX POSIX-backed leaves.
- LLVM may still be the compiler/code generator; LLVM's XRay runtime is no longer linked.

A temporary implementation that reads LLVM sleds with a Simple runtime is a useful bring-up substage. It is **not completion** of the full Simple-owned emitter design. If supported, identify it as a separate private backend and retain exact version checks.

### Two implementation routes

1. **Conservative bridge:** use legal LLVM inline assembly or a controlled low-level emission seam, with precise constraints, side effects, unique per-emission labels, and explicit stack/red-zone rules. Initially isolate selected functions from unsupported inlining/LTO transformations. The existing COFF fixtures establish that custom slots can be emitted with stock LLVM; they are not yet the production emitter.
2. **Full optimizer-integrated route:** lower semantic site intent into late backend patchpoint/pseudo instructions and emit bytes plus metadata together after final transformations. This can be a Simple backend implementation or a maintained LLVM backend extension where needed.

The first route avoids making an LLVM fork the initial prerequisite. The second is engineering work required if full optimizer integration cannot be guaranteed by the selected bridge. Neither route asks a linker to discover arbitrary function boundaries from bytes.

### Stage-2 completion gate

- Differential tests: equivalent canonical observations against stage 1 for the same declared physical-function coverage and workload.
- No LLVM XRay runtime symbols/archive in a Simple-native binary.
- All emitter, map, lifetime, patching, and ABI gates pass on the declared Linux targets.
- The same client binary interface/schema tests pass with both adapters.
- Windows remains tracing-off and free of the new Linux runtime/build dependencies.

Retain the LLVM adapter as a build-selectable fallback while the native backend matures. Do not switch a live module from one incompatible sled ABI to another.

## 9. Stage 3 — Windows Simple-owned implementation

Reuse stage 2's common core, selection, session logic, canonical formats, and as much ISA logic as valid. Add Windows ABI profiles, PE/COFF map registration, and SOSIX Windows-backed memory/synchronization leaves.

### Toolchain policy

The tested path uses Clang-produced COFF objects/assembly with the native Windows toolchain. Do not assume changing a build to MinGW makes upstream LLVM XRay a supported Windows runtime. MinGW is an optional additional toolchain profile that must pass the same ABI, relocation, mitigation, and runtime tests; it is not the architecture solution.

No Clang Windows XRay feature port is mandatory for the Simple-owned route. Simple can emit its own valid slot descriptions/assembly into the object pipeline. If later adopting LLVM's own XRay machinery on Windows, that becomes a separate upstream/runtime-port project, not an implicit stage-3 requirement.

### Windows x64

- Preserve the original function's live admitted state, not just what an ordinary callback promises to preserve.
- Respect Windows stack alignment and shadow space.
- Use real `CALL`/`RET` pairing. Do not synthesize a return address with a push/jump sequence or rewrite the application's return address as a tracing trick.
- Compile genuine indirect C/C++ dispatch sites with CFG support and link the corresponding metadata. An assembly indirect branch does not gain checks merely from a linker flag.
- Prefer direct calls to resident trampolines and a resident typed dispatcher.
- Treat CET compatibility-mode execution, strict-mode qualification, and negative enforcement proof as distinct evidence.

The Microsoft ABI makes upper vector lanes volatile across ordinary calls; instrumentation inserted into a function cannot infer that those lanes are dead at its insertion point. This is the reason for the vector-preservation gate. [S3]

### Windows ARM64

- Preserve original LR and the admitted integer/vector/FP state; keep SP aligned.
- Do not use platform-reserved x18 as scratch.
- Preserve x16/x17 before a branch that may require a linker veneer.
- Use a consistent PAC signing/authentication modifier: restore the appropriate SP before authenticating LR.
- Retain suitable branch-target landing instructions; do not claim enforcement solely from their presence.
- Test fixed-width SIMD explicitly. SVE/SME and ARM64EC are separate, initially unsupported profiles. [S4]

The existing ARM64 fixture saves Q0–31, FPCR, FPSR, NZCV and relevant integer/LR state. Its scalar arithmetic test does not replace a native register-snapshot regression.

### Stage-3 completion gate

Native Windows x64 and ARM64 each pass their complete declared profile. Shared code from Linux does not waive native Windows validation. Public interface/schema conformance and the existing nontracing Windows build remain unchanged.

## 10. Sled generation, ABI profiles, and linker responsibilities

### 10.1 Where the slots are created

Create slots while generating object code, with corresponding metadata produced from the same emission. The compiler knows entry/exit/tail semantics and live-state constraints. The linker retains, relocates, folds or rejects according to a declared contract, and checks the final layout.

**Do not ask the linker to blindly insert NOPs into already optimized arbitrary code.** That would require reconstructing control flow, adjusting displacements and metadata, and proving placement rules the compiler already knows. Entry-only patchable-function options are not by themselves a complete entry/exit/map implementation.

The current inline-assembly bridge must keep its constraints true even after runtime patching. With only a memory clobber declared, the hook must preserve every other live admitted state component. Use `sideeffect`, the appropriate alignment declaration, and conservative Linux red-zone handling. LLVM supports unique inline-assembly emission identifiers; use those rather than fixture-global labels. These annotations do not by themselves pin pure arithmetic relative to a timing hook: production boundary placement needs late emission or demonstrated operand/scheduling constraints. [S6]

### 10.2 Current x64 13-byte candidate

This is a **Simple-private encoding**, not LLVM XRay binary compatibility.

| Byte offset | Disabled / immutable contents | Enabled contents |
| --- | --- | --- |
| 0–1 | `EB 0B`: skip to +13 | `66 90`: two-byte NOP |
| 2–6 | Direct `CALL rel32` to resident trampoline | Same |
| 7–8 | `EB 04`: skip embedded ID | Same |
| 9–12 | Embedded 32-bit function/site lookup ID | Same |
| 13 | Original continuation | Original continuation |

Only the aligned first 16 bits change. The trampoline reads the ID relative to the real call return address. It does not overwrite an argument/scratch register in the sled to transport the ID. The old 11-byte prototype that used R10 for this purpose is not the selected design.

The entire payload/branch target is finalized before any worker can enter it. Runtime retargeting of the embedded call displacement is not part of activation; change an immutable, safely published dispatcher configuration instead.

### 10.3 Current ARM64 32-byte candidate

| Byte offset | Operation |
| --- | --- |
| 0 | Aligned 32-bit `B +32` while off; `NOP` while on |
| 4 | Save x16/x17 |
| 8 | Save x0/x30 |
| 12, 16 | Materialize the ID into w0 |
| 20 | `BL` resident trampoline |
| 24 | Restore x0/x30 |
| 28 | Restore x16/x17 |
| 32 | Original continuation |

Only the first instruction is changed during activation. The preserved scratch registers also protect against an otherwise valid range-extension veneer clobbering them.

### 10.4 Preserved-state policy

Do not call arbitrary plugin code directly from the hidden machine hook. The default hook invokes only the audited internal collector. More expressive aspects consume deferred records or use an independently specified synchronous advice mechanism.

Initial x64 native profile: ordinary Windows x64 convention, qualified GPR/RFLAGS handling, full YMM0–15 and MXCSR preservation, and CPU plus OS-enabled AVX state. Select the trampoline at initialization, not by CPUID on every callback. A non-AVX machine needs a separately qualified SSE/FP-state profile; it must not execute AVX instructions speculatively as a supposed universal baseline.

Stage-2 Linux x86-64 uses a **separate SysV AMD64 profile**: its caller-saved integer set, stack-call rules, and red-zone treatment differ from Windows. In particular, the Windows-style preservation fixture is not a qualification of a SysV trampoline. Share state-layout/emission logic only where the ABI rules actually match; validate the Linux argument/result and vector/FP profiles independently.

Extended profiles have two valid routes:

- Compiler-aware saves/restores from a declared live-state/clobber contract.
- An independently validated extended-state save implementation, using the actual CPUID/XCR0-supported layout, alignment, mask, buffer size, stack-probing/reentrancy rules, and restore semantics.

“Use XSAVE” is not itself a proof. Do not allocate an assumed fixed-size area for every future CPU state. Reject AVX-512/opmask, AMX, APX, x87/MMX, SVE/SME, and special conventions until their admitted state is preserved or the entire callback chain is mechanically proven not to touch it.

### 10.5 Optimization and relocation checklist

- Preserve entry before observable body execution and exit after the result exists, at ABI-correct stack positions.
- Emit `TAIL_EXIT` before a tail transfer. Never insert between LLVM `musttail` and its required `ret`.
- Cover every supported ordinary return path; report noreturn functions correctly.
- Do not assume `sideeffect` means no duplication, no cloning, or no inlining.
- Bind map records to actual emitted copies. Associate them with COMDAT/section lifetime so discarded functions do not leave patchable dangling records.
- Disable identical-code folding for selected functions initially, or represent aliases explicitly. One address cannot silently mean two incompatible identities.
- Retain manifest roots through dead stripping; validate after LTO and linking.
- Check x64 direct-call reach and ARM64 branch reach; use validated nearby islands/veneers or reject an out-of-range site. No displacement truncation.
- Test full and thin LTO separately. Conservative no-LTO/no-inline islands are an acceptable initial limitation, not a claim that full LTO is already supported.
- Scope sanitizer/instrumentation ordering; exclude hooks, collectors, allocators used by tracing, and patch control code from recursive instrumentation.

## 11. Function maps and executable-memory access

### Map design

Use one read-only resident module manifest containing a format version, target/ABI profile, build identity, section bounds, function table, and site table. Each site identifies its kind, physical address/relocation, length, alignment, expected off/on switch values, immutable template, and owning function.

ELF and PE/COFF use their appropriate relocation/section-retention mechanisms. Register manifests explicitly at safe startup or controlled module load. In PE, derive addresses from the loaded image and validated RVAs/relocations, not file offsets. ASLR must not change semantic identities. [S7]

### Validation before patching

1. Check version, target, profile, counts, size arithmetic, and image ownership.
2. Ensure each site lies entirely within the expected executable image range and cannot overflow address arithmetic.
3. Check patch-word alignment and ensure it does not straddle an unsupported boundary.
4. Validate expected original bytes and immutable payload; reject an unexpected patch owner.
5. Resolve and range-check every branch target.
6. Check dense ID bounds, duplicate sites, aliases, map/table retention, and canonical identity collisions.
7. Publish the immutable validated manifest only after all checks succeed.

Executable-memory “fetch” is bounded inspection of known sites in a registered image. Do not scan arbitrary process pages for a byte pattern, infer functions from symbol names alone, or use SEH to turn arbitrary invalid reads into normal control flow. Current resident-image ownership and bounds are the safety preconditions.

Debug names/PDB/DWARF may enrich offline decoding; runtime patch correctness must not depend on debug files being present.

## 12. Concurrent patch/unpatch and consistency

### 12.1 Three independent guarantees

| Problem | Required control | What it does not prove |
| --- | --- | --- |
| Instruction integrity | Immutable sled payload plus qualified atomic switch/cache protocol | Exact paired spans or callback lifetime |
| Handler/data lifetime | Resident code/maps plus generation-bound admission/drain | Globally simultaneous updates to all sites |
| Semantic session consistency | Boundary protocol and per-invocation bookkeeping | Hardware instruction-fetch correctness |

One atomic store changes one site. It does not atomically switch all entries/exits in a module or stop every core at one timestamp.

### 12.2 Native patch transaction

Use one serialized control-plane owner per module and a shared page-range protection owner. Concurrent enable/disable callers queue or receive `Busy`; hooks do not take this lock.

1. Resolve a fully validated immutable patch plan.
2. Prepare the handler generation, buffers, map references, and collector before any site can reach them.
3. Obtain the required patch mode: proven execution quiescence, or a qualified live-patch platform capability.
4. Record original page protections and acquire exact page-range ownership. Do not remove execute permission from pages currently being executed in a live-patch mode.
5. Change only the aligned activation word using the backend's exact supported atomic operation.
6. Apply the platform's instruction-stream synchronization protocol and check every result.
7. Restore protections on every exit path and verify the transaction outcome.
8. Publish completion and a transition marker only after the required synchronization completes.

The Windows prototype used `InterlockedExchange16`/`InterlockedExchange` and `FlushInstructionCache` while the selected code region remained executable. It is evidence for that experiment, not a blanket authorization to keep arbitrary text writable or to omit page restoration in production.

**Important:** C/C++ data-race freedom or a release store is not, by itself, an instruction-fetch specification. Qualify the relevant ISA/OS code-modification protocol. Retaining code and allowing either old or new behavior makes stale execution safe at the semantic level, but does not excuse a possible torn instruction stream.

The always-available safe design option is **startup or SOSIX-established quiescent patching**. Quiescence must prevent execution from entering the target region, including uncontrolled foreign threads or signal handlers. If that boundary cannot be established and live patching is not qualified, return `Unsupported`/`Busy`. Do not suspend arbitrary threads while holding loader/runtime locks as an improvised substitute.

This separates a solvable engineering qualification task from an alleged fundamental impossibility. Live patching remains independently enabled per target profile.

### 12.3 Failure and rollback

On a partial patch failure, immediately close admission. Keep all handlers/maps resident. Track the exact installed state of each site; do not report the module as fully off because a later store failed.

Attempt a controlled rollback only through the same validated patch protocol. If restoration or cache synchronization fails, leave the session in a faulted/closed state and expose diagnostics. Do not reclaim reachable state. For a host failure that prevents any safe continuation guarantee, fail-fast is preferable to claiming success and continuing with unknown code/protections.

Host policy denial is not the design's assumed blocker, but API failures still require correct handling.

### 12.4 Raw-edge mode: universal V1 baseline

Raw mode records the edges actually observed, with generation/transition markers. An exit without a recorded entry, or an entry without a later exit, is allowed around activation boundaries and loss. Consumers must not synthesize certainty from these gaps.

Admission and in-flight reservations need a single proved linearization protocol. A packed atomic state/CAS or equivalent validated implementation can combine closed/generation/reservation state; separate “check open, then increment” operations are not sufficient without a race proof.

Each callback reserves the generation before using its resources, publishes a complete event, and releases its reservation. Stop closes new admission and drains existing reservations/buffers. Old site execution may still reach the resident closed dispatcher and safely produce no event.

The dispatcher and gate/descriptor storage remain resident or tombstoned. Reclaim a buffer only after the closed gate prevents new references and all existing reservations are gone. Do not recycle the address of a descriptor still observable by a late reader; logical handle release is not permission to create an ABA/use-after-free race.

### 12.5 Exact paired spans: stronger optional capability

Do not implement general spans with one thread-local token. Recursive calls, nested selected functions, rejected entries, old uninstrumented frames, and fibers make that incorrect.

Admit exact mode only under one of these contracts:

- **Quiescent task-root activation:** all relevant roots are outside instrumented frames, future roots pass a controlled admission barrier, and selected hooks become observable before those roots run.
- **Resident pre-armed hooks:** hooks were installed before relevant work began, and every relevant invocation, including rejected entries, has bookkeeping until it returns.

Required implementation:

1. Per-logical-context invocation stack with unique tokens and explicit rejected-entry sentinels.
2. Context belongs to the fiber/task when execution migrates; a native thread-local ring is only transport.
3. Tokens bind a frame to its original generation; exit does not guess from the currently active generation.
4. On stop, close new admission but retain required exit hooks and invocation bookkeeping until relevant frames drain.
5. Nested calls after admission closes still need rejected markers when their exits could otherwise pop an admitted parent.
6. Handle tail-exit as a terminal edge with defined depth semantics.
7. Detect maximum depth/queue exhaustion; mark loss/truncation or reject exact guarantees, never silently mispair.
8. Never reuse a generation/incarnation while a stale token can refer to it; fail explicitly at counter exhaustion.

An admission count reaching zero does not by itself prove that no unadmitted frame will execute an exit. Physical unpatching requires the relevant quiescence condition. It is safe to leave hooks armed with admission closed until such a condition exists.

`drain` timeout returns `TimedOut` with state still `Draining`; it does not release live resources. A stop/drain request from inside its own callback is deferred or returns `Busy` rather than deadlocking on itself.

## 13. Security, SEH, and process exit

### SEH and unwind

The normal implementation does not require SEH handlers for activation or event delivery. It uses compiler-created slots, validated maps, normal calls/returns, and OS memory APIs. Adding a dynamic exception handler is not the central difficulty; using exceptions to repair arbitrary partial instruction states would add unnecessary complexity here.

No language-level unwind support is introduced. State that external unwinding/stack walking through these frames is outside the initial contract. If it is later required, add and test static/dynamic unwind metadata as a separate capability without changing the V1 tracing interface. Do not claim that absence of language exceptions automatically makes metadata irrelevant to every Windows diagnostic tool.

### CFG, CET, PAC, and BTI

| Mechanism | Design treatment | Evidence needed for the corresponding claim |
| --- | --- | --- |
| CFG | Prefer direct trampoline calls; instrument real indirect dispatch; register dynamically generated targets only where necessary | Policy + binary/callsite inspection + valid-target success + recognized invalid-target rejection |
| x64 CET shadow stack | Real balanced calls/returns; no forged return slots | Policy distinguishes enabled/audit/strict; positive trampoline run; negative return test |
| ARM64 PAC | Correct LR sign/authentication lifecycle and SP modifier | Enabled user-pointer-auth policy; positive signed return; recognized wrong-modifier rejection; actual trampoline under the same policy |
| BTI/IBT landing compatibility | Keep appropriate landing instructions where applicable | Actual supported OS enable/query mechanism and enforcement test before claiming enforcement |

Microsoft exposes user shadow-stack policy fields separately for enable, audit, and strict mode. It also defines `ProcessUserPointerAuthPolicy` and `EnablePointerAuthUserIp`; use official SDK definitions, not guessed feature numbers. [S8–S10]

The PE specification says its forward-CFI compatibility marker for IBT/BTI is not used by Windows. That does **not** prove every possible present/future mechanism absent. It does mean an assumed generic “Windows BTI policy” must not be invented as a mandatory blocker. Qualify a BTI-specific gate only when the actual supported target exposes the relevant mechanism. [S7]

The negative tests run deliberately invalid transfers only inside short-lived test child processes. They do not add SEH to the Simple runtime or change system-wide policy. A generic crash is not a successful enforcement result. Applicable positive controls and diagnostic classification are required.

### Dynamic providers without unload

Load and validate a provider on the control path; publish an immutable descriptor only after preparation. Keep its code and referenced data resident. Unregistering observation means closing admission and draining logical references, not unmapping the DLL/code.

Bound the number of retained generations/providers; “no unload” must not become unlimited memory growth. A full bound returns `ResourceExhausted`. Existing loader signing/capability checks remain separate and are not bypassed.

### Exit behavior

For normal process shutdown: close admission, request task completion, drain within a deadline, flush on a non-hook path, then release logical resources. Avoid blocking or substantial loader work inside `DllMain`, loader-lock callbacks, or destructors with uncontrolled ordering.

Forced termination, fatal hardware exceptions, power loss, and `TerminateProcess` cannot promise complete buffered output. Records include completion/loss markers so a reader recognizes an incomplete trace. This is an explicit delivery limit, not a reason to require unwind support.

## 14. Hot-path collection and aspect integration

Resolve path/layer/feature pointcuts at prepare/start time into immutable site selections and metadata. Do not hash directory strings, traverse trees, or interpret pointcuts on every function entry.

Use fixed-size per-thread transport rings with bounded, preinitialized context bookkeeping. Publish records with a defined producer/consumer protocol. Recursion guards exclude tracing internals; overflow increments checked loss counters and emits a gap marker when capacity permits. Test reentrant signals separately: suppress and count them unless a qualified signal-safe path exists.

Application/aspect behavior such as folder-boundary logs, depth logs, timing aggregation, and function-map decoding runs in deferred consumers by default. Synchronous observers require an explicit bounded, no-throw, no-allocation, no-reentry contract; they are not arbitrary plugins attached to a hidden trampoline.

Exact depth logs require qualified paired-span mode. A raw-mode consumer marks depth unknown after an unmatched edge or loss until an explicit resynchronization boundary; it must not guess a balanced stack from incomplete records.

Function entry/exit alone does not reveal every memory allocation, free, or data write. Memory profiling requires separate typed allocation/free/access instrumentation with compatible identities and event schema. Do not promise allocation attribution from function tracing alone.

An uninstrumented build removes sites, maps, initialization, and trace dependencies. An instrumented-but-disabled build still has branch/slot/code-layout costs. Call this low-overhead disabled instrumentation, not mathematically zero overhead.

Measure wall time, cycles/event, code size, cache effects, buffer memory, initialization, patch latency, and drain latency against a noninstrumented baseline. No overhead percentage is established by the existing billion-call stress counts.

## 15. Minimize Windows build impact during stages 1 and 2

This is a release constraint, not merely a preference.

| Area | Stage-1/2 rule | Verification |
| --- | --- | --- |
| Default Windows configuration | Tracing remains off | Configuration snapshot/golden test |
| Dependency resolution | Linux LLVM XRay/native POSIX leaves excluded before import/build evaluation | Build-DAG/dependency diff |
| Compiler flags | No new `-fxray-*`, tracing macros, forced assembler flags, or global target-feature changes | Compile-command diff |
| Link flags/libraries | No XRay/compiler-rt tracing archive, ELF section symbols, new startup library, or unconditional trace export | Link-command/import/export diff |
| Toolchain | No unrelated Windows LLVM/SDK/MinGW upgrade | Existing pinned toolchain remains authoritative |
| SimpleOS compiler-rt | Keep its freestanding XRay-OFF configuration | File/config regression check |
| Initialization | No trace TLS initializer, background thread, map scan, or handler registration in tracing-off binaries | Section/symbol/startup inspection |
| Common facade | Existing users unchanged; explicit unsupported requests return a stable error | Interface contract tests |
| Object cache | Trace settings enter keys only where they affect emission; target/ABI separation preserved | Cache hit/invalidation tests |
| CI | Linux-only leaf changes do not require a new full Windows bootstrap | Path/dependency-scoped lane selection |

When shared schema/core/lowering changes, run a narrow Windows tracing-off smoke test and interface check. Do not eliminate existing mandatory project gates. Keep experimental native Windows XRay qualification in a distinct opt-in/path-scoped workflow until stage 3.

Compare reproducible objects/binaries where supported; otherwise normalize timestamps and compare commands, sections, imports/exports, code, and dependency graphs. Do not demand identical whole-PE hashes when the build embeds changing timestamps.

Stage 2 must not secretly begin a mandatory Windows implementation. Keep Windows-specific assembly, SDK imports, and host leaves behind the stage-3 target feature. The existing dedicated proof PR may validate experiments without adding a dependency to normal Windows application builds.

## 16. Work packages and release gates

### 16.1 Implementation sequence

| Package | Work | Completion evidence |
| --- | --- | --- |
| W0 | Freeze V1 facade, statuses, metadata, event semantics, SDN keys, and unsupported behavior | Golden schema/API tests; old `AspectParamsV1` compatibility |
| W1 | Implement bounded collector and common lifecycle/session core | Model/unit/stress tests, recursion/loss/deadline tests |
| W2 | Implement hosted Linux LLVM adapter and state-preserving handler shim | Real Simple-generated Linux integration; profile-specific ABI tests |
| W3 | Prove Windows tracing-off build isolation | Command/dependency/artifact comparison with baseline |
| W4 | Implement native map format, emitter bridge, and Linux host patch leaves | Object inspection, malformed-map rejection, quiescent execution |
| W5 | Qualify native Linux patching/ABI/LTO subset; differential test stage 1 | Stage-2 conformance and no LLVM-XRay runtime dependency |
| W6 | Add Windows host/COFF and x64/ARM64 profiles | Independent native profile qualification |
| W7 | Broaden LTO/ABI/ISA/live-patching support incrementally | New capability only after its own gates pass |

Proposed new modules should follow the repository's layer ownership: a common tracing contract/core, private backend adapters, compiler site intent/emission, and SOSIX host leaves. Do not place Win32 code in the public facade or a Linux dependency in common initialization.

### 16.2 Acceptance matrix

| Gate | Required test | Stages |
| --- | --- | --- |
| API-01 | Same client source/ABI and canonical reader across all backends | 1, 2, 3 |
| WIN-OFF-01 | No Windows default dependency/flag/startup regression | 1, 2; retain in 3 |
| ABI-01 | Integer, float, vector arguments/returns, aggregates, flags, stack alignment, error-state preservation | Every admitted target/profile |
| ABI-02 | Adversarial handler clobbers every state component allowed by its ABI | Every admitted target/profile |
| EMIT-01 | Multiple returns, tail calls, recursion, generic instantiations, thunks, no-return, red-zone/stack-probe cases | 1, 2, 3 |
| OPT-01 | O0/O2/O3 and separately no-LTO/full-LTO/ThinLTO; supported inlining/cloning/COMDAT/ICF modes | Each advertised mode |
| MAP-01 | ASLR, stripped images, section GC, malformed/corrupt map, duplicate IDs/sites, many modules | 1 adapter and 2/3 native |
| RANGE-01 | Branch-limit boundaries and deliberate out-of-range images; correct veneer or explicit failure | 2, 3 |
| PATCH-01 | Concurrent callers plus controller; site integrity, result/state snapshots, transition accounting | Qualified live modes |
| PATCH-02 | Inject protection/flush/write/restore failures at each step; closed safe state and truthful status | 2, 3 |
| LIFE-01 | Admission-close race, late callback, stale token, generation exhaustion, stop inside callback | Common core |
| SPAN-01 | Nested admitted/rejected calls, recursion, old frames, tail exits, fiber migration, depth overflow | Before paired mode is advertised |
| BUF-01 | Ring overflow, slow consumer, reentrancy, allocation prohibition, ordering and loss markers | Common collector |
| MIT-01 | Actual policies + positive and recognized negative CFG/CET/PAC controls, as applicable | Windows supported protection profiles |
| EXIT-01 | Normal exit, deadline expiry, forced termination, partial-record reader recovery | All |
| PERF-01 | Off/static/dynamic cost, code size, memory, patch/drain latency; measured budgets | Before default enable |
| TOOL-01 | CLI/profiler/AOP/LSP decode the same metadata and report incomplete coverage/loss | All |

ABI tests include the current expected-failure baseline to prevent accidentally “fixing” the regression by making the handler less adversarial. A skipped ISA test is unavailable evidence, not a pass for that profile.

Use the same acceptance scenarios for all three backends. Architecture-specific expected bytes and policy fields belong in target fixtures, not duplicated semantic tests. Native tests are required for runtime claims; cross-build/disassembly jobs remain valuable earlier checks.

### 16.3 Formal/model checks versus execution tests

Model the control-plane state machine, generation-bound admission, drain, and per-invocation stack rules. Check invariants including no use of an uninitialized generation, no release while reserved, no token reassignment, and truthful timeout states. Tie the model to actual transition functions/tests rather than proving a disconnected simplified algorithm.

Formal checks do not prove an assembler encoding, compiler transformation, OS cache API, or hardware mitigation implementation. Those require object inspection and native execution. Conversely, a long stress run does not replace a race argument.

## 17. Risk register and rollout decision

| Subject | Classification | Concrete solution/control | Release condition |
| --- | --- | --- | --- |
| Windows scalar sled feasibility | Demonstrated for the fixture | Retain native x64/ARM64 tests | Do not generalize beyond tested scope |
| x64 vector/FP-state loss | Reproduced defect in initial prototype | Bounded full-YMM/MXCSR preservation; reject uncovered profiles | ABI-01/02 on actual backend |
| Linux LLVM handler extended state | Implementation/qualification work | Qualified preservation shim plus pinned upstream path audit | Real Linux adapter tests |
| SEH/unwind | Explicitly outside initial contract | No exception-based patching; normal ABI-correct calls | No claim of cross-trampoline unwinding |
| Hot unload | Removed from scope | Process-resident code/maps/providers; bounded generations | No premature freeing |
| Host security permission | Assumed available, not research blocker | Respect failures and report them | No bypass or silent success |
| CFG/CET/PAC enforcement | Positive/negative self-tests passed on native hosts; not inferred from flags | Retain isolated tests and capture policies in each actual instrumented executable | Matching supported profile; strict CET is a separate gate |
| BTI policy assumption | Not an established general Windows requirement | Do not invent a policy; retain compatible landing instructions | Conditional gate for a real supported mechanism |
| Concurrent patching | Demonstrated stress plus remaining platform qualification | Immutable payload, serialized control, exact switch/cache protocol; quiescent fallback | PATCH-01/02 and platform review |
| Exact span consistency | Flat-token approach insufficient | Controlled roots or pre-armed hooks; per-context admitted/rejected frame stack | SPAN-01; otherwise raw mode only |
| Function maps/large images | Ordinary but substantial implementation | Linked manifest validation, ASLR/GC/COMDAT/range tests | MAP-01/RANGE-01 |
| Optimizer/LTO integration | Substantial implementation, not proven by fixture | Late emission or conservative islands, unique site IDs, explicit supported modes | EMIT-01/OPT-01 |
| Windows build disturbance | Avoidable integration risk | Target-local graph, off defaults, no global compiler-rt change | WIN-OFF-01 |
| Forced-exit delivery | Inherent bounded-buffer limitation | Explicit incomplete/loss records and best-effort shutdown | Reader never claims a complete trace |

This distinguishes **a known defect**, **an implementation task with a concrete method**, **a hardware/toolchain qualification task**, and **an intentionally unsupported feature**. They must not all be described as mysterious unresolved research problems.

Roll out by opt-in build/profile. Keep stage-1 Linux LLVM available until stage 2 passes equivalent conformance. Keep Windows native tracing opt-in until stage 3 is qualified. On an unsupported configuration, reject the requested capability or use a fallback the caller explicitly allowed; do not silently degrade exact spans into raw edges or silently turn tracing off.

**Final answer to “all dangers cleared?”:** no universal claim is justified. The architecture has a practical implementation route, verified native feasibility, a reproduced ABI defect with a bounded remedy, and explicit controls/tests for remaining integration risks. The staged plan can proceed without changing the public interface and without making Windows pay the Linux integration cost.

## 18. Sources and reproducibility

Primary technical sources were checked on 2026-11-03. Implementation decisions in this document are design proposals unless identified as existing code or executed tests.

- **S1:** [LLVM XRay documentation](https://llvm.org/docs/XRay.html).
- **S2:** [LLVM x86-64 XRay trampoline source](https://github.com/llvm/llvm-project/blob/main/compiler-rt/lib/xray/xray_trampoline_x86_64.S). Pin the implementation revision in the build; this moving source URL is not a version lock.
- **S3:** [Microsoft x64 calling convention](https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention?view=msvc-170).
- **S4:** [Microsoft Windows ARM64 ABI](https://learn.microsoft.com/en-us/cpp/build/arm64-windows-abi-conventions?view=msvc-170).
- **S5:** [Microsoft FlushInstructionCache](https://learn.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-flushinstructioncache).
- **S6:** [LLVM inline assembly](https://llvm.org/docs/LangRef.html#inline-assembler-expressions) and [call/musttail restrictions](https://llvm.org/docs/LangRef.html#call-instruction).
- **S7:** [Microsoft PE/COFF specification](https://learn.microsoft.com/en-us/windows/win32/debug/pe-format).
- **S8:** [User shadow-stack policy](https://learn.microsoft.com/en-us/windows/win32/api/winnt/ns-winnt-process_mitigation_user_shadow_stack_policy).
- **S9:** [Process mitigation policy enum](https://learn.microsoft.com/en-us/windows/win32/api/winnt/ne-winnt-process_mitigation_policy).
- **S10:** [User pointer-authentication policy](https://learn.microsoft.com/en-us/windows-hardware/drivers/ddi/ntddk/ns-ntddk-process_mitigation_user_pointer_auth_policy) and [Microsoft SDK header source](https://github.com/microsoft/win32metadata/blob/main/generation/WinSDK/RecompiledIdlHeaders/um/winnt.h).
- **S11:** [Control Flow Guard](https://learn.microsoft.com/en-us/windows/win32/secbp/control-flow-guard) and [SetProcessValidCallTargets](https://learn.microsoft.com/en-us/windows/win32/api/memoryapi/nf-memoryapi-setprocessvalidcalltargets).
- **S12:** [GitHub native Windows ARM64 runner availability](https://github.blog/changelog/2025-08-07-arm64-hosted-runners-for-public-repositories-are-now-generally-available/).

Pinned repository references:

- [Aspect parameter extension seam](https://github.com/ormastes/simple/blob/2425a95cc1772b5e4c4b1a4d45474f1feac4ad2d/src/lib/common/plugin/aspect_params.spl).
- [Existing MIR debug trace injection](https://github.com/ormastes/simple/blob/2425a95cc1772b5e4c4b1a4d45474f1feac4ad2d/src/compiler/50.mir/mir_debug_trace_injection.spl).
- [Existing lifecycle helper and its scope](https://github.com/ormastes/simple/blob/2425a95cc1772b5e4c4b1a4d45474f1feac4ad2d/src/lib/common/aspect_dynload_lifecycle_v1.spl).
- [Join-point pointer slots](https://github.com/ormastes/simple/blob/2425a95cc1772b5e4c4b1a4d45474f1feac4ad2d/src/compiler/99.loader/joinpoint_slots.spl).
- [SOSIX library adapter](https://github.com/ormastes/simple/blob/2425a95cc1772b5e4c4b1a4d45474f1feac4ad2d/src/os/sosix/host/library_capability_adapter.spl).
- [SOSIX dynload/memory route manifest](https://github.com/ormastes/simple/blob/2425a95cc1772b5e4c4b1a4d45474f1feac4ad2d/doc/01_research/runtime/sosix_unification/sosix_dynload_memory_route_manifest_v1_2026-09-28.md).
- [SimpleOS builtins-only compiler-rt configuration](https://github.com/ormastes/simple/blob/2425a95cc1772b5e4c4b1a4d45474f1feac4ad2d/src/os/port/llvm/compiler_rt_cmake.cmake).
- [Native verification PR](https://github.com/ormastes/simple/pull/5962) and [original passing native run](https://github.com/ormastes/simple/actions/runs/41443090162).

## 19. Final qualification addendum

This section records reviewed native regression/enforcement logs. It does not change the staged interface or the release gates above.

The first expanded run, [41553661875](https://github.com/ormastes/simple/actions/runs/41553661875), did not qualify the added checks: an assembly/C++ object filename collision broke the x64 link, and missing Windows header/type setup broke the enforcement harness compile. These were test-harness build failures, not runtime ABI or mitigation results. The next run, [41553846630](https://github.com/ormastes/simple/actions/runs/41553846630), passed native x64 ABI regression but exposed a missing import library for `SetProcessValidCallTargets`. The fixture was fixed to use the documented `WindowsApp.lib`; no normal application build dependency was changed.

### Final successful run

- **Run:** [41554579305](https://github.com/ormastes/simple/actions/runs/41554579305), both native jobs successful.
- **Commit:** [`4d36e39f08a49a23642766f09bcc692c44dde242`](https://github.com/ormastes/simple/commit/4d36e39f08a49a23642766f09bcc692c44dde242).
- **x64 job:** [125650220036](https://github.com/ormastes/simple/actions/runs/41554579305/job/125650220036).
- **ARM64 job:** [125650219654](https://github.com/ormastes/simple/actions/runs/41554579305/job/125650219654).

| Check | Reviewed result | Exact scope |
| --- | --- | --- |
| x64 original-vector regression | Expected YMM-upper/MXCSR loss reproduced | Confirms the original general-handler defect |
| x64 bounded entry/exit remedy | YMM0–15, MXCSR, tested RFLAGS, IDs/kinds/counts passed | Native Windows, AVX OS state enabled; no AVX-512 claim |
| CFG valid target, x64 and ARM64 | Both positive controls returned successfully | The tested guarded indirect callsite and registered private target |
| CFG invalid target, x64 and ARM64 | `0xc0000409`, fast-fail subcode `0x0a` (10) | Recognized CFG rejection on both hosts |
| x64 CET normal return | Positive control succeeded; enabled = 1, audit = 0, strict = 0 | Active compatibility-mode protection |
| x64 CET mismatched return | `0xc0000409`, subcode `0x39` (57) | Recognized invalid-return rejection; not strict-mode qualification |
| ARM64 PAC correct SP modifier | Positive control succeeded; user-pointer-auth policy = 1; signed LR changed | Native pointer authentication active |
| ARM64 PAC wrong SP modifier | `0xc0000409`, subcode `0x49` (73) | Recognized pointer-authentication invalid-return rejection |
| Original scalar concurrent sled test | Passed again on both architectures, zero result/ID errors | Still the original scalar fixture, not full ABI coverage |

The final scalar stress logs recorded 15,000 pair-state transition iterations on each target. x64 reported 2,655,864,352 overlapping worker calls and 2,136,599 / 2,133,832 raw entry/exit callbacks; ARM64 reported 1,086,898,560 calls and 647,738 / 638,701 raw callbacks. The disabled-path and nonbenchmark caveats from section 3.2 still apply.

The process-isolated protection self-tests and scalar trampoline tests are separate executables. The latter already logged CFG/CET, but did not log the ARM64 PAC policy in that executable. Therefore this run proves native PAC enforcement in the self-test and native execution of the PAC-containing trampoline, **not yet an independently captured per-binary policy association for that trampoline**. Add that assertion to W6 rather than hiding the distinction. BTI enforcement, strict CET, ARM64 register snapshots, generic paired spans, and the production compiler/LTO integration remain bounded qualification tasks.

All new fixtures remain in **draft PR #5962, unmerged**. The existing scalar trampoline was retained as the regression baseline; adding a passing bounded replacement fixture is not a claim that the production runtime or every original test path has already been migrated to it. No application source interface, normal Windows build, or production Simple XRay implementation was changed by these qualification experiments.
