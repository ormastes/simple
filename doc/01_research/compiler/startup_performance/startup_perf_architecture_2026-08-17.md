# Simple Startup, Aspect Loading, Interpreter, Compiler, and Loader Performance Architecture

**Research, design, implementation plan, parallel-agent guide, and Modern SSpec verification plan**
**Date:** 2026-08-17
**Repository:** `ormastes/simple`
**Inspected baseline:** `5747bdd660bb5e58ba02cc1ae928eef823595cd5`
**Status:** proposed architecture and phased implementation plan; current measurements and implementation status are explicitly separated from targets
**Revision:** v2 — adds config-driven CLI commands/options, exact option routing, and `--x<namespace>-...` provider forwarding without rebuilding `simple-core`

---

## 0. Executive decision

Simple should adopt a **Go-like absence-at-runtime rule**, a **Bun/JavaScriptCore-like low-latency tiering rule**, a **CPython-like quickening rule**, and a **Rust-like exact incremental query rule**, without replacing Simple's existing MDSOC+, SCI/provider, SMF, aspect, and multi-backend architecture.

The central decision is:

```text
CAPABILITY decides whether a component exists.
PLACEMENT decides whether it is static or dynamic.
ACTIVATION decides when a dynamic component is loaded.

capability: off | auto | on
placement:  auto | static | dynamic
activation: startup | command | first_use | hotspot | manual
```

These axes must remain independent. A capability that is available in the default `normal` profile must not therefore be loaded during `simple --help`. A dynamically replaceable optimizer must not therefore remain dynamic after a full release rebuild. An aspect that is disabled must not leave a runtime branch, pointcut table, log string, mapping, constructor, or loader lookup in the normal hot path.

### 0.1 Binding conclusions

1. **Introduce a tiny stage-0 launcher.** It classifies the first command/path with a fixed lexical grammar, but command names, ordinary option spellings, aliases, help summaries, route patches, and extension namespaces are generated into SCI. It handles root `--help` and `--version` internally and exits without reading SCI, project configuration, compiler metadata, or aspect manifests.
2. **Replace public `mmap` policy with public `load` policy.** `mmap`, `pread`, ordinary read, direct execution, VFS prewarm, and cached-image mapping are implementation strategies selected by the loader.
3. **Keep the default user profile `normal`; keep `tiny` explicit.** Normal has complete expected semantics but lazy availability. Tiny is a strict deployment profile where unused capabilities are physically absent.
4. **Make compiler, interpreter, and loader separate command capsules.** Root startup contains none of them. A source route selects frontend plus interpreter or JIT; an SMF route selects only the base loader; a native route normally executes directly.
5. **Keep one static/dynamic component ABI.** Development can rebuild one `.smf` or native provider without rebuilding the core. A full rebuild folds `placement=auto` components statically when the embedded implementation hash matches the configured implementation hash. `placement=dynamic` remains external after every rebuild.
6. **Strip optional aspects from default closures.** Logging, tracing, profiling, coverage, debug dumps, sanitizers, runtime AOP, optimization remarks, loader tracing, and compiler phase tracing are aspect packs. The core imports no aspect implementation.
7. **Keep the current MIR interpreter as the reference oracle.** Add a separate typed, dense, register-based execution IR for the fast interpreter and all JIT tiers. Do not mutate the reference path into an unreviewable performance experiment.
8. **Complete tiering rather than merely naming tiers.** Tier 0A is generic typed ExecIR, Tier 0B is quickened/specialized ExecIR, Tier 1 is fast Cranelift compilation, and Tier 2 is optimized LLVM compilation. JIT compilation consumes typed IR, not source text.
9. **Redesign SMF loading around segments, not symbols.** Validate and map each RX/R/RW segment once, apply a compact relocation stream under W^X, resolve imports at module activation, and never allocate/copy/protect one executable buffer per symbol on the normal path.
10. **Evolve the existing semantic cache.** Do not build a second cache subsystem. Add exact query DAGs, interface hashes, aspect match-set hashes, optimizer/backend identities, and object/ExecIR/native tiers to the current CAS.
11. **Use fair performance lanes.** Native Simple is compared with native Go/Rust/C. Fresh source execution is compared with Python, Bun, `go run`, and `cargo run`. Cached source is compared with bytecode/cache-hit paths. Compiler cold, warm no-op, one-body change, interface change, and release builds are separate lanes.
12. **No performance claim without non-vacuous evidence.** Exit code zero is insufficient. Every test run must emit an explicit scenario/result count; otherwise the lane is `INCONCLUSIVE` and requires a direct `simple run` reproduction.
13. **Make the CLI surface composition data.** Adding or renaming a command, exact option, alias, help line, option value map, or `--x<namespace>-...` extension namespace regenerates SCI and, when needed, one provider artifact; it does not relink `simple-core`. Only the invariant lexical grammar, reserved root options, or the versioned option-wire ABI can require a core rebuild.

### 0.2 Target architecture

```text
                         OPERATING SYSTEM
                               |
                               v
+------------------------------------------------------------------+
| simple stage-0                                                   |
|                                                                  |
| fixed argv classifier       embedded root help/version           |
| compact SCI route/option index reader    static component table  |
| exact module admission      minimal fatal stderr                 |
|                                                                  |
| NO GC, scheduler, reflection, compiler, interpreter, JIT, AOP,   |
| UI, Office, IDE, test runner, profiler, logger, or directory scan|
+-------------------------------+----------------------------------+
                                |
                         StartupPlanV1
                                |
          +---------------------+-----------------------+
          |                     |                       |
          v                     v                       v
    native artifact          SMF artifact           source/command
          |                     |                       |
     direct exec          loader.base              command capsule
                                |                       |
                     exact selected modules        +---+-----------+
                                                  |               |
                                             interpreter       compiler/JIT
                                                  |               |
                                                ExecIR      frontend -> MIR
                                                  |               |
                                             quickening     fast/release path
                                                  |               |
                                           hotspot Tier 1/2  selected backend

Optional cross-cutting behavior enters only through versioned aspect/provider
contracts. Disabled means physically absent. Selected dynamic modules are
admitted by exact path, digest, ABI, interface hash, and capability policy.
```

### 0.3 What "better than Go" can truthfully mean

Simple can target better-than-Go results in these equivalent lanes:

- stage-0 root command dispatch versus the `go` tool's root command dispatch;
- tiny native Simple hello versus a native Go hello with equivalent output and semantics;
- warm cached Simple source versus `go run` or other build-and-run workflows;
- specialized Simple interpreter versus CPython on statically typed scalar and collection workloads;
- Simple incremental one-body-change compilation versus Go and Rust incremental development builds.

It is not a valid claim to compare first-run `simple program.spl`, which parses and executes source, against an already-linked `./go-program` and call the difference "runtime performance." The benchmark harness must reject such category errors.

---

## 1. Scope and terminology

### 1.1 Scope

This document covers:

- process startup and `startup()` composition;
- SCI/config lookup, command routing, and config-driven CLI option routing;
- static and dynamic component selection;
- aspect stripping, packaging, and activation;
- SMF/native module loading;
- interpreter architecture and tiered JIT;
- compiler cold, warm, and incremental performance;
- default, tiny, full, and instrumented profiles;
- cross-language benchmarking;
- parallel implementation ownership;
- Modern SSpec correctness, performance, security, and generated-manual verification.

It does not redesign Simple syntax, ownership semantics, MDSOC+ visibility, the public language effect system, or the meaning of existing source programs. Any optimization that changes observable semantics is rejected.

### 1.2 Terms

| Term | Meaning in this document |
|---|---|
| **stage-0** | The smallest process entry and route classifier. It can print root help/version and produce a `StartupPlanV1`. |
| **component** | A compiler phase, backend, interpreter, loader capability, command provider, runtime service, or aspect implementation described by one versioned descriptor. |
| **capability** | A semantic or operational facility such as `compiler.frontend`, `loader.hot_reload`, `aspect.log.debug`, or `backend.llvm`. |
| **placement** | `static`, `dynamic`, or `auto`; it does not decide whether a capability is enabled. |
| **activation** | The point at which a dynamic component is admitted and initialized. |
| **SCI** | The compact generated Simple Composition Index used for startup routing, option routing, and provider selection. It is not parsed as general SDN/text on the stage-0 hot path. |
| **CLI option route** | A generated record that binds an exact option spelling/alias and scope to a bounded plan patch or provider-forwarding action. |
| **extension namespace** | A short configured provider name used by the invariant syntax `--x<namespace>-<key>[=<value>]`; the namespace is data, while only the `--x` lexical form is fixed in stage-0. |
| **route patch** | A precompiled data-only change to a startup/command plan, such as selecting a route variant or adding a component/aspect ID. Stage-0 applies the patch without understanding provider-specific semantics. |
| **SMF** | Simple module format. The target design uses segment-oriented loading and explicit ABI/import/export metadata. |
| **ExecIR** | Proposed typed, compact, register-based execution bytecode shared by the fast interpreter and JIT tiers. |
| **reference interpreter** | The current direct MIR evaluator retained for correctness comparison and debugging. |
| **aspect pack** | A physical load unit containing one or more logically independent aspect facets. |
| **receipt** | Structured evidence describing a selection, load, cache, compile, or execution decision. Receipts are enabled for tests, diagnostics, and certification, not necessarily allocated on the production fast path. |

### 1.3 Public policy must not expose implementation accidents

The current launch metadata exposes `mmap_hint`, `include_mmap_cache`, and a cache strategy named `mmap`. That names a mechanism rather than intent. The replacement is:

```text
load_policy:
    normal
    index_only
    map_selected_segments
    read_ahead_selected
    direct_exec
    auto
```

The provider then chooses `mmap`, `MapViewOfFile`, SimpleOS VFS pages, `pread`, anonymous executable memory, an embedded static table, or direct OS execution. This keeps host, Windows, and SimpleOS implementations substitutable.

---

## 2. Truth boundary and current evidence

### 2.1 Inspected repository baseline

All current-code observations in this document refer to repository commit:

```text
5747bdd660bb5e58ba02cc1ae928eef823595cd5
```

The repository is highly active. Every implementation agent must record both its immutable starting SHA and the fetched integration SHA. Performance reports must name the exact executable digest, not a mutable `bin/simple` symlink.

### 2.2 Historical measurements are direction, not admission

The current checked-in cross-language report dated 2026-06-11 records one measurement run in a Docker container limited to two CPUs. Its useful historical observations include:

| Historical lane | Recorded result |
|---|---:|
| Simple interpreter cold hello | 53.206 ms |
| Simple SMF loader cold hello | 38.070 ms |
| Simple native cold hello | 4.721 ms |
| C native cold hello | 4.440 ms |
| Go native cold hello | 66.875 ms |
| Python cold hello | 18.347 ms |
| Simple interpreter fib(35), outer-process | 130.436 ms |
| Simple SMF fib(35), outer-process | 110.324 ms |
| Simple native fib(35), in-process | 62.431 ms |
| Go fib(35), in-process | 58.230 ms |
| C fib(35), in-process | 14.362 ms |
| Python fib(35) | 1903.527 ms |

These rows prove that the harness exists and that current Simple modes have materially different costs. They do **not** prove that Go generally starts in 66 ms, nor that Simple native generally beats Go startup. One run, container scheduling, cache state, compiler versions, output paths, and binary identity are insufficient for a release claim.

The same historical report recorded a 438.6 MB Simple interpreter/SMF runtime dependency, a 6.3 MB Simple native artifact, a 1.8 MB Go artifact, and a 15.6 KiB C artifact for its generated hello lane. These numbers describe that specific 2026-06-11 build and its debug/runtime composition; they are not language minimums. They nevertheless confirm that reducing the default Simple tool/runtime closure is a first-order requirement, not a micro-optimization.

A separate 20-run startup audit is more useful for the minimal path. It recorded:

| Audited artifact | File bytes | Average runtime |
|---|---:|---:|
| assembly syscall hello | 8,568 | 4.795 ms |
| C hello | 14,472 | 5.616 ms |
| C mmap/preload/argparse | 14,472 | 3.543 ms |
| Simple mmap/preload/argparse, core-C lane | 14,400 | 4.681 ms |
| Simple hello, core-C lane | 14,336 | 3.129 ms |
| Simple standalone TUI, core-C lane | 14,336 | 5.295 ms |
| Simple full TUI app, core-C lane | 14,368 | 6.510 ms |

The important conclusion is not the exact millisecond ordering. It is that a deliberately narrow Simple closure is already C-class in file size and startup shape, while the broad compiler/runtime executable is not. The architecture should make the narrow closure the real stage-0 rather than a special audit artifact.

### 2.3 Current startup strengths

The repository already contains useful foundations:

- manifest-driven startup argument parsing;
- pre-main file preload policy;
- launch metadata embedded in SMF/native artifacts;
- a startup plan that can distinguish scripts, SMF, and native artifacts;
- dynSMF policy, exact artifact paths, ABI sidecars, source/interface hashes, and evidence rows;
- provider admission separated from activation;
- static and dynamic provider concepts;
- background compilation explicitly prohibited from the startup session;
- a default dynSMF manifest whose entries are on-demand rather than default-autoloaded.

These should be refined, not discarded.

### 2.4 Current startup bottlenecks

#### Unified CLI dependency root

The current main CLI source directly imports broad command families including build, compile, check, browser, UI, Office, IDE, play, T32, statistics, OS commands, and tooling. A few imports are `lazy`, but the root still exposes a large source and link closure before command classification.

#### General data structures on the smallest path

The startup parser constructs arrays of text values and compares every argument against every schema declaration. That is acceptable for an application manifest parser but not for root `--version` or `--help`.

#### Full metadata reads

Current metadata helpers can parse launch metadata from complete SMF/native byte arrays. Stage-0 should read a fixed trailer and a bounded directory/index, not materialize the entire artifact merely to decide which execution capsule is required.

#### Public `mmap` coupling

Scripts and SMF default to `mmap_hint=true`, which encourages mapping/prewarming before evidence shows that it helps a given artifact. Page touching can turn a cheap lazy file mapping into synchronous I/O. Only selected segments or explicitly declared preloads should be touched.

### 2.5 Current loader bottlenecks

The curated module loader currently constructs, during loader creation:

- a compiler context;
- `ObjTaker`;
- an object provider;
- a JIT instantiator;
- an executable mapper;
- a cache manager;
- a resource lifecycle manager;
- several dictionaries for modules, symbols, fingerprints, exports, and dependencies.

Its default config enables JIT and cache. The load path can read exported code, allocate executable memory, copy code, and map/register it for each symbol. The compatibility path similarly performs per-symbol allocation and protection transitions.

This is a capable development/hot-reload loader. It is not a minimal program loader. It must become an optional composition around `loader.base`, not the only path.

### 2.6 Current interpreter bottlenecks

The direct MIR interpreter is valuable as a portable semantic oracle, but its hot state uses dictionaries for locals, blocks, functions, aggregates, strings, and saved frames. Each MIR instruction enters a large tagged match, resolves generic operands, and repeatedly constructs or looks up semantic objects. It also imports a logging facade and emits creation/debug calls through that facade.

These costs are structural. Removing startup overhead alone will not make long interpreter workloads competitive with optimized native Go, Rust, or JavaScript JITs.

### 2.7 Current tiered-JIT gap

The repository already names three tiers:

```text
Tier 0: interpreted
Tier 1: Cranelift
Tier 2: LLVM
```

The current manager, however, creates a JIT handle eagerly, tracks profiles in dictionaries, and compiles retained source text when a threshold is reached. The Tier 2 transition principally changes state/counters; a complete optimized-LLVM OSR path is not yet proven. The target design keeps the policy vocabulary but changes the compilation input to typed ExecIR/MIR, creates native engines lazily, and makes OSR/deoptimization explicit.

### 2.8 Current dynamic optimizer gap

Simple already has:

- `PluginScope` = source, MIR, or both;
- `ApplyMode` = static, dynamic, or both;
- versioned optimizer manifest concepts;
- entry symbols, ABI names, aliases, cost classes, backend policies, and registries.

But the dynamic manifest is explicitly a skeleton, built-in passes are directly imported, and a dynamic descriptor lacking a typed built-in `PassKind` can pass through a generic runner without executing an implementation. The plan must finish invocation and build integration, not create a parallel optimizer plugin model.

### 2.9 Current aspect gap

The full AOP tooling includes runtime lambdas, `Any`, class-based log/tracing/contract aspects, a local logger with level branches, runtime enable/allowlist checks, and debug-log checks. This is suitable for the full tools/profile path. It must not be imported by stage-0, loader.base, or the fast interpreter dispatch loop.

### 2.10 Current CLI composition strength and missing option layer

The repository already has the right base for a data-driven CLI: SCI composition records for providers, bindings, and commands; a canonical pointer-free `SimpleCliCommandV1` request/result wire; provider operations for describe, argument validation, execution, and completion; and dynamic provider admission separated from activation. The SCI decoder is sectioned and can reject unknown required sections while permitting additive optional sections.

The missing layer is a first-class option-route section. Today, root/global and many command option spellings remain embedded in CLI source and the unified main imports their owners. There is no canonical record for exact option spelling, arity, scope, help, forwarding, semantic cache classification, or an extension namespace. Consequently, adding a seemingly small global option can still touch a hot CLI/core source file or enlarge the root dependency closure. This plan extends the existing SCI/provider model; it does not create a second plugin or CLI registry.

---

## 3. Research synthesis: what to adopt and what not to copy

### 3.1 Go: build-time closure and indexed dependency metadata

The Go compiler separates parsing, type checking, unified IR construction, middle-end optimization, SSA lowering, architecture-specific lowering, and object emission. Its unified export data stores types, inline candidates, generic bodies, and escape summaries, with an index for lazy decoding. A client package normally needs the compiled output of each direct import rather than rescanning all transitive source dependencies.

**Adopt for Simple:**

- one compact, indexed interface/export artifact per module;
- direct-dependency consumption;
- lazy decoding of only referenced exported entities;
- build-time dead closure for native applications;
- compiler phase timing and statistically meaningful `benchstat`-style comparison;
- immutable old/new toolchain snapshots for compiler validation.

**Do not copy blindly:**

- a permanently monolithic runtime for every deployment profile;
- static-only toolchain extensibility;
- package-level invalidation where Simple can safely preserve block/query granularity.

Primary source: [Go compiler architecture](https://go.dev/src/cmd/compile/README), [compile command](https://go.dev/src/cmd/compile/doc.go).

### 3.2 Bun and JavaScriptCore: source startup, compact bytecode, and tiering

Bun emphasizes a small native source-launch path and uses JavaScriptCore. Bun's official documentation reports a 5.2 ms hello on its reference Linux benchmark and recommends `hyperfine` for CLI measurements. Its compiled executable mode moves path resolution, file reading, parsing, and transpilation from runtime to build time. Its bytecode option moves JavaScriptCore bytecode generation to build time and reports a 2x `tsc` startup improvement on its documented case.

JavaScriptCore uses one bytecode source of truth across its LLInt interpreter, Baseline JIT, DFG JIT, and FTL JIT. It starts at a low-latency interpreter, promotes hot functions, performs higher-tier compilation concurrently, and supports on-stack replacement and deoptimization.

**Adopt for Simple:**

- one compact ExecIR shared by the interpreter and JIT tiers;
- low-latency Tier 0 followed by evidence-driven tier promotion;
- build-time bytecode/ExecIR caching;
- concurrent high-tier compilation;
- OSR at explicit safe points;
- profiles that can trade memory for speed without changing semantics.

**Do not copy blindly:**

- JavaScript's pervasive dynamic tagging where Simple has static type evidence;
- a large JIT/runtime closure for tiny native applications;
- runtime parsing when an exact cached ExecIR/native artifact is valid.

Primary sources: [Bun runtime](https://bun.com/docs/runtime), [Bun benchmarking](https://bun.com/docs/project/benchmarking), [Bun compiled executables and bytecode](https://bun.com/docs/bundler/executables), [JavaScriptCore bytecode](https://webkit.org/blog/9329/a-new-bytecode-format-for-javascriptcore/), [JavaScriptCore speculation/tiering](https://webkit.org/blog/10308/speculation-in-javascriptcore/).

### 3.3 CPython: generated dispatch, quickening, and inline caches

CPython's current internal interpreter documentation describes traditional switch, computed-goto, and tail-call interpreter implementations. PEP 659 specialization rewrites adaptive instructions into guarded specialized forms and stores small inline caches adjacent to instructions. Specialized instructions are expected to minimize branches and dependent memory accesses and to deoptimize when assumptions fail.

**Adopt for Simple:**

- generated opcode definitions and dispatch implementations;
- portable switch fallback plus computed-goto/tail-call variants;
- quickening counters;
- guarded specialized opcode families;
- small inline caches;
- deoptimization to the generic typed opcode;
- contiguous, preallocated frame/stack storage.

**Exploit Simple's advantage:**

Most arithmetic, local slots, fields, and direct calls already have static types. Simple should emit typed opcodes immediately and reserve adaptive specialization for interface calls, dynamic modules, variants, generics at late boundaries, and shape-dependent operations.

Primary sources: [CPython interpreter internals](https://github.com/python/cpython/blob/main/InternalDocs/interpreter.md), [PEP 659](https://peps.python.org/pep-0659/).

### 3.4 Rust: exact incremental queries, backend abstraction, and build profiles

Rust's incremental compiler stores query results and a query dependency DAG. Its red-green algorithm can keep dependents green even after an input changes when the recomputed result fingerprint is unchanged. Rust separates backend-agnostic code generation through a stable backend interface and supports concurrent codegen units. Cargo uses distinct development and release profiles; embedded `no_std` and abort-style panic profiles demonstrate that runtime facilities can be explicit deployment choices.

**Adopt for Simple:**

- exact query keys and result fingerprints;
- ordered dependency reads;
- semantic green propagation;
- selective serialization of expensive results;
- backend-agnostic MIR/ExecIR contracts;
- independent codegen units;
- normal/dev/release/tiny profile composition;
- worker-local arenas and immutable shared results.

**Do not copy blindly:**

- crate-wide granularity where block-level identities are available;
- shared compiler state that scales poorly beyond a few threads;
- trait-object overhead at hot backend boundaries when static specialization can be generated.

Primary sources: [rustc incremental compilation](https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation.html), [backend-agnostic codegen](https://rustc-dev-guide.rust-lang.org/backend/backend-agnostic.html), [parallel rustc](https://rustc-dev-guide.rust-lang.org/parallel-rustc.html), [Cargo release profiles](https://doc.rust-lang.org/book/ch14-01-release-profiles.html).

### 3.5 ELF/glibc: dynamic loading must be narrow and explicit

The glibc hardening guidance warns that general `dlopen`/`dlclose`, lazy binding, symbol interposition, underlinking, cycles, and dynamic TLS add complexity and unpredictability. It recommends explicit dependencies, immediate binding, RELRO, non-executable stacks, and no writable-executable load segments.

Simple still needs controlled dynamic modules, but should adopt the same discipline:

- load only exact configured modules;
- no directory search on the fast path;
- no arbitrary symbol interposition;
- no dependency cycles;
- bind all imports when the selected module activates;
- pin modules for the process by default;
- prohibit RWX;
- separate module admission from activation;
- use immutable replacement plus atomic rename for updates.

Primary source: [GNU C Library dynamic-linker hardening](https://sourceware.org/glibc/manual/latest/html_node/Dynamic-Linker-Hardening.html).

### 3.6 GCC, LLVM, and Cargo: explicit extension namespaces and one static/dynamic implementation

GCC plugins use an explicit plugin identity and namespaced option form (`-fplugin-arg-<name>-<key>=<value>`) rather than allowing every plugin to claim arbitrary compiler flags. LLVM's new pass manager uses the same pass-plugin entry contract for dynamic loading and static integration. Cargo discovers external subcommands by a reserved `cargo-<command>` namespace rather than rebuilding Cargo whenever a tool adds a command. Rust also distinguishes options that affect tracked compiler semantics from options that should not invalidate incremental artifacts.

**Adopt for Simple:**

- reserve one invariant extension grammar, `--x<namespace>-<key>[=<value>]`;
- bind each namespace to an exact SCI provider descriptor rather than a filesystem search;
- use the same provider implementation and ABI whether it is dynamically loaded in development or statically folded into a provider capsule for release;
- classify option semantics so help/routing changes do not poison compiler caches while compile-semantic options do enter exact action keys;
- keep conventional exact options config-driven for user ergonomics, with the namespaced form as the zero-core-rebuild escape hatch.

**Do not copy blindly:**

- do not forward unvalidated raw strings to arbitrary paths;
- do not silently ignore an unknown namespace or missing required provider;
- do not load a provider merely to discover whether the following token is its value; the extension grammar requires `=` for values.

Primary sources: [GCC plugin loading and arguments](https://gcc.gnu.org/onlinedocs/gccint/Plugins-loading.html), [LLVM new-pass-manager plugins](https://llvm.org/docs/WritingAnLLVMNewPMPass.html), [Cargo custom subcommands](https://doc.rust-lang.org/beta/book/ch14-05-extending-cargo.html), [rustc tracked options](https://doc.rust-lang.org/stable/nightly-rustc/rustc_session/config/struct.Options.html).

---

## 4. Non-negotiable principles

### 4.1 Architecture preservation

The implementation must preserve:

- MDSOC+ ownership, visibility, and dependency direction;
- the SCI/provider composition model;
- one versioned interface per substitutable boundary;
- static and dynamic implementations of the same logical component;
- host/SimpleOS separation through ports;
- interpreter/native/SMF semantic parity;
- the existing cache and artifact identity model;
- explicit mission-critical and security policies;
- generated documentation and test traceability.

### 4.2 Core never depends on an aspect

Allowed:

```text
aspect.log.debug -> startup.event ABI
aspect.loader.trace -> loader.event ABI
aspect.compiler.profile -> compiler.event ABI
```

Forbidden:

```text
startup core -> aspect.log.debug implementation
loader.base -> full AOP weaver
interpreter dispatch -> dynamic Logger object
compiler core -> coverage/report UI
```

A core may publish a minimal event schema or optional import slot, but the disabled production closure must not execute a branch or allocate a receipt per event.

### 4.3 Static and dynamic are deployment placements, not different implementations

The same source-level component descriptor, ABI tests, semantic tests, and capability contract generate:

```text
component implementation
    +-- static object/archive
    +-- SMF/native dynamic provider
```

No feature may have one code path for static and a semantically different path for dynamic.

### 4.4 No silent fallback

A strict request for LLVM, a dynamic optimizer, a security aspect, or a specific loader provider either activates that exact implementation or fails with a structured reason. Only an explicit `auto` policy may choose an alternative, and its receipt records the choice.

### 4.5 No startup compilation

Stage-0 and the startup admission path never invoke a shell or compiler child. Missing development artifacts may be queued for a later warm service, but the current command either uses an admitted artifact, a valid static implementation, or fails/chooses an explicitly permitted fallback.

### 4.6 Cache failure never changes correctness

A cache hit must be validated by exact semantic identity. A cache miss, corrupt entry, interrupted transaction, or quota eviction may cost time but may not change the program result. Every cached tier has a deterministic uncached reference path.

### 4.7 Instrumentation must be structurally removable

`disabled` means:

```text
no implementation code
no aspect metadata
no log format strings
no pointcut match table
no module mapping
no constructor
no hot-path condition
no per-event allocation
```

### 4.8 Performance is subordinate to semantic and security gates

A faster path is not admitted until:

- reference/new-path results match;
- failure behavior matches;
- ownership/effect checks remain active;
- exact ABI/digest/capability admission passes;
- malformed/corrupt artifacts fail closed;
- unsupported operations report `blocked`/`unsupported`, not success;
- a sabotage test proves the test reaches the changed path.

### 4.9 CLI surface changes are composition changes

After the one-time CLI option-route ABI lands, ordinary command/option evolution must not require editing or relinking stage-0. Command names, exact option spellings, aliases, help summaries, value maps, completion metadata, and extension namespaces belong to generated SCI sections. Provider-specific parsing and behavior belong to the provider. Stage-0 owns only the byte grammar, reserved root options, bounded index decoding, provider admission front door, and generic plan-patch application.

An option may enter `simple-core` only when it changes an invariant needed before SCI can be selected or validated. Convenience, compiler, loader, interpreter, UI, test, logging, optimizer, and backend options are never sufficient reasons.

---

## 5. Unified composition architecture

### 5.1 Three independent decisions

Every selectable component is described by a generated `ComponentDescriptorV1`:

```text
ComponentDescriptorV1
    component_id
    interface_id
    interface_version
    interface_hash
    implementation_hash
    capability_provides[]
    capability_requires[]
    target_mask
    profile_mask
    presence_policy
    placement_policy
    activation_policy
    static_symbol_index
    dynamic_artifact_path
    artifact_digest
    entry_symbol
    dependency_ids[]
    security_class
    update_generation
```

The composition resolver makes decisions in this order:

```text
1. Is the capability allowed and required?
2. Is a valid static implementation embedded?
3. Does policy require dynamic placement?
4. If auto, does the embedded implementation hash equal the configured hash?
5. If dynamic is selected, is the exact artifact admitted?
6. Are all dependencies admitted without a cycle?
7. Activate at the configured trigger.
```

### 5.2 Automatic dynamic-to-static folding

The requested development behavior is represented directly:

```text
NEW OR MODIFIED OPTIMIZER
        |
        v
build only optimizer.smf
        |
update SCI descriptor implementation_hash/path/digest
        |
existing compiler core sees:
    static hash != configured hash
        |
        v
load optimizer.smf without compiler rebuild

LATER FULL COMPILER REBUILD
        |
        v
same optimizer is compiled into compiler
embedded static hash == configured hash
        |
        v
use static implementation; no optimizer.smf load

EXCEPTION
placement = dynamic
        |
        v
always load external optimizer after every rebuild
```

This requires no manual config flip after a full rebuild.

### 5.3 Resolution algorithm

```text
resolve_component(desc, static_table, policy):
    if desc.presence == off:
        return ABSENT

    static = static_table.lookup(desc.component_id, desc.interface_hash)

    if desc.placement == static:
        require static.exists
        require static.impl_hash == desc.implementation_hash
        return STATIC(static)

    if desc.placement == dynamic:
        return admit_dynamic(desc)

    # placement == auto
    if static.exists and static.impl_hash == desc.implementation_hash:
        return STATIC(static)

    return admit_dynamic(desc)
```

A stale static implementation is never silently selected over a configured newer dynamic implementation. A dynamic artifact whose interface hash changed forces dependent rebuild admission rather than implementation-only reload.

### 5.4 Presence, placement, and activation defaults

| Component family | Presence default | Placement default | Activation default |
|---|---|---|---|
| stage-0 route classifier | on | static | startup |
| root help/version | on | static | command |
| SCI compact index reader | auto | static | command |
| loader.base | auto | auto | command |
| interpreter.fast | auto | auto | command |
| interpreter.reference | off in release; on in dev/test | dynamic/auto | manual/test |
| compiler.frontend | auto | auto | command |
| compiler.semantic/MIR | auto | auto | command |
| optimizer.basic | auto | auto | command |
| optimizer.expensive | off/auto by profile | auto | command |
| backend.cranelift | auto | auto | command/hotspot |
| backend.llvm | off/auto by profile | dynamic/auto | command/hotspot |
| loader.hot_reload | off | dynamic | first_use |
| aspect.log.error/warn | off in tiny; auto in normal | auto | first_use |
| aspect.log.debug/trace | off | dynamic | first_use |
| coverage/profile/sanitizer | off | dynamic | command/manual |
| GUI/Office/IDE | off for CLI route | dynamic/auto | command |

### 5.5 SCI is generated, compact, and bounded

Stage-0 must not parse a full SDN document or enumerate directories. Build/config tooling compiles human-readable configuration to one `simple.sci` binary.

Proposed fixed header:

```text
StartupIndexHeaderV1
    magic[8]            = "SIMPSCI1"
    schema_version      : u16
    header_size         : u16
    flags               : u32
    generation          : u64
    route_count         : u32
    option_route_count  : u32
    namespace_count     : u16
    component_count     : u32
    string_bytes        : u32
    route_index_offset  : u64
    option_index_offset : u64
    namespace_offset    : u64
    component_offset    : u64
    dependency_offset   : u64
    string_offset       : u64
    content_digest[32]
    signature_offset    : u64
    signature_size      : u32
```

Routes use a minimal-perfect-hash or sorted binary index generated at build time. Lookup is bounded and allocation-free:

```text
RouteEntryV1
    key_hash            : u64
    key_span            : Span32
    route_kind          : u8
    command_id          : u32
    component_first     : u32
    component_count     : u16
    flags               : u16
```

The SCI carries exact component paths and hashes; it never instructs stage-0 to scan `PATH`, a plugin folder, or the entire repository. Command and exact-option lookups use generated sorted/MPH indexes; extension namespace lookup uses a tiny unique namespace index.

### 5.6 Profile composition

```text
normal (default)
    full expected language semantics
    common facilities available
    optional heavy components lazy
    instrumentation off

tiny (explicit, strict)
    infer and close only required capabilities
    unsupported required capability = compile/build error
    optional runtime families physically absent

full (explicit)
    all installed standard capabilities available
    still lazy; availability is not eager loading

debug/instrumented (overlay)
    selected log/trace/profile/coverage/debug aspects
    may choose instrumented ExecIR or compiler pipeline variants
```

### 5.7 CLI commands and options are generated composition data

The CLI uses one-time stable routing/wire contracts and thereafter treats surface evolution as data:

```text
human SDN/config + provider descriptors
                |
                v
          SCI generator
                |
      +---------+--------------------------+
      |                                    |
command/alias/help index         exact option/namespace index
      |                                    |
      +-----------------+------------------+
                        |
                    stage-0
                        |
                exact admitted provider
```

The immutable `simple-core` set is intentionally narrow:

```text
-h, --help
-V, --version
--config-index=<path>
--no-config
--profile=<id>
--json
--strict
--diagnose-startup
--                              # hard routing boundary
--x<namespace>-...              # invariant extension grammar only
```

Even `--execution`, `--backend`, `--opt-level`, `--log`, test options, UI options, and future global options are generated exact option routes or provider options. Their spellings are not compiled into stage-0. The fixed core set may be reduced further after migration; it may not grow casually.

### 5.8 Exact config-registered options

Exact options retain conventional ergonomics while staying outside the core binary. Example source configuration:

```yaml
cli_options:
  - name: --execution
    aliases: [--exec-mode]
    scope: global
    value_mode: required
    values:
      auto: route.source.auto
      interpret: route.source.interpret
      jit: route.source.jit
      native: route.source.native
    action: select_route_variant
    help: Select the source execution engine
    semantic_class: runtime_selection

  - name: --backend
    scope: [compile, run-source]
    value_mode: required
    value_provider: backend.catalog
    action: provider_forward
    provider: compiler.cli
    forward_name: --backend
    help: Select a configured compiler/JIT backend
    semantic_class: compile_semantic
```

The SCI generator validates names, aliases, scope, arity, values, provider bindings, route patches, help, completion metadata, semantic class, and missing-provider policy. Adding or changing a record performs no source compilation and no link.

Exact options can be:

- `global`: recognized before or after command selection according to the route record;
- `command`: recognized only for one command/route family;
- `entry`: recognized around a source/SMF/native entry only when `after_entry=true`;
- `provider`: forwarded to an exact provider without changing the startup plan;
- `routing`: mapped to a generated `StartupPlanPatchV1`.

### 5.9 Generic namespaced extension options

The zero-core-rebuild escape hatch is:

```text
--x<namespace>-<key>
--x<namespace>-<key>=<value>
```

Examples:

```text
--xllvm-pass=loop-vectorize
--xinterp-quickening=off
--xloader-verify=strict
--xlog-level=debug
--xoffice-experimental-ribbon
```

Binding configuration:

```yaml
cli_extension_namespaces:
  - namespace: llvm
    provider: backend.llvm
    binding: cli.extension.llvm
    availability: optional
    missing_policy: error
    help: LLVM backend extensions

  - namespace: log
    provider: aspect.log
    binding: cli.extension.log
    availability: optional
    missing_policy: warn_skip
    semantic_class: instrumentation
```

Grammar and routing rules:

1. Namespace matches `[a-z][a-z0-9_]{0,31}` and contains no `-`; the first `-` after `--x` is the namespace/key delimiter.
2. Key is nonempty, bounded, ASCII-lowercase/hyphen normalized, and delivered as structured bytes.
3. A bare option is a flag. A namespaced value **must use `=`**. The router never consumes the next argv token because it does not load a provider to discover arity.
4. `--xllvm-pass=gvn` becomes `CliExtensionArgV1(namespace="llvm", key="pass", value="gvn", has_value=true)`. A provider adapter may expose it internally as `--pass=gvn`; raw shell forwarding is forbidden.
5. Namespace lookup is exact in SCI. There is no derivation from filenames, import names, `PATH`, or a plugin directory.
6. `--` ends all Simple routing. Every later token belongs to the selected command/application unchanged.
7. Before a command/path, global extension options are collected. After a command, command/global extensions remain eligible until `--`. After a direct program entry, only extension namespaces and exact records marked `after_entry=true` are intercepted; all other tokens are program arguments.

A provider can add another namespaced key without changing SCI because stage-0 treats the key/value as opaque structured data. Only adding/changing the namespace binding, exact help summary, provider digest, or capability policy updates SCI.

### 5.10 SCI option-route section

Extend the current sectioned SCI rather than changing the existing command record in place:

```text
SCI_SECTION_CLI_OPTION_ROUTE_V1 = 10

SimpleCliOptionRouteRecordV1
    option_id
    spelling
    aliases[]
    scope_kind
    scope_ids[]
    value_mode                 # flag|required|optional|repeatable
    after_entry
    action_kind                # plan_patch|provider_forward|help_only
    plan_patch_id
    provider_id
    binding_service_id
    forward_name
    help_summary
    completion_kind
    semantic_class
    availability
    missing_policy
    required_capability_bits

SimpleCliExtensionNamespaceRecordV1
    namespace
    provider_id
    binding_service_id
    allowed_scope_ids[]
    before_command
    after_command
    after_entry
    help_summary
    semantic_class
    availability
    missing_policy
    required_capability_bits
```

A route-affecting option points to data, not provider-specific code:

```text
StartupPlanPatchV1
    patch_id
    set_profile_id?
    set_route_variant_id?
    add_component_ids[]
    remove_component_ids[]
    add_aspect_ids[]
    add_capability_bits
    deny_capability_bits
```

Stage-0 applies this generic patch. A new option that selects an existing route/component/aspect therefore needs only an SCI update. A genuinely new startup semantic field requires a versioned contract extension; that exceptional case is allowed to rebuild core.

Rollout is one-time and fail-closed: stage-0/SCI minor version 1.1 introduces the option section and feature bit. An old reader encountering a composition that requires option routing rejects it as unsupported rather than ignoring options. Once the new reader is deployed, future records do not rebuild it.

### 5.11 Provider option ABI

Do not overload the existing command ABI with unversioned conventions. Add an optional interface group:

```text
SimpleCliExtensionV1
    describe(namespace, scope) -> bounded option/help schema
    validate(batch, context) -> validation receipt
    apply(batch, context) -> plan/runtime/provider receipt
    complete(prefix, context) -> bounded candidates

CliExtensionBatchV1
    route_id
    command_id
    entry_kind
    namespace_id
    args[]: CliExtensionArgV1
    capability_grant
    output_capacity
```

The wire is pointer-free, length-bounded, versioned, and callable through the existing admitted provider session/pin ownership model. Stage-0 never invokes a shell or starts a compiler to process an option. Static and dynamic providers expose the same interface and conformance tests.

Root help stays I/O-free and documents only core options plus the generic extension syntax. `simple options`, `simple help --all`, and command help read the SCI option/help index without loading providers. `simple help <command> --full` may query only that command's admitted provider for generated/dynamic details.

### 5.12 Missing providers, collisions, and security

Default behavior is fail-closed:

```text
unknown exact option in a Simple-owned option scope
                                    -> error with nearest configured names
unrecognized option after direct entry and outside a declared after_entry route
                                    -> application argument
unknown --x namespace               -> error; never silently forward
declared required provider missing  -> error
declared optional provider missing  -> configured error|warn_skip|silent_skip
ABI/digest/capability mismatch       -> error
```

`silent_skip` is permitted only for explicitly non-semantic diagnostic/instrumentation options, is forbidden in release and mission-critical profiles, and must still appear in a compact receipt when evidence is enabled. The user-requested "forward if module exists" behavior is represented by `availability=optional` plus an explicit missing policy; existence alone never bypasses digest, ABI, interface, export, or capability admission.

Reserved core spellings and the entire `--x` prefix cannot be overridden. Exact global aliases are unique. Command-local options may overlap only in disjoint command scopes. Extension namespaces are globally unique and explicitly assigned; duplicated normalized IDs are a configuration error. Arbitrary provider paths and environment-provided namespaces are prohibited.

### 5.13 Option semantic identity and rebuild rules

Every route has one semantic class:

```text
routing_only          # spelling/help/dispatch only
diagnostic_only       # output formatting, no program artifact semantics
runtime_selection     # interpreter/JIT/runtime capability selection
compile_semantic      # parsing/type/MIR/optimization semantics
codegen_semantic      # backend/target/code generation semantics
instrumentation       # aspect/instrumented variant selection
```

Only the relevant projection enters an action key. Renaming `--backend` or changing its help does not invalidate compiled code; changing the resolved backend does. Adding `--xlog-level=debug` changes runtime/aspect activation identity, not the source HIR key. A compiler option that changes overflow semantics enters parse/type/MIR keys as declared. Incorrectly classifying a semantic option as untracked is a release-blocking cache-soundness bug.

Required rebuild matrix:

| Change | Compile work | Link work | `simple-core` | SCI |
|---|---:|---:|---:|---:|
| command alias/help | 0 | 0 | unchanged | regenerate section |
| exact option spelling/alias/help/value map | 0 | 0 | unchanged | regenerate option section |
| add/change extension namespace binding | 0 | 0 | unchanged | regenerate option/provider sections |
| provider adds a new `--xnamespace-key` with same ABI | provider only | provider package only | unchanged | update artifact digest if embedded |
| provider body change, ABI compatible | provider only | provider package only | unchanged | update digest |
| provider option ABI minor-compatible extension | provider + affected adapters | no root relink | unchanged | update interface metadata |
| core reserved grammar or option-wire ABI major | affected core/readers | core relink | rebuild | schema migration |

For `placement=auto`, a full release rebuild may fold an option implementation into its owning command/compiler/loader/interpreter capsule. It must not pull that implementation into stage-0 merely because it became static. This preserves the no-heavy-root principle while retaining development-time replacement.

---

## 6. Stage-0 `startup()` redesign

### 6.1 Stage-0 closure

The stage-0 executable contains only:

```text
[ process/ABI entry ]
[ fixed byte/span helpers ]
[ argv classifier ]
[ root help/version data ]
[ bounded SCI header/index reader ]
[ static component lookup table ]
[ exact module admission front door ]
[ minimal fatal write-to-stderr ]
[ direct exec / in-process dispatch port ]
```

It must not contain:

```text
GC                         scheduler
reflection                 async runtime
compiler parser            HIR/MIR
optimizer                   interpreter
Cranelift/LLVM              full SMF loader
runtime AOP                 logging framework
coverage/profile            UI/Office/IDE
project config parser       directory/plugin scanner
shell spawning              background compiler client
```

### 6.2 Entry flow

```text
_start / OS entry
        |
        v
simple_start(argc, argv, envp, auxv)
        |
        +-- argc == 1 ----------------------------> root default policy
        |
        +-- first token is -h/--help ------------> print embedded root help; exit
        |
        +-- first token is -v/--version ----------> print embedded version; exit
        |
        +-- core lexical/root flags --------------> parse invariant forms only
        |
        v
classify first command/path
        |
        +-- native executable --------------------> direct exec unless in-process requested
        +-- .smf ---------------------------------> loader.base capsule
        +-- source extension ---------------------> source execution capsule
        +-- known CLI-0 command ------------------> embedded or static command
        `-- other command/options ----------------> SCI route + option lookup
```

Root `--help` and `--version` do not open SCI. Subcommand help, such as `simple compile --help`, reads only the compact SCI command/option help index. A deliberately requested `--full` help view may load only the command provider, never the compiler engine or unrelated providers.

### 6.3 Invariant lexical grammar, generated option semantics

Stage-0 hardcodes only token shapes and the reserved root options listed in Section 5.7. It does **not** hardcode `--execution`, `--backend`, logging, optimization, UI, test, or future provider option names. For a non-root route it performs a bounded two-level lookup:

```text
token starts with --x
    -> parse namespace/key/value shape
    -> namespace SCI lookup
    -> collect structured provider extension arg

other token starts with --
    -> exact option SCI lookup in current scope
    -> apply plan patch or collect provider-forward arg

non-option token
    -> classify command/path or forward as positional arg
```

The first pass identifies the command/path and applicable option scopes without activating providers. The second pass applies generated route patches and groups provider option batches. Provider validation occurs only after the exact provider is admitted. No provider is loaded simply to parse argv.

A hard `--` terminator is honored before all generated routing. For direct program execution, unrecognized options are application arguments; only the reserved `--x` namespace and exact routes explicitly marked `after_entry=true` are intercepted. This prevents a new Simple option from stealing an application's existing option accidentally.

### 6.4 Allocation-free classifier

The classifier uses borrowed spans into `argv`, integer hashes, generated sorted/MPH indexes, and fixed small arrays. It performs no general text normalization, Unicode conversion, heap allocation, dictionary creation, provider activation, or environment enumeration. Option batches use caller-owned bounded spans; if the configured maximum is exceeded, startup fails before loading a provider.

Proposed low-level API:

```simple
struct StartupArgSpanV1:
    ptr: u64
    len: u32

struct StartupRequestV1:
    argv0: StartupArgSpanV1
    first: StartupArgSpanV1
    profile_id: u16
    core_flags: u32
    entry_kind: u8
    option_token_first: u16
    option_token_count: u16
    routing_boundary: u16

fn startup_classify_v1(argc: i32, argv: *u8) -> StartupRequestV1
```

A higher-level Simple adapter can expose text values after the selected runtime allocator exists.

### 6.5 `StartupPlanV1`

```text
StartupPlanV1
    route_kind
    command_id
    profile_id
    execution_mode
    target_id
    component_ids[]
    route_patch_ids[]
    provider_option_batches[]
    direct_exec_path
    entry_path
    program_arg_start
    load_policy
    cache_policy
    strictness
    plan_hash
```

The plan is deterministic for a fixed SCI, static table, arguments, environment allowlist, and artifact identities.

### 6.6 Startup receipts without startup overhead

Production stage-0 should not build a rich object graph. Use one of three evidence levels:

```text
none
    no receipt allocation

compact
    fixed-size StartupReceiptV1 written to caller buffer or event ring

full
    external probe reads load/open/map/exec evidence and joins it with compact receipt
```

`--diagnose-startup` activates compact/full evidence. Normal startup remains branch-minimal through a separately linked/instrumented stage-0 variant or one cold command-boundary branch, never per operation.

### 6.7 Config precedence

```text
1. build-sealed policy for security-critical constraints
2. exact `--config-index` when permitted
3. deployment SCI path embedded in stage-0
4. user SCI path when profile allows
5. built-in defaults
```

Stage-0 does not parse project SDN. Human CLI configuration is compiled to SCI ahead of startup; project configuration belongs to compiler/build capsules. A config-only command/option/namespace edit regenerates SCI atomically and performs zero source compilation and zero linking.

### 6.8 Direct native execution

For an installed native program:

```text
simple app [args]
    |
SCI route says native/direct_exec
    |
execve/CreateProcess/SimpleOS launch
```

The compiler, interpreter, SMF loader, and runtime aspect loader remain absent. For shell-installed wrappers, the fastest deployment is a direct symlink/shim to the native executable so even the universal launcher can be skipped where desired.

### 6.9 Source execution route

```text
source path
    |
exact source identity + dependency manifest lookup
    |
    +-- valid cached native image ----> direct exec / map admitted image
    +-- valid cached ExecIR ----------> interpreter.fast
    +-- valid cached SMF -------------> loader.base
    `-- cache miss -------------------> compiler.frontend + selected execution path
```

A cache hit may not require the source frontend. The cache key includes source/content identity, direct dependency interface hashes, compiler ABI, language semantics version, target, profile, aspects, optimizer/backend identities, and security policy.

### 6.10 Startup I/O policy

Do not make `mmap` the unconditional answer.

```text
small fixed SCI header/index
    -> pread/read exact bytes

large SMF/native segments
    -> map selected page-aligned segments

small compact ExecIR
    -> bounded read into execution arena may be faster

explicit declared preload
    -> selected read-ahead/page touch

root help/version
    -> no external I/O
```

The performance harness chooses thresholds from evidence per target. It records bytes read, page faults, mappings, and syscalls so a faster wall-clock result cannot hide excessive I/O.

### 6.11 Cross-platform ports

```text
StartupHostPortV1
    read_exact(path, offset, span)
    map_readonly(path, offset, size)
    map_exec_image(plan)
    direct_exec(path, argv, env_allowlist)
    protect(region, mode)
    page_size()
    monotonic_time_optional()
    fatal_write(bytes)
```

Implementations:

- Linux/POSIX;
- Windows (`CreateFileW`, `ReadFile`, `CreateFileMappingW`, `MapViewOfFile`, `CreateProcessW`);
- SimpleOS VFS/process loader;
- bare-metal static table with no filesystem loader.

### 6.12 Stage-0 budgets

Initial structural budgets, to be evidence-adjusted:

```text
root code/text closure           <= 256 KiB host target
root writable state              <= 32 KiB before selected runtime
heap allocations for help/version = 0
external file opens for help/version = 0
optional module mappings for help/version = 0
constructors outside stage-0      = 0
provider loads while parsing argv   = 0
config-only CLI option edit compile = 0 modules
config-only CLI option edit links   = 0
```

The existing ~14 KiB core-C startup audit is a stronger proof-of-possibility than the 256 KiB ceiling. The larger ceiling allows a robust multi-platform self-hosted implementation while the release stretch target remains substantially lower.

---

## 7. Aspect stripping and dynamic activation

### 7.1 Aspect taxonomy

```text
startup aspects
    startup.trace
    startup.profile
    startup.audit

loader aspects
    loader.trace
    loader.relocation_debug
    loader.symbol_debug
    loader.integrity_strict
    loader.hot_reload

interpreter aspects
    interp.trace
    interp.calltrace
    interp.profile
    interp.coverage
    interp.strict_ub
    interp.debugger

compiler aspects
    compiler.phase_trace
    compiler.ast_dump
    compiler.hir_dump
    compiler.mir_dump
    compiler.optimization_remarks
    compiler.coverage
    compiler.profile
    compiler.formal

runtime aspects
    log.error
    log.warn
    log.info
    log.debug
    log.trace
    sanitize
    leak_check
    fault_injection
    telemetry
```

### 7.2 Logical facets versus physical packs

Do not create one tiny shared object per log level. Preserve logical selection while grouping physical files:

```text
aspect.log.basic.pack
    log.error
    log.warn

aspect.log.standard.pack
    log.info

aspect.log.debug.pack
    log.debug

aspect.log.trace.pack
    log.trace
    calltrace
    perf-events
```

The descriptor index selects facets inside an admitted pack. Deployments may regroup packs without changing facet IDs or pointcut contracts.

### 7.3 Disabled aspect path

```text
configuration says off
        |
composition excludes facet
        |
weaver/generator emits no callsite or import slot
        |
linker sees no pack dependency
        |
startup index contains no activation edge
        |
ZERO runtime residue
```

A normal interpreter loop must not contain:

```text
if trace_enabled
if debug_log_enabled
logger.log(...)
lookup advice list
allocate Any[]
```

### 7.4 Instrumentation readiness levels

A module declares one readiness level:

```text
none
    no instrumentation sites; enabling requires recompilation/rebuild

boundary
    stable cold-boundary import slots exist for module/function lifecycle events
    aspect may activate without rebuilding inner loops

full
    instrumented variant contains patchable sites/ExecIR event opcodes
    intended for debug/profile builds
```

Stage-0, loader.base, and fast production interpreter default to `none` or narrowly `boundary`. Full tracing uses a separate instrumented closure; arbitrary full tracing cannot be promised on a binary whose callsites were intentionally stripped.

### 7.5 Aspect activation sequence

```text
trigger reached
    |
resolve facet descriptor from already-admitted pack index
    |
verify capability and pointcut scope
    |
admit exact pack path/digest/ABI/interface hash
    |
resolve every required symbol now
    |
pin pack
    |
install immutable dispatch table / patch cold boundary slot
    |
emit AspectActivationReceiptV1
```

There is no directory search, global symbol interposition, or lazy unresolved symbol binding.

### 7.6 Aspect ABI

```text
AspectFacetV1
    facet_id
    facet_version
    pointcut_schema_hash
    required_event_schema_hash
    activation_kind
    thread_safety
    reentrancy
    payload_policy
    security_class
    before_fn?
    after_fn?
    around_fn?
    flush_fn?
```

Payloads use typed fixed records or spans, not `Any` and arbitrary closure capture at core boundaries. Full-language adapters may wrap typed payloads for rich tooling outside the base.

### 7.7 Logging design

The mandatory core contains only a fatal path suitable for reporting an admission or process-start failure:

```text
fatal_write(code, bounded_message)
```

Normal logs are aspects. Compile-time elimination rules:

| Requested level | Included logical facets |
|---|---|
| off | none |
| error | error |
| warn | error, warn |
| info | error, warn, info |
| debug | error, warn, info, debug |
| trace | all selected trace facets |

For firmware/site-ID logging, the callsite may encode only a compact site ID and typed values while host tooling reconstructs text from debug metadata. That facility is still an explicit logging aspect, not a default runtime dependency.

### 7.8 Static/dynamic aspect lifecycle

```text
aspect placement=auto
    developer modifies aspect
        -> build aspect pack only
        -> SCI points to new implementation hash
        -> old static hash differs
        -> dynamic pack activates

    full runtime/compiler rebuild
        -> aspect source folded into selected static profile
        -> static hash matches SCI
        -> no dynamic pack load

aspect placement=dynamic
    -> always external

aspect presence=off
    -> excluded statically and dynamically
```

### 7.9 Security policy

- Security-critical integrity/authorization aspects may be build-sealed static requirements.
- A dynamic aspect never gains more authority than its descriptor capability set.
- Payload collection is redacted and bounded by policy.
- Production runtime AOP defaults off.
- Dynamic unload defaults prohibited; module replacement uses a new generation and safe handoff.
- Mission-critical mode rejects unsigned or unproven aspect packs and rejects runtime instrumentation not listed in the deployment policy.

### 7.10 Aspect proof obligations

Generated/formal checks:

```text
CoreNoAspectDependency
DisabledFacetAbsentFromPlan
StaticDynamicFacetSemanticParity
FacetDependencyAcyclic
FacetCapabilityMonotonic
FacetPayloadBounded
AutoPlacementDeterministic
NoStaleStaticSelection
```

---

## 8. Loader redesign

### 8.1 Split the loader into a mandatory base and optional capabilities

```text
loader.base
    artifact identify
    bounded header/directory read
    ABI/digest/capability admission
    segment plan
    mapping
    relocation
    exact import resolution
    export lookup
    entry transfer

loader.cache                 optional
loader.compiler_bridge       optional
loader.generic_instantiation optional
loader.jit                   optional
loader.hot_reload            optional
loader.remote_resolver       optional
loader.debug                 optional aspect/capability
loader.lifecycle_full        optional
```

`loader.base` must not construct a compiler context, generic instantiator, JIT engine, hot-reload generation manager, remote resolver, or rich lifecycle graph.

### 8.2 Loader configurations

```text
ModuleLoaderConfigV2
    cache_policy: off | exact | persistent
    jit_policy: off | on_demand
    generic_instantiation: off | on_demand
    hot_reload: off | generation_swap
    diagnostics: none | compact | full
    security: normal | strict | mission_critical
```

Base defaults:

```text
cache_policy = off or exact-readonly according to route
jit_policy = off
generic_instantiation = off
hot_reload = off
diagnostics = none
```

A source/JIT route can compose `loader.base + loader.jit + compiler_bridge`; an ordinary precompiled SMF route does not.

### 8.3 SMF vNext segment model

The normal load path should resemble an executable loader rather than a symbol copier.

```text
SMF header/trailer
    fixed magic/version/target/ABI
    directory offset/size
    content digest
    interface hash
    implementation hash
    signature metadata

segments
    RX code/read-only executable helpers
    R  constants/metadata/export strings
    RW mutable data
    BSS zero-fill description

indexes
    imports
    exports
    relocations
    capabilities
    dependencies
    launch metadata
    debug/aspect metadata optional
```

Proposed segment entry:

```text
SmfSegmentV2
    kind
    flags              # R/W/X, compressed, discardable
    file_offset
    file_size
    memory_size
    alignment
    virtual_offset
    content_digest
```

### 8.4 One mapping per segment, not per symbol

Current normal behavior to retire from the fast path:

```text
for each exported symbol:
    read code bytes
    allocate RW memory
    copy bytes
    change protection
    flush instruction cache
    register symbol
```

Target:

```text
validate directory
    |
create complete LoadPlanV1
    |
reserve module address space
    |
map/copy RX, R, RW segments once each
    |
apply compact relocations while writable through safe mapping policy
    |
make final protections
    |
flush instruction cache once per changed code range
    |
resolve/register export index
```

### 8.5 W^X mapping strategies

Preferred order by host capability:

1. dual mapping of the same backing storage: one RW alias and one RX alias;
2. temporary RW anonymous/file-backed mapping, relocate, then transition to RX;
3. platform JIT write-protect API where required;
4. strict failure when no safe executable mapping exists.

Never create a simultaneously writable and executable segment. The executable stack is prohibited. Strict profiles require RELRO-equivalent sealing of import/export and immutable metadata after activation.

### 8.6 Relocation format

Use a compact typed relocation stream sorted by target segment and offset:

```text
RelocBlockV1
    target_segment
    relocation_kind
    base_offset
    count
    delta_encoded_offsets[]
    symbol_or_segment_indices[]
    addends[]
```

Optimize common relative relocations separately. The loader validates every target and source range before mutating memory. Malformed, overlapping, out-of-range, unsupported, or writable-to-executable policy violations fail before entry transfer.

### 8.7 Export lookup

Build-time generate:

- a minimal-perfect-hash table when stable/beneficial;
- otherwise a compact sorted hash/index table;
- optional ordinal IDs for closed static dependency sets.

Runtime export lookup compares the stored full stable name when hashes collide. No global process-wide string dictionary is required for a module with closed ordinal imports.

### 8.8 Import resolution policy

Dynamic loading is lazy at the **module/capability level**, but symbol binding inside an activated module is eager and fail-closed:

```text
selected module not used
    -> not loaded

selected module activates
    -> all declared direct dependencies admitted
    -> all required imports resolved
    -> immutable import slots sealed
    -> constructors/initializers run in topological order
```

This avoids the runtime unpredictability of arbitrary lazy binding while preserving Simple's desired component modularity.

### 8.9 Static implementation path

Static components are represented by the same logical export/import index:

```text
StaticComponentEntryV1
    component_id
    interface_hash
    implementation_hash
    export_table
    initialization_fn
    capability_set
```

The resolver returns a static export table without invoking the dynamic loader. Static/dynamic parity tests invoke the same conformance suite through the same port.

### 8.10 `LoadPlanV1`

```text
LoadPlanV1
    artifact_path
    artifact_kind
    target
    ABI/interface/implementation identities
    dependency_order[]
    segment_plans[]
    relocation_summary
    import_count
    export_count
    load_policy
    security_policy
    cache_identity
    plan_hash
```

Planning is side-effect-free. The loader first validates the complete plan, then performs mappings and relocations transactionally.

### 8.11 `LoadReceiptV1`

```text
LoadReceiptV1
    artifact_digest
    plan_hash
    selected_provider
    static_or_dynamic
    bytes_read
    bytes_mapped
    segment_count
    relocation_count
    resolved_import_count
    page_faults_optional
    protection_transitions
    cache_status
    generation
    result
    failure_reason
```

Production `none` evidence mode can omit the receipt. Test/profile mode must obtain equivalent evidence from a fixed buffer plus external syscall/mapping probes.

### 8.12 Cache design

Loader cache tiers:

```text
header/directory cache
    exact artifact digest -> validated compact directory

relocation plan cache
    artifact + load address policy + direct dependency export identities

native image cache
    exact semantic/build identity -> admitted mapped image description

negative resolution cache
    generation + caller + module name + search-policy identity -> exact miss
```

The existing negative module-resolution cache tests should be retained and extended. Resetting a generation invalidates negative results. A missing module must not cause repeated file-existence storms.

### 8.13 Hot reload

Hot reload remains optional and outside loader.base:

```text
admit new generation
    |
construct and validate complete mapping
    |
resolve imports against declared generation policy
    |
quiescence/ownership check
    |
atomic dispatch-table swap
    |
old generation retained until no users
```

No in-place overwrite of a mapped artifact. Updates write a new immutable path and atomically rename the deployment descriptor.

### 8.14 Generic instantiation/JIT

A precompiled module may declare unresolved generic templates, but the ordinary base loader must not create a compiler automatically. Possible policies:

```text
closed
    build rejects unresolved runtime instantiation

preinstantiated
    required generic instantiations included in artifact

on_demand
    loader activates compiler_bridge + JIT only when a missing declared
    instantiation is first requested
```

Tiny and mission-critical profiles default `closed` or `preinstantiated`.

### 8.15 Loader performance targets

Targets are ratios measured on the same pinned host:

| Lane | Initial admission target | Stretch target |
|---|---:|---:|
| root help/version loader activity | zero module loader mappings | same |
| tiny SMF load-to-entry | <= 1.5x comparable OS shared-object load | <= 1.1x |
| bytes read for entry | directory + selected segments only | no unselected segment pages |
| protection transitions | O(segments), not O(symbols) | one final seal per mutable code range |
| export lookup | bounded O(1) or O(log n) | generated MPH for hot modules |
| missing-module repeated probe | one uncached generation lookup | same |
| base loader heap | bounded arena; no compiler/JIT objects | no general dictionary for closed module |

### 8.16 Loader compatibility strategy

Keep existing loaders as named reference/compatibility providers:

```text
loader.reference.current
loader.compat.symbol_copy
loader.v2.segment
```

The route policy initially selects reference for unsupported SMF versions. New V2 artifacts select the segment loader. Once parity, security, and performance gates pass, V2 becomes default; compatibility remains explicit and removable from tiny closures.

---

## 9. Fast interpreter and tiered execution

### 9.1 Preserve the reference interpreter

The direct MIR evaluator remains the semantic oracle for:

- compiler bring-up;
- differential testing;
- unsupported-platform fallback;
- debugger/reference mode;
- validation of ExecIR lowering and JIT code generation.

Do not optimize it by hiding semantics behind unsafe shortcuts. Performance work goes into a distinct fast interpreter.

### 9.2 ExecIR V1

ExecIR is a typed, compact, register-oriented bytecode produced after semantic checking and essential MIR normalization.

```text
source
  -> frontend
  -> typed HIR
  -> MIR
  -> mandatory canonicalization
  -> ExecIR V1
       +-> fast interpreter
       +-> Baseline/Cranelift compiler
       +-> optimized LLVM compiler
       +-> persistent bytecode cache
```

Properties:

- stable versioned opcode schema;
- typed registers/slots;
- dense function and block IDs;
- explicit control-flow edges;
- compact constants and metadata indexes;
- source/span map in optional side section;
- exception/deopt/OSR tables;
- ownership/effect facts required at runtime boundaries;
- no dependence on source text for execution or tier promotion.

### 9.3 Typed register lanes

A frame uses dense arrays or a generated compact layout:

```text
ExecFrameV1
    pc
    function_id
    caller_frame
    i64_slots[]
    f64_slots[]
    ref_slots[]
    vector_slots[] optional
    spill_bytes[]
    exception_state
```

For small functions, a unified 64-bit slot array plus a static slot-kind table may have better locality. The generator chooses and benchmarks layouts; the ABI does not expose internal pointers.

The hot path must not use dictionaries for local IDs, block IDs, or function lookup.

### 9.4 Typed opcodes

Examples:

```text
CONST_I64          dst, const_index
MOVE_I64           dst, src
ADD_I64            dst, lhs, rhs
ADD_F64            dst, lhs, rhs
CMP_LT_I64         dst, lhs, rhs
LOAD_FIELD_I64     dst, object, field_offset
STORE_FIELD_I64    object, field_offset, src
BR_TRUE            cond, target_block
CALL_DIRECT        dst, function_id, arg_base, arg_count
CALL_INTERFACE     dst, cache_id, interface_slot, receiver, args
RETURN_I64         src
```

Static type knowledge eliminates runtime type tests for ordinary arithmetic and local access.

### 9.5 Generated opcode source

One declarative opcode table generates:

- enum/opcode numbers;
- operand layouts;
- decoder;
- switch dispatcher;
- computed-goto dispatcher where supported;
- tail-call handlers where supported;
- disassembler;
- verifier;
- profiler counters for instrumented builds;
- Cranelift template lowering;
- documentation and binary golden vectors.

No hand-maintained drift among interpreter, verifier, disassembler, and JIT.

### 9.6 Dispatch variants

```text
portable
    generated switch/match

fast host
    computed goto / labels-as-values where supported

tail-call
    small opcode handlers with guaranteed tail calls on qualified compilers

embedded
    compact switch tuned for code size
```

All variants execute the same opcode semantics and pass differential tests.

### 9.7 Quickening

ExecIR starts with generic typed boundary operations only where runtime evidence is needed:

```text
CALL_INTERFACE_ADAPTIVE
LOAD_DYNAMIC_FIELD_ADAPTIVE
VARIANT_DISPATCH_ADAPTIVE
MODULE_IMPORT_ADAPTIVE
GENERIC_CALL_ADAPTIVE
```

After a counter reaches zero, the instruction specializes in place or into a per-session shadow copy:

```text
CALL_INTERFACE_MONO
CALL_INTERFACE_POLY2
CALL_DIRECT_CACHED
LOAD_FIELD_SHAPE
MODULE_IMPORT_RESOLVED
```

Each specialized form contains minimal guards and deoptimizes to its base family on failure. Immutable on-disk ExecIR remains unchanged; process-local quickened code can be discarded.

### 9.8 Inline caches

Cache records are compact and instruction-adjacent:

```text
InterfaceCallCacheV1
    expected_type_id
    method_generation
    target_function_id

ModuleImportCacheV1
    provider_generation
    export_ordinal
    address_or_handle
```

Avoid pointer chasing and general dictionaries. Cache miss counters decide whether another specialization is profitable.

### 9.9 Superinstructions

Profile-guided generation can fuse frequent sequences:

```text
LOAD_CONST_I64 + ADD_I64 + STORE_LOCAL_I64
    -> ADD_CONST_LOCAL_I64

CMP_LT_I64 + BR_TRUE
    -> BR_LT_I64

LOAD_FIELD_REF + NULL_CHECK + CALL_DIRECT
    -> CALL_FIELD_DIRECT_NONNULL
```

Only fusions with proven semantic equivalence and measurable wins are admitted. The generator retains a reversible mapping to base opcodes for debugging and formal checks.

### 9.10 Function calls

Call overhead is reduced through:

- dense function table;
- fixed calling convention shared with JIT tiers;
- preallocated frame arena;
- direct-call opcodes after resolution;
- tail-call opcode where valid;
- small function inlining during ExecIR lowering for configured budgets;
- return-value slots without boxed `Any`.

### 9.11 Memory and object model

Fast scalar operations remain unboxed. References use stable handles or direct pointers according to runtime profile. GC barriers are generated only for reference stores in a GC-enabled profile. No-GC/tiny profiles omit GC tables/barriers entirely when verified safe.

```text
integer arithmetic -> raw integer slots
floating arithmetic -> raw floating slots
references -> ref slots
variants -> compact tag + typed payload location
text/array -> runtime handles with specialized common operations
```

### 9.12 Tiering

```text
Tier 0A: generic typed ExecIR
    immediate execution; lowest latency

Tier 0B: quickened/specialized ExecIR
    inline caches, superinstructions, direct calls

Tier 1: Cranelift baseline/fast native
    compile hot functions/loops from ExecIR or MIR

Tier 2: LLVM optimized native
    expensive, concurrent, only for sufficiently hot/long-lived code
```

The policy uses time and work estimates rather than one global call count:

```text
benefit = estimated_interpreter_cost_saved
cost    = measured/predicted_compile_cost + code_memory_cost
promote when benefit > cost * safety_factor
```

Profile classes provide initial thresholds; counters adapt from actual compilation and execution receipts.

### 9.13 Lazy JIT creation

The interpreter session contains no JIT engine until a Tier 1 candidate is admitted:

```text
cold/short program
    -> no Cranelift library, context, threads, or code cache mapping

hot candidate
    -> activate backend.cranelift through component resolver
    -> create JIT service
    -> compile typed function
```

Tier 2 LLVM is independently activated. Tiny/strict-interpreter profiles can prohibit all JIT activation.

### 9.14 Compile from typed IR, never source text

Tier promotion receives:

```text
function ExecIR/MIR
resolved type/layout tables
constant pool
profile data
exact dependency generations
aspect/instrumentation identity
```

It must not re-read or reparse the source file. A sabotage test deletes/renames the source after ExecIR creation; valid Tier 1 compilation must still succeed and produce the same result.

### 9.15 OSR and deoptimization

OSR points exist at verified loop headers, call returns, and selected safepoints.

```text
interpreter frame
    -> OSR map
    -> native frame/state
    -> execute Tier 1/2

failed speculation / invalidated generation
    -> deopt map
    -> reconstruct ExecIR frame
    -> continue at defined PC
```

Ownership, GC roots, exception state, and aspect readiness are part of the map. No arbitrary instruction can be an OSR point.

### 9.16 Concurrent compilation

- one bounded high-priority Tier 1 queue;
- lower-priority Tier 2 queue;
- immutable compile requests;
- worker-local arenas;
- no blocking of the executing thread after a request is queued;
- memory-pressure policy can cancel/defer Tier 2 first;
- build/bootstrap compiler work retains priority over performance test lanes.

### 9.17 Persistent code cache

Key:

```text
ExecIR function hash
+ direct dependency interface hashes
+ target/CPU features
+ runtime ABI
+ backend version
+ optimization profile
+ aspect/instrumentation identity
+ security policy
```

A cached native function is admitted through the same loader security and relocation path. On invalidation, execution remains in ExecIR until a new compile completes.

### 9.18 Debugging and tracing

Production fast interpreter:

```text
no trace opcode
no debug branch
no per-op counter
```

Instrumented variants:

- shadow ExecIR with event opcodes;
- generated counter-enabled dispatcher;
- boundary-only debugger slots;
- reference interpreter for semantic stepping.

Debugger attach policy must say what is possible without recompilation. It must not claim full instruction tracing for a stripped binary.

### 9.19 Interpreter target matrix

| Lane | Admission target | Stretch target |
|---|---:|---:|
| fresh typed source startup, interpreter | <= local CPython `-S` equivalent | <= local Bun source hello |
| typed scalar geomean | >= 3x CPython | within 2.5x native Go/Rust |
| collections/text geomean | >= 2x CPython where semantics match | competitive with non-optimizing JS tier |
| quickening overhead on non-specializable code | < 3% | < 1% |
| Tier 1 warm kernels | within 1.5x best Go/Rust AOT | within 1.25x |
| Tier 2 warm kernels | within 1.2x best Go/Rust/C | within 1.1x |
| cold short program | no JIT mapping | same |

These are targets. They become claims only after the current self-hosted identity and statistical benchmark gates pass.

---

## 10. Compiler architecture and compile-time performance

### 10.1 Split compiler engine from command/UI surfaces

```text
compiler.frontend
    lexer/parser
    mandatory desugar
    source identities

compiler.semantic
    name/type/effect/ownership checks
    public interface extraction

compiler.mir
    typed lowering
    canonicalization

compiler.execir
    MIR -> ExecIR lowering and verification

compiler.opt.basic
    cheap canonical passes

compiler.opt.pack.*
    vectorization, aggressive inline, GPU, domain passes

backend.cranelift
backend.llvm
backend.c
backend.wasm
backend.cuda
backend.vhdl

compiler.cli
    argument/help/report rendering

compiler.tools.*
    lint, fmt, coverage, dumps, formal, IDE services
```

The stage-0 route `compile` loads `compiler.cli` plus the selected engine modules. Root help does not. `compile --help` loads only the command/help capsule unless backend enumeration was explicitly requested.

### 10.2 Simple Interface Format (SIF)

Create an indexed compiled interface artifact, building on existing HIR/MIR/cache identities:

```text
SIF Header V1
    module semantic identity
    language semantics version
    interface schema version
    direct dependency interface hashes
    index offsets
    content digest

Indexed entities
    exported declarations/types
    trait/interface implementations
    effects and ownership summaries
    public aspect/pointcut facts
    constant values
    inline candidate bodies
    generic bodies/constraints
    escape/alias/layout summaries
    source anchors/debug references optional
```

A compiler of module Q reads SIFs for Q's direct imports. Entries are decoded lazily by entity ID. Tooling may use a shallower view; distributed/release builds may use a deep direct-dependency summary. The representation choice is explicit rather than accidental.

### 10.3 Exact query DAG

Queries are stable functions over exact keys:

```text
parse(file_content_hash, language_version)
collect_module_interface(module_id, parsed_item_hashes)
resolve_name(scope_id, name_id, import_interface_hashes)
type_check(body_id, interface_context_hash)
borrow_check(body_id, typed_body_hash, policy_hash)
lower_mir(body_id, typed_body_hash)
optimize_mir(body_id, mir_hash, pass_set_hash, target_hash)
lower_execir(body_id, optimized_mir_hash, execir_schema_hash)
codegen_unit(unit_id, optimized_ir_hash, backend_hash, target_hash)
link(product_id, object_hashes, runtime_closure_hash)
```

Store:

- query key/fingerprint;
- ordered dependency reads;
- result fingerprint;
- optional serialized result for expensive queries;
- diagnostics fingerprint;
- provenance and schema version.

If an input changes but the query result fingerprint is unchanged, dependents remain green.

### 10.4 Reuse existing CAS

Extend current cache records rather than adding a competing cache root:

```text
CAS object
    object kind
    schema version
    semantic key
    content digest
    dependency digests
    target/profile identity
    producer identity
    payload
    integrity checksum
```

Tiers:

```text
source/token/AST
module interface/SIF
HIR/type/effect/borrow
MIR
optimized MIR per pass set
ExecIR
object/codegen unit
SMF/native image
startup SCI
aspect match set/woven variant
```

### 10.5 Body versus interface invalidation

```text
function body changes, public interface unchanged
    -> parse/body/type/MIR/opt/codegen for affected body
    -> module SIF public hash remains green
    -> importers remain green

public signature/effect/ownership/layout changes
    -> module interface hash changes
    -> exact dependent queries invalidated

aspect implementation changes, pointcut contract unchanged
    -> dynamic aspect module only in development
    -> woven callers invalidated only when static/instrumented build uses it

aspect pointcut/match set changes
    -> recompute match-set query
    -> invalidate exactly matched bodies and dependent artifacts
```

### 10.6 AOP cache identities

Separate:

```text
aspect contract hash
aspect implementation hash
pointcut query hash
matched symbol/body ID set hash
weave order hash
payload/event schema hash
```

This prevents every aspect edit from invalidating the whole compiler or application while preserving correctness.

### 10.7 Development versus release pipelines

```text
dev-fast
    incremental queries
    mandatory frontend normalization
    cheap MIR passes
    no LTO
    Cranelift or fast backend
    multiple codegen units
    debug info bounded

release
    exact clean/validated cache inputs
    full profitable pass plan
    LLVM or selected production backend
    LTO/PGO when configured
    static folding of placement=auto defaults
    complete closure/security/size certification

tiny-release
    same semantic checking
    strict capability closure
    no unused runtime families
    abort/minimal failure policy where declared
    selected backend optimized for size/startup
```

`dev-fast` is not allowed to skip semantic correctness checks. It changes optimization and artifact-placement policy, not language rules.

### 10.8 Complete dynamic optimization support

One optimizer contract covers source, MIR, and target/backend policy:

```text
OptimizerPluginV1
    stable_id
    interface_version/hash
    implementation_hash
    scope: source | MIR | both
    phase
    ordering constraints
    required analyses
    preserved analyses
    target/backend policy
    cost class
    purity/determinism
    entry functions
```

Required completion work:

1. dynamic entry symbols invoke a real implementation;
2. source optimizers receive a stable source/HIR transform view;
3. MIR optimizers receive typed MIR/analysis handles;
4. dynamic passes report preserved/invalidated analyses;
5. the pipeline planner topologically orders static and dynamic passes;
6. duplicate stable IDs/aliases are rejected;
7. built-in and dynamic implementations use the same conformance tests;
8. `placement=auto` follows the implementation-hash rule;
9. a full compiler rebuild statically folds configured default passes;
10. `placement=dynamic` always loads externally.

### 10.9 Frontend transforms versus optional optimization

Keep mandatory normalization static/common:

```text
required desugar
    async/generator semantic lowering
    placeholder/lambda normalization
    pattern normalization
    semantics-preserving canonicalization required by later stages
```

Optional source profitability transforms can be static or dynamic:

```text
source loop canonicalization
collection idiom rewrite
constant/source simplification
DSL/domain rewrite
profile-guided source transform
```

A dynamic frontend optimizer may not redefine syntax or bypass semantic validation. Its output re-enters the canonical validation pipeline.

### 10.10 Backend-specific optimization

Separate common MIR optimization from backend-native optimization:

```text
common MIR pass plan
    target-independent canonical and profitable transforms

backend policy
    skip/retain common passes according to backend guarantees

backend optimizer pack
    machine/ABI/instruction-specific transforms
```

LLVM may skip Simple passes that LLVM performs better; Cranelift may retain low-cost Simple passes; embedded/VHDL/GPU backends select distinct packs. The selection is typed policy, not scattered string comparisons.

### 10.11 Parallel compilation

Parallelize only after exact ownership and immutable result boundaries exist.

Good units:

- independent source-file parsing;
- body type checking after interface collection;
- borrow/effect checks per body/region;
- MIR optimization per function where pass scope permits;
- codegen units;
- independent backend modules;
- cache serialization/compression;
- high-tier JIT requests.

Serial/global units:

- schema/contract initialization;
- module public interface fixpoint;
- global coherence checks that truly require whole-program state;
- module-level passes;
- final link/composition;
- release certification.

Use worker-local arenas and immutable shared query results. Avoid one global mutable registry lock. The scheduler must throttle under memory pressure; parallelism that triggers early-OOM is a regression.

### 10.12 Compiler service/daemon

An optional per-workspace compiler service may retain:

- mapped SCI/SIF indexes;
- query DAG/fingerprints;
- immutable parsed/typed/MIR/ExecIR objects;
- backend services;
- file watcher state;
- bounded cache hot set.

It is never required for correctness and never part of stage-0. The CLI uses an exact protocol/ABI and falls back to an in-process compiler capsule when the service is absent or incompatible.

### 10.13 Compiler memory policy

- memory-map large immutable CAS objects on demand;
- lazy decode indexed SIF entities;
- release body-local arenas after result serialization;
- retain hashes without retaining every value;
- bound monomorphization/generic queues;
- separate resident hot cache from disk/global CAS;
- expose high-water counters in profile builds;
- give bootstrap/build lanes CPU and memory priority over verification lanes;
- cancel/defer optional Tier 2/JIT/profile work first under pressure.

### 10.14 Compile-time comparison lanes

```text
C0: parser-only equivalent source
C1: semantic check/type check
C2: dev object/bytecode output
C3: dev linked executable
C4: release optimized executable
C5: warm no-op rebuild
C6: one function-body edit, interface stable
C7: public interface edit
C8: optimizer implementation-only dynamic rebuild
C9: compiler core edit requiring compiler rebuild
C10: full bootstrap/release certification
```

Do not compare Python bytecode generation with LLVM release LTO as one "compile time" number.

### 10.15 Compiler target matrix

| Lane | Admission target | Stretch target |
|---|---:|---:|
| root `compile --help` | no engine load | same |
| tiny cold dev compile | <= local Rust dev comparable product | approach/local Go build |
| warm no-op | <= 10% of cold dev | <= 5% |
| one body change | beat Go and Rust comparable incremental lane | proportional to affected query closure |
| config-only placement change | compiled modules = 0; linked objects = 0; SCI only | same |
| optimizer implementation-only dev edit | rebuild one optimizer artifact; compiler core unchanged | same plus hot reload into service |
| release AOT runtime performance | within 1.1x best equivalent Go/Rust/C baseline | parity/better on selected workloads |
| compiler peak RSS | bounded per profile; no unbounded graph retention | lower than current self-hosted baseline by evidence |

Absolute millisecond budgets are generated after the new harness rebaselines the current SHA on pinned hardware.

---

## 11. Default, tiny, full, and instrumented profiles

### 11.1 Default profile

```text
profile = normal
```

Normal provides expected language semantics and common runtime capabilities. It does not eagerly map every available component.

```text
available but lazy:
    compiler engine for compile/source miss
    interpreter for interpret/source cache
    loader for SMF/dynamic module
    JIT backends
    GUI/Office/IDE

absent unless requested:
    debug/trace/profile/coverage/sanitizer
    runtime AOP
    expensive/uncommon optimizer packs
```

### 11.2 Tiny profile

```text
profile = tiny
```

Tiny is strict and explicit. Capability analysis computes the minimum valid closure. A required unsupported capability causes a build error rather than silently upgrading to normal/full.

Candidates for physical absence when unused:

- GC and barriers;
- scheduler, threads, async;
- reflection/type registry;
- dynamic loader;
- interpreter/JIT/compiler;
- unwinding;
- runtime AOP;
- logging/tracing;
- filesystem/network;
- GUI/GPU;
- locale/Unicode/vector-font packs;
- remote services.

Tiny can still be a GUI, server, or embedded profile when those exact capabilities are selected. It does not mean CLI-only.

### 11.3 Full profile

```text
profile = full
```

All installed standard capabilities are available, but command/first-use activation remains lazy. Full must not mean "load LLVM, GUI, debugger, GPU, and Office at every process start."

### 11.4 Instrumentation overlays

```text
instrument = none | error | debug | trace | coverage | profile | sanitize
```

Overlays select aspect facets and may choose instrumented module variants. They do not create new language semantics.

### 11.5 Native runtime closure

A tiny native Simple program can plausibly be lighter than standard Go when it requires no scheduler, GC, reflection, dynamic loader, or runtime aspect machinery. This is a target to verify, not a current general claim.

```text
Simple tiny native hello
    OS loader
    minimal process/runtime entry
    print/write support
    main

No universal launcher, compiler, interpreter, JIT, scheduler, GC, or aspect pack.
```

### 11.6 Installed source versus installed native

Recommended deployment choices:

```text
development
    simple app.spl
    cache + interpreter/JIT + dynamic changed modules

installed tool
    native executable or closed SMF/ExecIR bundle
    parsing moved to build time

embedded/tiny
    statically closed native/SMF image
    optional packs only when platform policy permits
```

---

## 12. Performance measurement and admission

### 12.1 Fair benchmark lanes

| Lane | Simple | Required comparison |
|---|---|---|
| root tool dispatch | `simple --version`, root help | `go version/help`, `rustc --version`, `bun --version`, `python -V` with output-normalized submetrics |
| native hello | Simple AOT native | Go/Rust/C native hello |
| source hello | fresh `.spl` interpreter/JIT | Python, Bun, `go run`, `cargo run` as appropriate |
| cached source | exact ExecIR/SMF/native cache hit | Bun bytecode/compiled path, Python `.pyc`, warm `go run` cache |
| interpreter throughput | fast ExecIR | CPython and JSC low tier where obtainable |
| warm tiered runtime | Cranelift/LLVM JIT | Bun/JSC warm, Go/Rust AOT |
| compiler dev | Simple dev artifact | Go build, Rust dev, Bun transpile/bytecode with equivalent product |
| compiler release | optimized native | Go/Rust release/native |
| loader | SMF segment activation | OS shared-object/executable loader for equivalent module |

### 12.2 Metrics

Every startup run records:

- time to first instruction/route decision where instrumentable;
- time to first output byte;
- total process wall time;
- user/system CPU;
- peak RSS/PSS where supported;
- minor/major page faults;
- file opens/stats;
- bytes read;
- mapping count and mapped bytes;
- loaded module identities;
- relocation count;
- protection transitions;
- child process count;
- exit/result/checksum evidence.

Compiler runs additionally record:

- parsed files/blocks;
- typed bodies;
- MIR/ExecIR units produced;
- query red/green counts;
- cache hit/miss by tier;
- codegen units;
- linked objects;
- peak memory/high-water arenas;
- phase timings and critical path.

Interpreter/JIT runs record:

- base and specialized opcode counts;
- cache hit/miss/deopt;
- superinstruction counts;
- Tier 1/2 requests/completions/cancellations;
- OSR/deopt counts;
- code cache hit/miss;
- execution checksum.

### 12.3 Sampling

Minimum release profile:

```text
startup/CLI:
    30 warmups where appropriate
    50 measured process runs
    cold-file-cache lane separately and explicitly privileged

micro/runtime:
    sufficient iterations for >= 500 ms measured work per sample
    20 or more independent samples

compiler:
    20 paired old/new samples for stable small/medium suites
    larger suites at least 10 paired samples
```

Report p50, p95, max, dispersion, and confidence/statistical comparison. Do not publish only the fastest run or a single average.

### 12.4 Environment control

- immutable binaries named by SHA/digest;
- exact compiler/runtime versions;
- CPU affinity;
- stable performance governor/perflock where permitted;
- isolated workspace and cache directories;
- output redirected consistently;
- network disabled for unrelated lanes;
- fixed environment allowlist;
- container quota recorded but not confused with scheduler width;
- background load noted;
- thermal/frequency anomalies rejected;
- old/new runs interleaved or randomized to reduce drift.

Bun's official documentation recommends `hyperfine` for CLI measurement; Go's compiler documentation recommends repeated benchmark samples, `benchstat`, and `perflock`. The Simple harness should support both external tools while keeping its own machine-readable receipt contract.

### 12.5 Gate levels

```text
G0 structural, every PR
    no forbidden dependencies/mappings
    exact route/load plans
    no silent fallback
    static/dynamic parity
    cache correctness
    W^X/security

G1 competitive, pinned nightly machine
    relative p50/p95/RSS/size gates against installed references

G2 stretch, scheduled qualification
    better-than-Go/Bun/Rust/Python target claims
    multi-machine confirmation
```

Shared public CI should not fail a PR on a 2% wall-clock fluctuation. It should fail on structural regressions and large statistically significant performance regressions.

### 12.6 Provisional target scorecard

| Area | G1 admission | G2 stretch |
|---|---|---|
| root `--version` | no external open/module load; p50 <= local `go version` | <= 0.8x local `go version` and C-class first-byte |
| root help | no SCI/compiler/interpreter/loader/aspect load | lower first-byte than `go help` with output work separated |
| config-only CLI surface edit | 0 compiled modules, 0 links, unchanged core digest | atomic SCI update below measurement noise of a provider build |
| non-root option routing | bounded indexed lookup, zero provider loads while parsing | <= 1.05x the same command route without provider options |
| tiny native hello | size/RSS/startup <= equivalent Go or Rust on same host | better than both on at least two hosts |
| source interpreter hello | <= Python `-S` p50 | <= Bun source p50 |
| cached source | <= Bun source and <= 2x direct native | near compiled bytecode/native bundle path |
| fast interpreter geomean | >= 3x CPython typed suite | <= 2.5x Go/Rust native |
| Tier 1 warm | <= 1.5x best AOT/JSC comparison | <= 1.25x |
| release AOT | <= 1.1x best equivalent Go/Rust/C | parity/better |
| tiny SMF loader | <= 1.5x comparable OS module load | <= 1.1x |
| warm no-op compile | <= 10% cold | <= 5% |
| one-body edit | better than Go/Rust comparable lane | affected-query proportionality |
| optimizer-only edit | no compiler-core rebuild | dynamic reload/service update |

### 12.7 Claim language

Reports use:

```text
PASS        exact gate proven with admitted evidence
FAIL        gate executed and violated
BLOCKED     required tool/platform/capability unavailable
INCONCLUSIVE execution returned without required result/evidence
UNVERIFIED  design/source contract only; live path not run
```

Never label a source contract, stub artifact, fallback interpreter, stale binary, or exit-zero-without-results as performance evidence.

---

## 13. Modern SSpec verification architecture

### 13.1 Verification doctrine

Modern SSpec tests are executable specifications and the source of truth for generated manuals. Every major requirement has:

1. a deterministic unit/contract test;
2. an integration test that crosses the real boundary;
3. a system/performance/security test where applicable;
4. a sabotage case proving the test reaches the changed implementation;
5. a generated manual with visible steps, commands, evidence, and expected results.

A passing process exit code is not sufficient. The runner output must contain an explicit scenario/result count. When it does not, the test is `INCONCLUSIVE` and must be checked through a direct `bin/simple run` reproduction.

### 13.2 Requirement IDs

```text
STARTUP-001  Root help/version perform no external config/module load.
STARTUP-002  First command/path is classified before optional component activation.
STARTUP-003  Startup never spawns a compiler/shell child.
STARTUP-004  Startup load policy is implementation-independent.
STARTUP-005  SCI lookup is bounded, exact, and directory-scan free.

COMPOSE-001  Presence, placement, and activation are independent.
COMPOSE-002  Auto placement prefers matching static implementation.
COMPOSE-003  Auto placement selects exact dynamic artifact on static hash mismatch.
COMPOSE-004  Full rebuild folds auto component static when hashes match.
COMPOSE-005  Dynamic placement remains dynamic after full rebuild.
COMPOSE-006  No core component depends on an aspect implementation.

CLI-OPT-001  Adding/renaming an exact option, alias, help, or value map rebuilds SCI only.
CLI-OPT-002  Adding a namespaced extension key rebuilds only its provider when ABI-compatible.
CLI-OPT-003  `--x<namespace>-<key>[=<value>]` routes only to an exact configured provider.
CLI-OPT-004  Namespaced values require `=` and never consume the next argv token.
CLI-OPT-005  Unknown namespaces/options in Simple-owned scopes and missing required providers fail closed; unrecognized direct-entry application options pass through.
CLI-OPT-006  Optional missing-provider behavior follows explicit policy and is receipt-visible.
CLI-OPT-007  Core-reserved options/prefixes cannot be overridden.
CLI-OPT-008  `--` prevents all subsequent Simple option interception.
CLI-OPT-009  Root help/version do not read SCI or load providers; extended help reads only indexes.
CLI-OPT-010  Option semantic classification drives exact cache-key projection.
CLI-OPT-011  Static/dynamic provider option behavior and output are identical.
CLI-OPT-012  A full rebuild may fold provider options into the provider capsule, never stage-0.
BUILD-CLI-001 A CLI composition-only edit compiles zero modules, links zero objects, and leaves `simple-core` digest unchanged.

ASPECT-001   Disabled aspect has zero code/data/load-plan residue.
ASPECT-002   Selected facet loads only its exact admitted pack.
ASPECT-003   Static and dynamic facet semantics match.
ASPECT-004   Corrupt/ABI-mismatched pack fails closed.
ASPECT-005   Instrumentation readiness is reported truthfully.

LOADER-001   V2 maps segments, not one executable allocation per symbol.
LOADER-002   No W+X mapping exists.
LOADER-003   All imports resolve before module activation.
LOADER-004   Missing modules use exact negative cache within a generation.
LOADER-005   Base loader does not construct compiler/JIT/hot-reload services.
LOADER-006   Static and dynamic provider exports conform to one ABI.

INTERP-001   ExecIR and reference MIR interpreter produce identical results.
INTERP-002   Fast frames use dense slots, not dictionaries, on admitted opcodes.
INTERP-003   Quickening preserves semantics and deoptimizes correctly.
INTERP-004   Tier 1 compiles from ExecIR/MIR without source access.
INTERP-005   Cold programs do not activate a JIT backend.
INTERP-006   OSR/deopt preserve locals, roots, effects, and exceptions.

COMPILER-001 Body-only edits do not change public interface hash.
COMPILER-002 Green query results prevent unnecessary dependent execution.
COMPILER-003 Config-only composition changes rebuild SCI only.
COMPILER-004 Optimizer implementation-only edits rebuild one dynamic artifact.
COMPILER-005 Dynamic optimizer entry executes real transformation.
COMPILER-006 Full rebuild statically folds auto optimizer.
COMPILER-007 Direct-dependency SIF decoding is lazy and exact.

PERF-001      Benchmarks use immutable admitted binaries.
PERF-002      Equivalent semantic/product lanes are compared.
PERF-003      Reports contain p50/p95/RSS/I/O/module evidence.
PERF-004      Fallback/stub/stale/identity mismatch is not measured as success.
PERF-005      Explicit result counts are required.
```

### 13.3 Proposed test layout

```text
test/01_unit/startup/
    startup_classifier_spec.spl
    startup_plan_spec.spl
    startup_sci_index_spec.spl
    component_resolution_spec.spl
    cli_option_route_spec.spl
    cli_extension_namespace_spec.spl

test/01_unit/aspect/
    aspect_descriptor_spec.spl
    aspect_pack_index_spec.spl
    aspect_auto_placement_spec.spl

test/01_unit/interp/
    execir_decode_verify_spec.spl
    execir_quickening_spec.spl
    execir_superinstruction_spec.spl

test/02_integration/startup/
    startup_static_dynamic_resolution_spec.spl
    startup_command_capsule_spec.spl
    startup_cli_option_provider_spec.spl
    startup_cli_help_index_spec.spl

test/02_integration/loader/
    smf_v2_segment_loader_spec.spl
    smf_v2_relocation_spec.spl
    loader_static_dynamic_parity_spec.spl

test/02_integration/interp/
    execir_reference_parity_spec.spl
    execir_jit_source_independence_spec.spl
    execir_osr_deopt_spec.spl

test/02_integration/compiler/
    sif_direct_dependency_spec.spl
    query_red_green_spec.spl
    dynamic_optimizer_execution_spec.spl

test/03_system/startup/
    startup_no_optional_load_spec.spl
    startup_route_matrix_spec.spl
    startup_no_child_process_spec.spl
    startup_cli_config_no_rebuild_spec.spl
    startup_xnamespace_forwarding_spec.spl

test/03_system/aspect/
    aspect_zero_residue_spec.spl
    aspect_pack_activation_spec.spl

test/05_perf/
    startup_stage0_perf_spec.spl
    startup_cli_option_index_perf_spec.spl
    loader_segment_perf_spec.spl
    interpreter_tiering_perf_spec.spl
    compiler_incremental_perf_spec.spl
    cross_language_execution_lanes_spec.spl

test/06_security/
    loader_artifact_admission_spec.spl
    loader_wx_relro_spec.spl
    aspect_capability_confinement_spec.spl

test/00_formal/
    startup_plan_determinism_lean_spec.spl
    component_dependency_acyclic_lean_spec.spl
    disabled_aspect_absence_lean_spec.spl
    cache_semantic_equivalence_lean_spec.spl
```

### 13.4 Test helper architecture

Proposed helpers are separate from the core and must not be imported by production stage-0:

```text
test/helpers/startup/startup_probe.spl
    run_with_load_probe()
    parse_proc_maps_or_platform_equivalent()
    capture_open_map_exec_events()
    assert_no_component_family()

test/helpers/startup/cli_option_probe.spl
    compile_composition_config()
    immutable_core_digest()
    capture_option_route_receipt()
    capture_provider_option_batch()
    assert_zero_compile_and_link()

test/helpers/loader/smf_fixture_builder.spl
    build_v2_fixture()
    corrupt_digest()
    corrupt_relocation()
    create_cycle()

test/helpers/perf/process_bench.spl
    immutable_binary_identity()
    run_samples()
    percentile()
    peak_rss()
    syscall_io_receipt()
    explicit_result_gate()

test/helpers/interp/execir_oracle.spl
    run_reference()
    run_fast()
    run_tier1()
    compare_result_and_effects()
```

On Linux, an external native probe may use `strace`, `/proc/<pid>/maps`, `perf stat`, `mincore`, or a small ptrace/eBPF helper according to environment. Windows uses ETW/Process Monitor-compatible providers; SimpleOS uses loader/VFS/process receipts. Environmental absence yields `BLOCKED`, never a false pass.

### 13.5 Root startup no-load SSpec

```simple
# @req STARTUP-001 STARTUP-003 PERF-004 PERF-005
# @evidence-display: detail
"""
# Root startup contains no optional runtime

The root version and help routes execute in stage-0. They do not open SCI,
load compiler/interpreter/loader/aspect modules, or spawn child processes.
"""

use std.spec.{describe, it, expect, step}
use test.helpers.startup.startup_probe.{
    run_with_load_probe,
    receipt_has_explicit_result,
    optional_module_hits,
    child_process_count,
    opened_path_suffixes
}

describe "Stage-0 root startup":
    it "prints version without optional component activation":
        step("Run the immutable stage-0 binary under the platform load probe")
        val receipt = run_with_load_probe(["--version"])

        step("Require an explicit execution result, not exit code alone")
        expect(receipt_has_explicit_result(receipt)).to_equal(true)
        expect(receipt.exit_code).to_equal(0)

        step("Verify optional module families were not mapped")
        expect(optional_module_hits(receipt, [
            "compiler", "interp", "loader", "aspect", "office", "ide", "ui"
        ])).to_equal([])

        step("Verify startup did not spawn a compiler or shell")
        expect(child_process_count(receipt)).to_equal(0)

        step("Verify SCI and project configuration were not opened")
        expect(opened_path_suffixes(receipt, [".sci", ".sdn", "simple.toml"])).to_equal([])
```

The helper API above is proposed. Its implementation must rely on external evidence where possible so an internal receipt cannot lie about omitted loads.

### 13.6 Route matrix SSpec

```text
input                         expected selected closure
--------------------------------------------------------------------------
--version                     stage0 only
--help                        stage0 only
compile --help                stage0 + SCI help index; no command provider
compile hello.spl             compiler CLI + frontend + semantic + MIR + backend
hello.spl --interpret         exact SCI option patch + frontend/cache + interpreter.fast
hello.spl --backend=cranelift exact option route + ExecIR/MIR + Cranelift on demand
hello.smf                     loader.base
native installed app          direct exec
ui                            UI command capsule; no compiler unless source miss
```

The test compares exact component IDs, not only process output.

### 13.7 Static/dynamic auto-placement SSpec

```simple
# @req COMPOSE-002 COMPOSE-003 COMPOSE-004 COMPOSE-005
use std.spec.{describe, it, expect, step}
use app.startup.component_resolution.{resolve_component_for_test}

describe "Automatic component placement":
    it "uses matching static implementation":
        step("Create a descriptor and matching embedded implementation hash")
        val result = resolve_component_for_test(
            placement: "auto",
            configured_impl: "impl-B",
            static_impl: "impl-B",
            dynamic_ready: true
        )
        expect(result.kind).to_equal("static")

    it "uses dynamic implementation when embedded static code is stale":
        step("Keep the old static implementation and configure a new module")
        val result = resolve_component_for_test(
            placement: "auto",
            configured_impl: "impl-B",
            static_impl: "impl-A",
            dynamic_ready: true
        )
        expect(result.kind).to_equal("dynamic")
        expect(result.reason).to_equal("static_impl_hash_mismatch")

    it "keeps explicit dynamic placement external after rebuild":
        val result = resolve_component_for_test(
            placement: "dynamic",
            configured_impl: "impl-B",
            static_impl: "impl-B",
            dynamic_ready: true
        )
        expect(result.kind).to_equal("dynamic")
```

An integration test must perform an actual optimizer/provider rebuild, not only call the pure planner.

### 13.8 Aspect zero-residue SSpec

Checks:

- link map contains no disabled aspect symbols;
- executable strings contain no disabled log formats/site tables;
- SCI has no activation edge;
- process maps contain no aspect pack;
- startup/open traces contain no aspect path;
- hot dispatch assembly/ExecIR contains no trace branch or event opcode;
- binary size delta from enabling the aspect is positive and attributable.

Sabotage:

1. place a valid pack at the normal path with a marker side effect;
2. run with aspect disabled;
3. test passes only if marker is absent and the file was never opened;
4. enable the aspect and require the exact marker/evidence;
5. corrupt the digest and require fail-closed activation.

### 13.9 Loader segment SSpec

```simple
# @req LOADER-001 LOADER-002 LOADER-003
# @evidence-display: detail
use std.spec.{describe, it, expect, step}

describe "SMF V2 segment loading":
    it "maps complete segments and resolves imports before entry":
        step("Build a fixture with multiple exported symbols in one RX segment")
        val fixture = build_v2_fixture(symbol_count: 128, code_segments: 1)

        step("Load under mapping/protection probe")
        val receipt = load_with_probe(fixture.path)

        step("Reject per-symbol executable mappings")
        expect(receipt.rx_mapping_count).to_equal(1)
        expect(receipt.export_count).to_equal(128)

        step("Require all imports resolved before entry transfer")
        expect(receipt.unresolved_import_count).to_equal(0)
        expect(receipt.entry_called).to_equal(true)

        step("Require W^X")
        expect(receipt.rwx_mapping_count).to_equal(0)
```

Corruption fixtures cover truncated headers, invalid segment ranges, overlapping mappings, relocation overflow, unsupported relocation, dependency cycle, digest mismatch, interface mismatch, capability escalation, and executable stack requests.

### 13.10 Interpreter differential SSpec

For every supported opcode and semantic family:

```text
source fixture
    -> MIR
    -> reference interpreter
    -> ExecIR interpreter variants
    -> Tier 1
    -> Tier 2 where available

compare:
    return value
    stdout/stderr contract
    file/network effects through mockable ports
    exception/panic category and source anchor
    ownership/move failure
    task/actor result
    final heap/object observable state
```

Use generated/random bounded programs in addition to hand-written cases. A mismatch stores the source, MIR, ExecIR, seed, target, and all receipts as a reproduction bundle.

### 13.11 Quickening and deoptimization SSpec

Required cases:

- monomorphic interface call specializes;
- generation/type change invalidates guard;
- specialized opcode deoptimizes to base instruction;
- result remains equal;
- repeated instability stops thrashing and remains generic;
- inline cache size stays within schema limit;
- disabled quickening runs same immutable on-disk ExecIR;
- specialization counters are absent in stripped production variant.

### 13.12 JIT source-independence sabotage

```text
1. parse/type/lower source to admitted ExecIR;
2. rename or make source unavailable;
3. execute until Tier 1 threshold;
4. require Tier 1 compile success from ExecIR;
5. require same checksum;
6. inspect file-open trace: source was not reopened;
```

This catches the current anti-pattern of compiling retained source text during tier promotion.

### 13.13 Exact incremental compiler SSpec

Scenarios:

```text
no-op rebuild
    parsed=0 or bounded index checks only
    typed=0
    MIR=0
    linked=0 unless final wrapper policy requires

private body change
    changed body parsed/typed/MIR/codegen
    public SIF hash unchanged
    importers green

public signature change
    SIF hash changes
    exact dependent bodies red

optimizer implementation-only dynamic edit
    compiler core artifact digest unchanged
    one optimizer artifact rebuilt
    SCI updated

optimizer interface change
    dependent pipeline/contracts invalidated

config-only placement change
    compiled_modules=0
    linked_objects=0
    SCI generation changes
```

### 13.14 Performance SSpec design

Do not put unstable p50 thresholds in a one-run `it`. The SSpec verifies the harness contract, runs or references a multi-sample profile, and checks a signed/hashed report:

```simple
# @req PERF-001 PERF-002 PERF-003 PERF-004 PERF-005
# @evidence-display: links
"""
# Stage-0 competitive startup profile

This scenario verifies immutable binary identity, equivalent work, sample count,
module/I/O evidence, percentile fields, and fail-closed classifications.
"""

use std.spec.{describe, it, expect, step}

describe "Stage-0 startup performance report":
    it "admits only a statistically valid report":
        step("Read the report and its immutable artifact manifest")
        val report = read_startup_profile_report()

        step("Require current self-hosted binary identity")
        expect(report.identity_admitted).to_equal(true)
        expect(report.binary_digest).not_to_equal("")

        step("Require enough samples and percentile fields")
        expect(report.measured_runs >= 50).to_equal(true)
        expect(report.has_p50 and report.has_p95 and report.has_rss).to_equal(true)

        step("Require explicit no-fallback and result evidence")
        expect(report.fallback_count).to_equal(0)
        expect(report.explicit_result_count).to_equal(report.measured_runs)

        step("Require zero optional mappings for root version")
        expect(report.optional_module_mapping_count).to_equal(0)
```

### 13.15 Cross-language profile contract

Each row records:

```text
language/runtime version
source and generated artifact digest
mode: source | bytecode | JIT | AOT | native
product semantics
compile/transpile work included or excluded
cache state
sample count
checksum/output contract
fallback status
startup and steady-state metrics
loaded runtime/module evidence
```

The profile refuses to compare mismatched product modes in one winner gate.

### 13.16 GUI/TUI evidence where relevant

This plan is primarily startup/compiler/runtime work, but UI command capsules require visible Modern SSpec manuals:

- render the TUI screen before and after selecting a startup profile;
- visually mark focus/click/typing actions;
- show which component pack becomes active;
- display a startup receipt panel in the diagnostic test application;
- keep GUI-only pixel captures only for behavior that cannot be represented in TUI;
- compare static and dynamic UI provider output.

Use typed captures such as `exec`, `log`, `artifact`, `text`, and `html`, with `# @inline`, `# @include`, `# @prev`, and `# @evidence-display` according to the existing scenario-manual guide.

### 13.17 Generated manual workflow

```text
1. write/update executable `*_spec.spl`
2. run the exact spec directly
3. require explicit result/scenario count
4. run `simple sspec-maintain scan <spec>`
5. inspect generated `doc/06_spec/...` manual
6. verify steps/actions/captures are visible and truthful
7. link report/reproduction artifacts
8. never hand-edit the generated manual as the source of truth
```

### 13.18 Formal/generated proof lane

Generate Lean definitions/theorems from the same schemas, initially for finite planner properties:

```text
StartupPlan deterministic for fixed inputs
Disabled capability absent from closure
Core-to-aspect dependency impossible
Component dependencies acyclic
Auto placement never chooses stale static implementation
Dynamic admission requires matching ABI/interface/digest
W and X are mutually exclusive for final segment permissions
Green cache reuse returns equivalent semantic result
Static/dynamic descriptor resolution has equal public behavior
```

Formal proof does not replace live mapping, execution, corruption, or performance tests.

### 13.19 Config-driven CLI option SSpec

```simple
# @req CLI-OPT-001 CLI-OPT-003 CLI-OPT-008 BUILD-CLI-001
# @evidence-display: links
"""
# Config-driven CLI options

This scenario proves that an option surface can change without relinking the
launcher and that a namespaced option reaches only its configured provider.
"""

use std.spec.*
use test.helpers.startup.cli_option_probe.{
    compile_composition_config, immutable_core_digest,
    capture_option_route_receipt, assert_zero_compile_and_link
}

describe "Config-driven CLI options":
    it "adds an exact option without rebuilding simple-core":
        step("Record the immutable stage-0/core artifact digest")
        val before = immutable_core_digest()

        # @capture(exec)
        step("Regenerate SCI after adding --new-mode to configuration")
        val build = compile_composition_config("test/fixtures/startup/cli_option_added.sdn")

        step("Require a composition-only build")
        expect(assert_zero_compile_and_link(build)).to_equal(true)
        expect(build.explicit_result_count).to_be_greater_than(0)

        step("Verify the launcher artifact did not change")
        val after = immutable_core_digest()
        expect(after).to_equal(before)

        # @capture(exec)
        step("Run the new option and inspect its exact route receipt")
        val routed = capture_option_route_receipt(["--new-mode=fast", "compile", "hello.spl"])
        expect(routed.option_id).to_equal("new-mode")
        expect(routed.provider_id).to_equal("compiler.cli")

    it "routes a namespaced extension to one admitted provider":
        # @capture(exec)
        step("Run --xllvm-pass=gvn with the LLVM namespace configured")
        val routed = capture_option_route_receipt(["compile", "hello.spl", "--xllvm-pass=gvn"])

        step("Verify structured forwarding and exclusive provider selection")
        expect(routed.namespace).to_equal("llvm")
        expect(routed.provider_id).to_equal("backend.llvm")
        expect(routed.key).to_equal("pass")
        expect(routed.value).to_equal("gvn")
        expect(routed.other_provider_loads).to_equal([])

    it "stops Simple routing at the hard terminator":
        step("Pass an extension-looking token after --")
        val routed = capture_option_route_receipt(["run", "app.spl", "--", "--xllvm-pass=gvn"])
        expect(routed.extension_count).to_equal(0)
        expect(routed.program_args).to_contain("--xllvm-pass=gvn")
```

The generated manual must show the config edit, SCI-only build evidence, unchanged core digest, routed provider identity, and forwarded structured option. Executable hashing/probe details remain folded.

### 13.20 CLI option sabotage and security matrix

Required scenarios:

```text
unknown exact option
    -> explicit error, no provider load

unknown --x namespace
    -> explicit error, no filesystem/plugin scan

optional provider absent + warn_skip
    -> warning + receipt + no behavior change

required provider absent
    -> fail before command execution

valid artifact with wrong digest/ABI/capability
    -> admission failure; option not applied

config attempts to override --help or --x prefix
    -> SCI generation failure

duplicate global alias / normalized namespace
    -> SCI generation failure

--xllvm-pass gvn
    -> parsed as flag plus positional token, never implicit value consumption

--xllvm-pass=gvn after --
    -> forwarded unchanged to application

root --help
    -> zero SCI opens and zero provider loads

simple help --all
    -> option index read; zero provider loads

simple help compile --full
    -> only compiler CLI provider may load

routing_only help rename
    -> compiler artifact action keys unchanged

compile_semantic resolved-value change
    -> exact affected compiler action keys change
```

Sabotage must place a valid provider with a marker side effect at the normal path, then run an unrelated option/command. The marker must remain absent and external load evidence must show that the provider file was never opened.

---

## 14. Parallel-agent implementation plan

### 14.1 Parallel-development rules

1. **Freeze contracts first.** No implementation lane invents its own component ID, startup plan, load receipt, SMF segment type, ExecIR opcode layout, query key, aspect facet, or evidence classification.
2. **One file owner per wave.** Shared files have one serial integration owner. Agents add adapters/new modules rather than concurrently rewriting root `__init__.spl`, CLI main, loader main, or central MIR files.
3. **Record immutable baselines.** Every work package records starting SHA, integration SHA, compiler binary digest, and SCI/schema versions.
4. **Acceptance reaches changed code.** Every lane includes a sabotage probe. Source-shape checks alone are `UNVERIFIED` until a live path executes.
5. **No placeholder success.** Hollow SMF artifacts, stubs, fallback paths, stale binaries, and exit-zero-without-result are rejected.
6. **Cross-mode parity is mandatory.** Reference interpreter, fast interpreter, Tier 1, Tier 2 where available, static component, dynamic component, host, and SimpleOS either pass or explicitly report unsupported/blocked.
7. **Frozen contracts change through versioning.** A post-freeze change requires a schema version bump, migration note, and ratification by contract/integration owners.
8. **The build lane owns memory.** Bootstrap/compiler builds have priority. Test lanes throttle to one process under low free memory; optional Tier 2/perf work is canceled first.
9. **Integrate by per-file three-way merge.** Never overwrite a hot file with a stale whole-file copy. Preserve unrelated current-main work.
10. **One certifier.** Implementation agents do not self-declare release completion. The certification lane validates exact merged artifacts.

### 14.2 Repository ownership levels

```text
L0 frozen schemas/contracts
    exclusive contract agents; append/version only after freeze

L1 core implementations
    one owner per module family

L2 adapters/integration
    one owner per shared root/dispatcher per wave

L3 tests/reports/manuals
    parallel by feature, but fixture/helper ownership remains exclusive

L4 certification
    read-only except generated reports and release receipts
```

### 14.3 Wave 0 — census and contract freeze

#### WP-00 — Baseline and collision census

- **Agent:** `baseline-census`
- **Owned paths:** new report/tracking files only; no code
- **Tasks:** inventory all existing startup plan, launch metadata, SCI/provider, SMF loader, dynSMF, optimizer plugin, AOP, interpreter tier, cache key, receipt, and performance helper names; map duplicates and authoritative owners.
- **Deliverables:** machine-readable census, dependency graph, binary/import/map baseline, benchmark environment manifest.
- **Acceptance:** every proposed public type/name checked for collision; current main SHA and exact binaries recorded; root help/version/source/SMF/native traces captured.
- **Sabotage:** point harness at stale/Rust-seed/non-self-host binary; admission must fail.

#### WP-01 — Component composition contract V1

- **Agent:** `composition-contract`
- **Owned paths:** proposed `src/lib/common/structural/component/**`, schema docs/specs
- **Tasks:** freeze capability, presence, placement, activation, descriptor, static implementation entry, and resolution reason enums.
- **Dependencies:** WP-00
- **Acceptance:** golden binary vectors; deterministic resolution; stale-static and dynamic-always cases; Lean schema generation.
- **Do not touch:** startup implementation, loader, compiler main.

#### WP-02 — Startup plan/index contract V1

- **Agent:** `startup-contract`
- **Owned paths:** proposed `src/app/startup/contract/**`, format docs/specs
- **Tasks:** freeze `StartupRequestV1`, `StartupPlanV1`, compact SCI header/route/component entries, plan hash, evidence level.
- **Dependencies:** WP-01
- **Acceptance:** malformed/truncated/overflow/collision golden vectors; no allocation-required fields; cross-endian policy explicit.

#### WP-03 — SMF V2 loader contract

- **Agent:** `smf-v2-contract`
- **Owned paths:** proposed `src/os/smf/format_v2/**`, specs/docs
- **Tasks:** freeze header, segments, imports, exports, relocations, capabilities, launch metadata, signatures, `LoadPlanV1`, and `LoadReceiptV1`.
- **Dependencies:** WP-01
- **Acceptance:** golden files for x86_64/AArch64/RISC-V; W^X invariants; invalid range/cycle vectors; V1 compatibility decision.

#### WP-04 — Aspect facet/pack contract V1

- **Agent:** `aspect-contract`
- **Owned paths:** proposed `src/lib/common/structural/aspect_pack/**`, specs/docs
- **Tasks:** freeze facet IDs, pack index, readiness levels, typed payload/event contracts, activation receipt, capability/security fields.
- **Dependencies:** WP-01
- **Acceptance:** logical-facet/physical-pack independence; disabled-facet absence theorem; pack golden vectors.

#### WP-05 — ExecIR V1 contract and opcode DSL

- **Agent:** `execir-contract`
- **Owned paths:** proposed `src/compiler/50.mir/execir/schema/**` or agreed canonical layer, generator input/specs
- **Tasks:** freeze file/header/function/block/frame metadata, base opcode families, operand encoding, exception/OSR/deopt tables, schema evolution policy.
- **Dependencies:** WP-00
- **Acceptance:** encoder/decoder golden vectors; verifier rejects malformed CFG/register/type data; opcode number stability.

#### WP-06 — Query/SIF/cache identity contract

- **Agent:** `incremental-contract`
- **Owned paths:** proposed `src/compiler/00.common/query_contract/**`, `src/compiler/20.hir/sif_contract/**`, schema specs
- **Tasks:** freeze query identity, ordered read edge, result hash, SIF header/index/entity IDs, cache producer/schema identity.
- **Dependencies:** WP-00, existing CAS owner review
- **Acceptance:** body-only/interface-change vectors; deterministic hashes; no second cache root.

#### WP-07 — Performance/evidence contract V1

- **Agent:** `perf-contract`
- **Owned paths:** `test/05_perf/profile_contracts/**`, new report schema/docs
- **Tasks:** freeze immutable artifact identity, sample metadata, lane/product kind, percentiles, RSS/I/O/maps/relocations, fallback/result classifications.
- **Dependencies:** WP-00
- **Acceptance:** current one-run report classified historical/non-admissible; missing result line yields `INCONCLUSIVE`; mismatched product comparison rejected.

#### WP-08 — CLI option route and extension contract V1

- **Agent:** `cli-option-contract`
- **Owned paths:** new schema/contract docs and golden vectors; no production codec edits in Wave 0
- **Tasks:** freeze exact option route, scope, arity, plan patch, extension namespace grammar, missing policy, semantic class, help/completion metadata, and `SimpleCliExtensionV1` wire records.
- **Dependencies:** WP-01, WP-02, review of current SCI/provider command wire
- **Acceptance:** golden vectors; reserved-name/collision rejection; `=`-only extension values; `--` boundary; unknown/missing fail-closed cases; static/dynamic conformance model.
- **Gate:** every later CLI option agent imports these records; no agent invents another prefix or option wire.

#### Wave 0 integration gate

One contract integrator verifies:

- no duplicate schema ownership;
- all generated IDs stable;
- dependency graph acyclic;
- formal generators build;
- every implementation wave can work without editing another contract.

No performance implementation begins before this gate.

### 14.4 Wave 1 — stage-0 and SCI

#### WP-10 — Native process entry and minimal runtime closure

- **Agent:** `stage0-entry`
- **Owned paths:** new `src/app/startup/stage0/entry_*`, linker/build definitions for stage-0 only
- **Tasks:** implement POSIX/Linux process entry adapter, minimal fatal write, borrowed argv spans, no-GC/no-scheduler closure.
- **Dependencies:** WP-02
- **Acceptance:** root binary/link map has no forbidden symbols; root version with zero heap allocations and zero external opens; exact exit/result marker in test build.
- **Sabotage:** link a forbidden compiler symbol; link-map gate fails.

#### WP-11 — Allocation-free route classifier

- **Agent:** `stage0-classifier`
- **Owned paths:** new `src/app/startup/stage0/classifier.spl`, unit specs
- **Tasks:** first-token/extension/core-root classification; fixed hash/byte comparisons; generic `--x` lexical split; scope-window and hard-`--` recognition. Exact option semantics remain outside this file.
- **Dependencies:** WP-02, WP-10 interfaces
- **Acceptance:** exhaustive token/extension corpus; malformed root forms; namespace/key/value shape; no project/command/provider-specific option names.

#### WP-12 — SCI generator

- **Agent:** `sci-generator`
- **Owned paths:** compiler/build-side SCI generator, not stage-0 reader
- **Tasks:** compile human config/provider manifests to compact SCI; generate command, exact-option, namespace, help, and component indexes; exact component paths/hashes/dependencies. The agent consumes WP-08 records but does not own shared composition codec files.
- **Dependencies:** WP-01, WP-02
- **Acceptance:** deterministic byte-for-byte output; config-only command/option/namespace update compiles zero modules and links zero objects; command/option/alias/namespace collision and dependency-cycle rejection.

#### WP-13 — Bounded SCI reader

- **Agent:** `sci-reader`
- **Owned paths:** new stage-0 SCI reader and format tests
- **Tasks:** fixed header/trailer read, digest/schema validation, bounded route/component lookup, no directory scan.
- **Dependencies:** WP-12 golden vectors
- **Acceptance:** bytes-read bound; truncated/oversized offsets rejected; only exact selected records read where supported.
- **Sabotage:** valid route exists only after unselected corrupt record; reader must not incorrectly scan/fail if format permits independent indexed access.

#### WP-14 — Static component table generator

- **Agent:** `static-component-table`
- **Owned paths:** build generator and generated table module
- **Tasks:** emit static descriptor/export tables with interface and implementation hashes.
- **Dependencies:** WP-01
- **Acceptance:** static lookup parity with dynamic descriptor; stale static hash test.

#### WP-15 — Startup planner/resolver

- **Agent:** `startup-planner`
- **Owned paths:** new planner module; no host I/O implementation
- **Tasks:** combine classifier, SCI, static table, profile, and exact policies into deterministic `StartupPlanV1`.
- **Dependencies:** WP-11–WP-14
- **Acceptance:** route matrix, auto/static/dynamic tests, no silent fallback, plan determinism theorem.

#### WP-16 — Root help/version and command help capsules

- **Agent:** `cli0-capsules`
- **Owned paths:** new root help/version data and command-help provider format; no compiler engine
- **Tasks:** embedded root output; separately generated subcommand help capsules.
- **Dependencies:** WP-10, WP-15
- **Acceptance:** root help/version opens no SCI; `compile --help` reads only the SCI help index; `compile --help --full` may activate only the compiler CLI provider; output parity with accepted CLI contract.

#### WP-17 — Startup host ports

- **Agent:** `startup-host-ports`
- **Owned paths:** POSIX/Windows/SimpleOS startup host adapters, separate subpaths
- **Tasks:** exact read, selected mapping, direct exec, protections, minimal fatal write.
- **Dependencies:** WP-02
- **Acceptance:** platform contract tests; implementation-independent plan; unsupported operation explicit.

#### WP-18 — Startup external evidence probe

- **Agent:** `startup-probe`
- **Owned paths:** test helpers/scripts only
- **Tasks:** open/map/exec/child/RSS/page-fault evidence; explicit result gate.
- **Dependencies:** WP-07
- **Acceptance:** catches hidden SCI open, compiler mapping, shell child, stale binary; absence of platform probe = `BLOCKED`.

#### WP-19 — SCI option-route section integration

- **Agent:** `sci-option-route`
- **Exclusive Wave-1 owned hot paths:** `src/lib/nogc_sync_mut/composition/types.spl`, `source.spl`, `codec.spl`, and new option-route index modules
- **Tasks:** add the versioned option/namespace records and SCI section; parse/validate exact options and namespaces; generate compact startup indexes; preserve existing command/provider records and unknown-section policy.
- **Dependencies:** WP-08, WP-12
- **Acceptance:** old command-only images remain readable; v1.1 option images round-trip canonically; config-only change reports 0 compile/0 link; old reader fails closed when the required feature bit is present.
- **Coordination:** no other Wave-1 agent edits these three shared files.

#### WP-19a — Stage-0 exact option and namespace router

- **Agent:** `stage0-option-router`
- **Owned paths:** new `src/app/startup/stage0/option_router.spl`, option-batch arena, focused specs
- **Tasks:** bounded exact-option lookup, generic plan-patch application, `--x` namespace routing, scope windows, `after_entry`, hard `--`, and provider batch grouping.
- **Dependencies:** WP-11, WP-13, WP-19
- **Acceptance:** no heap/provider load during parsing; unknown/missing cases fail by policy; route/app-argument collision corpus; root routes stay SCI-free.
- **Sabotage:** provider marker artifact remains unopened for an unrelated option.

#### WP-19b — `SimpleCliExtensionV1` provider wire

- **Agent:** `cli-extension-wire`
- **Owned paths:** new `src/lib/nogc_sync_mut/composition/cli_extension_wire.spl`, provider-side adapter, SFFI/process-call bridge additions assigned exclusively
- **Tasks:** pointer-free request/result schema; describe/validate/apply/complete operations; bounded structured key/value batches; static/dynamic adapters over admitted owned sessions.
- **Dependencies:** WP-08, current provider query/session contract
- **Acceptance:** fuzz/golden decode; length/overflow rejection; static/dynamic parity; no shell forwarding; pin/lifetime correctness.

#### WP-19c — Config-driven help, completion, and migration generator

- **Agent:** `cli-option-help`
- **Owned paths:** new help/completion generator, config migration tool, fixtures/manual specs; no stage-0 or composition codec edits
- **Tasks:** generate root generic extension line, SCI exact-option summaries, command help indexes, shell completion metadata, and current-hardcoded-option migration reports.
- **Dependencies:** WP-16, WP-19
- **Acceptance:** root help performs no I/O; `simple help --all` loads no provider; full command help loads only its provider; help/alias edits are SCI-only.

#### Wave 1 integration owner

- **Owned hot paths:** current CLI entry/build routing only during cutover
- **Tasks:** make `bin/simple` stage-0, route old unified CLI as a command capsule, connect option routing/provider batches, preserve compatibility, avoid whole-file replacement.
- **Gate:** existing CLI commands/options work through capsules/config; new exact and namespaced options work without a core relink; root route passes structural no-load gate.

### 14.5 Wave 2 — segment loader

#### WP-20 — SMF V2 reader/verifier

- **Agent:** `smf-v2-reader`
- **Owned paths:** V2 reader/verifier modules
- **Tasks:** bounded header/directory/index parsing; target/ABI/digest/capability checks.
- **Dependencies:** WP-03
- **Acceptance:** all corruption vectors; no full-file read for metadata-only plan.

#### WP-21 — Segment planner/mapper

- **Agent:** `segment-mapper`
- **Owned paths:** `loader.v2` mapping core and platform mapping port
- **Tasks:** reserve/map RX/R/RW/BSS; W^X; rollback on failure.
- **Dependencies:** WP-20, startup host protections
- **Acceptance:** O(segments) mappings; zero RWX; transaction cleanup.

#### WP-22 — Relocation engine

- **Agent:** `smf-relocator`
- **Owned paths:** V2 relocation decoder/applier
- **Tasks:** compact stream, relative/common relocations, bounds/overflow validation, icache ranges.
- **Dependencies:** WP-21
- **Acceptance:** architecture golden vectors; malformed relocation sabotage; one flush per changed range where supported.

#### WP-23 — Import/export index

- **Agent:** `smf-symbol-index`
- **Owned paths:** V2 export/import tables and build generator
- **Tasks:** ordinals/MPH/sorted fallback, collision verification, eager selected-module binding.
- **Dependencies:** WP-20
- **Acceptance:** bounded lookup; exact full-name collision check; unresolved import blocks activation.

#### WP-24 — Loader base split

- **Agent:** `loader-base-split`
- **Owned paths:** new `src/compiler/99.loader/base/**`; adapters around old loader
- **Tasks:** base loader has no compiler/JIT/cache/hot-reload construction; old loader becomes optional/reference provider.
- **Dependencies:** WP-20–WP-23
- **Acceptance:** import/link graph gate; tiny SMF executes; existing V1 path remains explicit compatibility.

#### WP-25 — Optional loader capabilities

- **Agent:** `loader-capabilities`
- **Owned paths:** new capability modules for cache, JIT bridge, generic instantiation, lifecycle, remote
- **Tasks:** move existing machinery behind component descriptors; lazy first-use activation.
- **Dependencies:** WP-24
- **Acceptance:** ordinary V2 load creates none; targeted tests activate exactly one capability.

#### WP-26 — Static/dynamic provider adapter

- **Agent:** `provider-unification`
- **Owned paths:** provider resolution/adapters, not component schemas
- **Tasks:** one export-table port for embedded static and admitted dynamic modules.
- **Dependencies:** WP-01, WP-14, WP-23
- **Acceptance:** conformance parity; implementation-hash auto placement; pinning.

#### WP-27 — Loader security and generation update

- **Agent:** `loader-security`
- **Owned paths:** admission/security/generation modules and `test/06_security` fixtures
- **Tasks:** signature/capability policy, cycle detection, immutable update/rename, no unload by default, hot-reload generation swap optional.
- **Dependencies:** WP-20–WP-26
- **Acceptance:** malicious/corrupt corpus; capability escalation rejected; no old/new mixed generation.

#### WP-28 — V1-to-V2 artifact emitter

- **Agent:** `smf-v2-emitter`
- **Owned paths:** backend/linker emitter for V2; no loader internals
- **Tasks:** page-aligned segments, compact relocations/indexes, launch metadata trailer, real export witnesses.
- **Dependencies:** WP-03, WP-23
- **Acceptance:** artifacts exceed known hollow-stub failure shape, invoke real behavior, pass V2 loader and static/dynamic parity.

### 14.6 Wave 3 — aspects and stripping

#### WP-30 — Aspect pack builder/index

- **Agent:** `aspect-pack-builder`
- **Owned paths:** pack generator and reader
- **Tasks:** logical facets, physical packs, fixed trailer/directory, selected chunk loading.
- **Dependencies:** WP-04, loader V2 index principles
- **Acceptance:** regroup facets without changing IDs; whole-pack scan not required.

#### WP-31 — Aspect composition resolver

- **Agent:** `aspect-resolver`
- **Owned paths:** aspect component adapter and activation planner
- **Tasks:** presence/placement/activation integration; static hash matching; exact dynamic admission.
- **Dependencies:** WP-01, WP-04, WP-26
- **Acceptance:** auto fold, dynamic always, off/absence, readiness truth.

#### WP-32 — Logging packs

- **Agent:** `logging-aspects`
- **Owned paths:** new log basic/standard/debug/trace packs and typed event adapters
- **Tasks:** replace default full logger dependencies at core boundaries; retain full-language logging outside core.
- **Dependencies:** WP-30, WP-31
- **Acceptance:** zero-residue disabled build; exact facet output; site-ID mode; no `Any` at core ABI.

#### WP-33 — Loader/startup diagnostic aspects

- **Agent:** `startup-loader-aspects`
- **Owned paths:** startup/loader trace/profile/audit facets
- **Tasks:** compact receipts and external evidence join; boundary readiness.
- **Dependencies:** WP-18, WP-30
- **Acceptance:** production no-aspect binary unchanged except allowed descriptor boundary; diagnostic variant truthful.

#### WP-34 — Compiler/interpreter aspects

- **Agent:** `compiler-interp-aspects`
- **Owned paths:** compiler phase/dump/remark and interpreter trace/profile facets
- **Tasks:** typed events, instrumented variants, no default hot-path import.
- **Dependencies:** ExecIR/compiler contracts
- **Acceptance:** normal dispatch has no branch; debug variant emits correct events; reference parity.

#### WP-35 — Instrumentation variant generator

- **Agent:** `instrumentation-generator`
- **Owned paths:** build generator for none/boundary/full variants
- **Tasks:** produce callsite-free and instrumented objects from same sources/contracts.
- **Dependencies:** WP-04, WP-32–WP-34
- **Acceptance:** link map/string/assembly absence tests; variant semantic parity.

#### WP-36 — Core dependency audit

- **Agent:** `aspect-dependency-audit`
- **Owned paths:** architecture checker rules/tests/reports
- **Tasks:** fail core->aspect implementation imports, runtime AOP imports in default interpreter/loader/startup, hidden log strings.
- **Acceptance:** intentional sabotage import fails build/architecture check.

### 14.7 Wave 4 — ExecIR and interpreter

#### WP-40 — MIR to ExecIR lowerer

- **Agent:** `execir-lowering`
- **Owned paths:** new lowerer; no dispatcher
- **Tasks:** typed registers, CFG, constants, direct calls, source maps, mandatory canonicalization.
- **Dependencies:** WP-05
- **Acceptance:** full supported MIR subset, explicit unsupported diagnostics, reference parity fixtures.

#### WP-41 — ExecIR encoder/decoder/verifier

- **Agent:** `execir-codec`
- **Owned paths:** generated codec/verifier
- **Tasks:** compact binary format, bounds/type/CFG validation, version migration hooks.
- **Dependencies:** WP-05
- **Acceptance:** fuzz/corruption corpus; deterministic encoding; no unchecked offsets.

#### WP-42 — Dense frame/value runtime

- **Agent:** `execir-frame-runtime`
- **Owned paths:** fast interpreter frame/slot/arena modules
- **Tasks:** dense slots, typed lanes/layout policy, frame arena, constants, references.
- **Dependencies:** WP-05
- **Acceptance:** no dictionary import in admitted hot module; allocation/high-water tests; GC/no-GC variants.

#### WP-43 — Generated base dispatcher

- **Agent:** `execir-dispatch`
- **Owned paths:** opcode generator outputs and dispatch implementations
- **Tasks:** switch, computed-goto, tail-call where qualified; embedded compact variant.
- **Dependencies:** WP-41, WP-42
- **Acceptance:** opcode semantic suite; generated outputs reproducible; dispatch variant parity.

#### WP-44 — Quickening and inline caches

- **Agent:** `execir-specialization`
- **Owned paths:** adaptive opcode families/cache records
- **Tasks:** counters, specialization, guards, deopt, instability policy.
- **Dependencies:** WP-43
- **Acceptance:** monomorphic/polymorphic/unstable cases; bounded caches; no specialization in stripped variant.

#### WP-45 — Superinstructions

- **Agent:** `execir-superinstructions`
- **Owned paths:** fusion planner/generated fused handlers
- **Tasks:** evidence-driven fusions and reversible mapping.
- **Dependencies:** WP-43
- **Acceptance:** formal/base sequence equivalence for admitted fusions; measurable dispatch reduction.

#### WP-46 — Calls, objects, exceptions, async/effects

- **Agent:** `execir-semantics`
- **Owned paths:** fast interpreter semantic families not owned elsewhere
- **Tasks:** direct/interface calls, variants, object/text/array operations, exception state, actor/task ports.
- **Dependencies:** WP-42–WP-44
- **Acceptance:** differential suite including failure/effects, not return values only.

#### WP-47 — Tier 1 Cranelift service

- **Agent:** `tier1-cranelift`
- **Owned paths:** ExecIR/MIR-to-Cranelift service and component descriptor
- **Tasks:** lazy engine activation, typed IR input, fixed ABI, native code receipt.
- **Dependencies:** WP-40, WP-26
- **Acceptance:** source-independence sabotage, cold no-JIT mapping, warm result parity.

#### WP-48 — OSR/deoptimization

- **Agent:** `tiering-osr`
- **Owned paths:** profile policy, OSR/deopt maps, patch tables
- **Tasks:** Tier0->Tier1 transition, generation invalidation, state reconstruction.
- **Dependencies:** WP-44, WP-47
- **Acceptance:** loop/call OSR, exception/root preservation, invalidation deopt.

#### WP-49 — Tier 2 LLVM and concurrent queues

- **Agent:** `tier2-llvm`
- **Owned paths:** Tier 2 service/policy/queue, not Tier 1 implementation
- **Tasks:** lazy LLVM activation, concurrent compile, priority/memory policy, real Tier 2 code path.
- **Dependencies:** WP-48
- **Acceptance:** actual LLVM code receipt/disassembly identity, cancellation under pressure, no enum-only promotion.

#### WP-4A — Persistent native code cache

- **Agent:** `jit-code-cache`
- **Owned paths:** code-cache records and loader adapter
- **Tasks:** exact keys, admitted native function images, invalidation.
- **Dependencies:** WP-06, WP-27, WP-47
- **Acceptance:** hit without source/backend activation; corrupt/stale entry falls back to ExecIR correctly.

### 14.8 Wave 5 — compiler and incremental build

#### WP-50 — Query engine integration

- **Agent:** `compiler-query-engine`
- **Owned paths:** central query DAG engine after contract freeze
- **Tasks:** ordered reads, red/green, result fingerprint comparison, selective serialization.
- **Dependencies:** WP-06
- **Acceptance:** exact incremental SSpec; deterministic parallel reads; cycle detection.

#### WP-51 — Existing CAS evolution

- **Agent:** `compiler-cas`
- **Owned paths:** existing cache implementation only
- **Tasks:** schema-kind tiers, transaction integrity, quotas, corruption handling, query/result objects.
- **Dependencies:** WP-50
- **Acceptance:** no second cache; crash/partial-write recovery; cache failure correctness.

#### WP-52 — SIF producer/consumer

- **Agent:** `sif-metadata`
- **Owned paths:** SIF encoder/decoder/index and direct-dependency integration
- **Tasks:** exported types/effects/ownership/aspects/inline/generic summaries; lazy entity decode.
- **Dependencies:** WP-06, WP-50
- **Acceptance:** direct-dependency-only compile fixture; body-only green interface; index read bounds.

#### WP-53 — Compiler service split

- **Agent:** `compiler-service-split`
- **Owned paths:** new compiler engine/service modules; serial adapter owner for old CLI imports
- **Tasks:** isolate frontend/semantic/MIR/ExecIR/backends from CLI/tools/UI.
- **Dependencies:** Wave 1 capsule architecture
- **Acceptance:** compile help no engine, root CLI no compiler import, compiler command parity.

#### WP-54 — Dev-fast pipeline

- **Agent:** `compiler-fast-pipeline`
- **Owned paths:** pass planner/dev profile and Cranelift build path
- **Tasks:** cheap passes, analysis reuse, parallel codegen units, timing receipts.
- **Dependencies:** WP-50–WP-53
- **Acceptance:** correctness parity, compile target report, no duplicate legacy optimizer execution.

#### WP-55 — Dynamic optimizer completion

- **Agent:** `optimizer-dynload`
- **Owned paths:** existing optimizer manifest/plugin registry and dynamic invocation adapter
- **Tasks:** real entry execution, source/MIR scopes, preserved analyses, static/dynamic auto fold.
- **Dependencies:** WP-01, WP-06, WP-26
- **Acceptance:** modify optimizer without compiler rebuild; transformed output proves invocation; full rebuild static; dynamic-always external.

#### WP-56 — Backend abstraction and packs

- **Agent:** `backend-components`
- **Owned paths:** backend port/component descriptors and backend-specific optimizer policy
- **Tasks:** Cranelift/LLVM/C/WASM/etc selection; no duplicated common logic; typed backend policies.
- **Dependencies:** WP-01, WP-54
- **Acceptance:** same MIR/ExecIR input, backend conformance, strict selection/no fallback.

#### WP-57 — Parallel compiler scheduler

- **Agent:** `compiler-parallel`
- **Owned paths:** compiler scheduler/worker-local arenas only
- **Tasks:** parallel queries/codegen, memory-pressure throttling, critical-path receipt.
- **Dependencies:** WP-50, WP-54
- **Acceptance:** deterministic outputs, no deadlocks, memory cap, speedup curve, no degradation beyond admitted worker count.

#### WP-58 — Workspace compiler service

- **Agent:** `compiler-daemon`
- **Owned paths:** optional service/protocol/client
- **Tasks:** persistent indexes/query hot set, exact handshake, in-process fallback.
- **Dependencies:** WP-50–WP-53
- **Acceptance:** absent/incompatible daemon correctness; warm improvement; stage-0 no daemon contact for root routes.

### 14.9 Wave 6 — profiles, integration, and certification

#### WP-60 — Profile/capability closure

- **Agent:** `profile-composition`
- **Owned paths:** profile resolver/build closure generator
- **Tasks:** normal/tiny/full/instrument overlays, strict tiny errors, placement independence.
- **Dependencies:** all contracts
- **Acceptance:** capability matrix, forbidden-symbol/link-map gates, tiny semantics.

#### WP-61 — CLI command capsule migration

- **Agent:** `cli-capsule-integration`
- **Owned paths:** shared CLI root/dispatch, serial only
- **Tasks:** move old unified CLI behind capsules incrementally; preserve aliases/help/output.
- **Dependencies:** Wave 1, WP-53
- **Acceptance:** all migrated commands load only owning capsules; compatibility suite.

#### WP-62 — Linux qualification

- **Agent:** `linux-qualification`
- **Owned paths:** Linux adapters/tests/reports only
- **Tasks:** ELF/maps/syscall/perf evidence, W^X, direct exec, pinned benchmarks.
- **Acceptance:** G0/G1 report with immutable identities.

#### WP-63 — Windows qualification

- **Agent:** `windows-qualification`
- **Owned paths:** Windows adapters/tests/reports only
- **Tasks:** mapping/protection/process launch/ETW evidence and performance.
- **Acceptance:** same planner semantics; blocked features explicit.

#### WP-64 — SimpleOS qualification

- **Agent:** `simpleos-qualification`
- **Owned paths:** SimpleOS loader/VFS/process ports/tests/reports
- **Tasks:** no-host fallback evidence, VFS selected reads/maps, SMF execution, QEMU/board gates.
- **Acceptance:** real launch/entry/result markers; no host binary substitution.

#### WP-65 — Benchmark harness and references

- **Agent:** `performance-harness`
- **Owned paths:** `test/05_perf`, benchmark scripts, generated reports
- **Tasks:** fair lanes, versions, immutable manifests, sample statistics, p50/p95/RSS/I/O/maps.
- **Dependencies:** WP-07
- **Acceptance:** rejects one-run/stale/fallback/mismatched-product reports; reproduces historical rows only as history.

#### WP-66 — Modern SSpec manuals

- **Agent:** `sspec-manuals`
- **Owned paths:** feature specs and generated `doc/06_spec` outputs; coordinate helper ownership
- **Tasks:** scenario steps, captures, TUI visual action evidence, traceability IDs, generated manual verification.
- **Acceptance:** explicit result counts; no hand-authored success; `sspec-maintain scan` clean.

#### WP-67 — Formal properties

- **Agent:** `formal-certification`
- **Owned paths:** generated Lean models/proofs/specs
- **Tasks:** planner, closure, W^X, cache, static/dynamic parity properties.
- **Acceptance:** generated from schemas; assumptions listed; live tests remain separate.

#### WP-68 — Release certifier

- **Agent:** `release-certifier`
- **Owned paths:** release reports/receipts only
- **Tasks:** fetch merged SHA, snapshot binaries, run full matrices, inspect link/maps, verify reports/manuals/formal results, classify blockers.
- **Acceptance:** one signed/hashed definition-of-done report; implementation agents cannot waive gates.

### 14.10 Agent work brief template

Every agent receives this exact structure:

```text
Work package:
Baseline SHA:
Fetched integration SHA:
Owned paths:
Read-only dependencies:
Frozen schema versions:
Do-not-touch paths:
Required implementation:
Required unit tests:
Required integration/system tests:
Required sabotage probe:
Required cross-mode parity:
Required performance/evidence fields:
Known blockers/unsupported targets:
Memory/parallelism budget:
Handoff artifacts:
```

### 14.11 Agent handoff template

```text
RESULT: implemented | partial | blocked
BASE_SHA:
HEAD_SHA:
FILES_CHANGED:
PUBLIC_CONTRACT_CHANGES: none | versioned details
TEST_COMMANDS:
EXPLICIT_RESULT_LINES:
DIRECT_RUN_REPRO:
SABOTAGE_PROBE:
ARTIFACT_DIGESTS:
PERF_REPORT:
STATIC/DYNAMIC_PARITY:
REFERENCE/FAST/JIT_PARITY:
KNOWN_FAILURES:
INTEGRATION_NOTES:
```

A handoff with exit code only and no explicit result line is rejected.

### 14.12 Integration order and conflict control

```text
contracts
   -> generated codecs/tables
   -> leaf implementations
   -> adapters
   -> shared root cutover
   -> platform qualification
   -> certification
```

Agents work in separate branches/worktrees. Shared hot files are touched only by the designated integration owner after leaf modules land. The integrator cherry-picks or reapplies per-file diffs onto current main, resolves semantic conflicts, and reruns affected gates.

---

## 15. Phased landing and release gates

### Phase 0 — Rebaseline and freeze

**Purpose:** establish current truth and prevent parallel contract drift.

Deliverables:

- immutable current self-hosted binaries and digests;
- root/source/SMF/native import/map/I/O traces;
- repeated current benchmark profile;
- component/schema census;
- frozen V1 contracts from Wave 0;
- explicit historical versus current report separation.

Exit gate:

```text
all schema golden vectors pass
all baseline artifacts immutable
all benchmark lanes classify product/mode/cache state
no implementation agent requires an undefined public contract
```

### Phase 1 — Stage-0 beside the existing CLI

**Purpose:** create the narrow path without risking current command coverage.

```text
new stage0
    root help/version
    route classifier
    SCI/static resolver
    fallback route -> current unified CLI capsule
```

Exit gate:

- root help/version use stage-0 only;
- existing commands still run through compatibility capsule;
- no compiler/interpreter/loader/aspect mapping for root routes;
- no startup child processes;
- root structural budgets pass;
- current CLI remains reversible through a build switch;
- invariant `--x` grammar and option-route feature bit are present, but no provider is loaded during argv parsing.

### Phase 2 — Component/CLI auto placement and SCI-only composition updates

**Purpose:** make dynamic development and static release use one contract.

Exit gate:

- matching static implementation selected;
- stale static selects exact admitted dynamic artifact;
- full rebuild folds auto component static;
- dynamic placement stays external;
- command, alias, exact-option, help, value-map, and extension-namespace config changes emit SCI with zero compiled modules/linked objects;
- an ABI-compatible provider can add `--xnamespace-key` by rebuilding only that provider and updating its artifact descriptor;
- root `simple-core` digest remains unchanged for all of the above;
- cycles, stale interfaces, and missing artifacts fail closed.

### Phase 3 — SMF V2 segment loader

**Purpose:** remove compiler/JIT creation and per-symbol executable copying from ordinary loads.

Migration:

```text
V1 artifact -> reference/compat loader
V2 artifact -> segment loader
```

Exit gate:

- real V2 emitter and loader execute fixtures;
- one segment mapping serves many exports;
- no RWX/executable stack;
- eager selected-module import binding;
- malformed corpus fails before entry;
- base loader dependency graph excludes compiler/JIT/hot reload;
- static/dynamic export conformance passes.

### Phase 4 — Aspect packs and zero-residue profiles

**Purpose:** move optional observability/debug behavior out of default closures.

Exit gate:

- logging and trace facet packs admitted dynamically;
- normal/tiny disabled builds have zero symbol/string/map/callsite residue;
- instrumented variants preserve semantics;
- readiness levels are truthful;
- core->aspect dependency audit passes;
- auto dynamic-to-static fold verified.

### Phase 5 — ExecIR fast interpreter

**Purpose:** improve steady-state interpreter performance without weakening the reference oracle.

Landing order:

```text
codec/verifier
 -> lowerer
 -> dense frames
 -> base dispatcher
 -> semantic families
 -> quickening/caches
 -> superinstructions
```

Exit gate:

- reference/fast parity across the supported semantic suite;
- malformed ExecIR rejected;
- no dictionary in admitted scalar/local hot path;
- no debug/log branch in production dispatch;
- quickening/deopt parity;
- CPython comparison G1 target reached on pinned qualification host or blocker documented.

### Phase 6 — Exact incremental compiler and SIF

**Purpose:** match the strongest Go/Rust build ideas while retaining Simple block/aspect identities.

Exit gate:

- direct-dependency SIF compilation;
- lazy entity decode;
- red-green query DAG;
- body-only change leaves importer interface green;
- exact aspect match-set invalidation;
- config-only SCI path;
- dynamic optimizer executes real transformations;
- old legacy optimizer engine cannot run in addition to canonical pipeline.

### Phase 7 — Tier 1/Tier 2, OSR, and code cache

**Purpose:** combine low startup with native-class hot execution.

Exit gate:

- no JIT mapping on cold programs;
- Tier 1 created lazily and compiles from typed IR;
- source-independence sabotage passes;
- OSR/deopt preserves complete state;
- Tier 2 emits actual LLVM code and compiles concurrently;
- memory pressure defers/cancels Tier 2 first;
- exact persistent code-cache hit avoids source/backend activation.

### Phase 8 — Profile closure and command capsule completion

**Purpose:** make normal, tiny, full, and instrumentation policies product-complete.

Exit gate:

- all CLI-0/CLI-1 commands use capsules;
- conventional exact options, aliases, help, and completion are generated from SCI;
- optional `--x<namespace>-...` forwarding is complete, admitted, scoped, and fail-closed;
- root binary no longer links unified app/tool graph;
- tiny profile fails on undeclared heavy requirements and omits unused facilities;
- full profile makes facilities available but does not eagerly activate them;
- platform ports have explicit qualification state.

### Phase 9 — Competitive qualification

**Purpose:** turn targets into truthful claims.

Exit gate:

- G0 structural suite green;
- G1 repeated measurements on pinned Linux and at least one second qualified host;
- exact tool/runtime versions and artifacts archived;
- native/source/cached/compiler lanes fair and separated;
- result-count and no-fallback evidence complete;
- generated Modern SSpec manuals reviewed;
- release certifier signs the report.

G2 "better than Go/Bun/Rust/Python" language is permitted only for the exact lanes and hosts that pass the declared ratios. It is never generalized to unrelated workloads.

---

## 16. Migration strategy

### 16.1 Avoid a flag-day rewrite

Keep existing implementations as explicit providers during transition:

```text
startup.current_unified_cli
loader.reference.current
loader.compat.symbol_copy
interpreter.reference.mir
optimizer.current_static
```

Add new providers beside them:

```text
startup.stage0.v1
loader.segment.v2
interpreter.execir.v1
optimizer.dynamic.v1
```

Route selection is controlled through SCI/profile policy and can be switched per test/build. Default changes only after parity and security gates.

### 16.2 Dual artifact emission

During loader migration, the compiler/linker can emit:

- V1 compatibility SMF;
- V2 segment SMF;
- both in qualification builds.

The test runs both and compares behavior. Tiny/new deployments can later omit V1 support.

### 16.3 CLI migration order

Move command families in risk order:

```text
root help/version
 -> read-only info/query commands
 -> fmt/lint/check helpers
 -> test tooling
 -> compile/build/native-build
 -> source run/interpreter/JIT
 -> UI/Office/IDE/OS families
```

Compiler/build routes move after SCI/component contracts and exact identity gates are stable.

### 16.4 CLI option migration

1. Land the one-time SCI option-route section, stage-0 generic router, and `SimpleCliExtensionV1` wire.
2. Inventory every option currently parsed in root/global CLI source and assign an owner, scope, arity, semantic class, help, completion, route patch, and missing policy.
3. Emit compatibility exact-option records first, preserving current spellings and accepted positions.
4. Move provider-specific behavior to the owning capsule; root keeps no behavior branch.
5. Assign short explicit extension namespaces for compiler backends, optimizers, interpreter, loader, logging/aspects, UI/Office, tests, and tools.
6. Use the namespaced path for experimental/rare options and promote stable ergonomic options to exact SCI records when warranted.
7. Compare old/new argument results, selected closure, diagnostics, completion, and cache-key projection.
8. Remove a hardcoded option only after config/static/dynamic parity and the config-only no-rebuild gate pass.

Migration must preserve application arguments. Exact options after a direct entry are intercepted only when their record declares `after_entry=true`; `--` always terminates launcher parsing. A compatibility profile may temporarily recognize legacy after-entry spellings through generated records, not hardcoded branches.

### 16.5 Logging migration

1. inventory direct core logging imports and format strings;
2. introduce typed event/fatal ports;
3. route full logging through an adapter outside core;
4. generate disabled/instrumented variants;
5. add zero-residue tests;
6. remove old imports only after output/diagnostic parity.

### 16.6 Interpreter migration

- reference MIR remains default for unsupported ExecIR operations;
- unsupported fallback is explicit in receipts and disqualifies performance rows;
- expand ExecIR semantic coverage family by family;
- make fast interpreter default only when coverage/parity reaches the declared threshold;
- keep reference selectable for debugging and certification.

### 16.7 Cache migration

- version new query/SIF/ExecIR objects in existing CAS;
- old entries remain readable only through declared migrations;
- corrupt/incompatible entries miss cleanly;
- no global cache deletion is required to land the new engine;
- cache cleanup understands object kind, reachability, age, and profile value.

---

## 17. Risks and mitigations

| Risk | Consequence | Mitigation/gate |
|---|---|---|
| Stage-0 grows into another full CLI | startup target lost | fixed lexical grammar, config-driven option routes, link/import budgets, command capsules |
| CLI option typo/unknown namespace is silently ignored | wrong execution or false test result | unknown fails closed; optional missing behavior must be explicit and receipt-visible |
| `--x` namespace hijack or arbitrary module path | untrusted code activation | globally unique configured namespaces, exact provider path/digest/ABI/capability admission |
| New Simple option steals an application argument | application compatibility break | scope windows, explicit `after_entry`, unrecognized pass-through, hard `--` boundary |
| Provider loaded merely to parse option arity/help | startup regression | exact arity/help in SCI; namespaced values require `=`; extended help index before provider query |
| Option semantic effect omitted from cache key | unsound reuse | mandatory semantic class and key-projection tests/sabotage |
| Dynamic component ABI churn | frequent dependent rebuilds | freeze/version contracts; separate interface and implementation hashes |
| Static and dynamic semantic drift | hard-to-reproduce bugs | one source/ABI/conformance suite; parity required before folding |
| General `dlopen` complexity | security/startup/TLS issues | exact paths, no interposition, eager module binding, pinning, no cycles |
| Segment loader corruption | code execution vulnerability | complete plan validation, W^X, bounds/overflow corpus, transactional rollback |
| Aspect "off" still costs branches | hot-path regression | separate stripped/instrumented variants; assembly/ExecIR absence checks |
| One pack per log level | mapping/relocation overhead | logical facets grouped into physical packs |
| Full tracing requested on stripped binary | misleading capability | explicit readiness `none|boundary|full`; fail/require instrumented variant |
| ExecIR becomes another unstable IR | maintenance duplication | generated schema/codec/dispatch/JIT; MIR->ExecIR boundary narrow and versioned |
| Quickening thrash | slower execution | miss/deopt counters; polymorphic limits; stable generic fallback |
| Tiering compiles short-lived code | startup/memory regression | benefit-cost policy; lazy engine; concurrent bounded queues |
| Tier 2 consumes bootstrap memory | OOM/build failure | build priority; memory admission; cancel Tier 2 first |
| Query cache unsoundness | wrong code | exact keys, result hashes, reference uncached path, randomized/sabotage tests |
| Cache over-retention | high RSS/disk exhaustion | tiered quota, reachability, LRU/value scoring, bounded resident hot set |
| Parallel compiler lock contention | no speedup or regression | immutable results, worker-local arenas, scaling gate, serial global phases |
| Historical benchmark gaming | false "better than" claims | current SHA, repeated samples, fair lanes, external evidence, one certifier |
| Self-host path not reached | tests pass wrong compiler | exact binary identity, source sabotage, direct run repro, no Rust seed fallback |
| Silent test runner success | false green | explicit results/count line mandatory; otherwise `INCONCLUSIVE` |
| Platform implementation diverges | host-only architecture | common plan/contracts, separate port tests, SimpleOS/Windows qualification |
| Tiny profile changes semantics | unsafe surprise | strict capability analysis; compile error rather than silent feature removal |
| Full profile eagerly loads everything | large startup | availability/activation separation, first-use/command activation |

### 17.1 Explicitly rejected shortcuts

Do not:

- mark all imports `lazy` and call the architecture complete;
- keep one monolithic binary and rely on the OS not faulting unused pages;
- parse full project configuration during root startup;
- scan plugin directories;
- use environment variables as the primary untyped component registry;
- add provider-specific options or module-name switches to stage-0 source;
- infer an extension provider from a filename, import path, or directory scan;
- silently ignore an unknown `--x` namespace or missing semantic provider;
- consume the next argv token as a namespaced extension value;
- load a provider merely to discover its option schema during normal routing;
- leave logging checks in every interpreter instruction;
- JIT by reparsing source at hotspot time;
- compare first-run source execution with an already-linked native binary;
- optimize the reference interpreter until it no longer serves as an oracle;
- create a second semantic cache;
- accept SMF magic/export-name checks as evidence of real implementation;
- report exit zero as test success without an explicit result line.

---

## 18. Definition of done

### 18.1 Startup

- `simple --help` and `simple --version` execute through stage-0 only.
- No SCI, project config, compiler, interpreter, loader, aspect, UI, Office, IDE, or test module is opened/mapped.
- No child process is created.
- Stage-0 route classification is allocation-free under the qualified ABI.
- SCI lookup is bounded and exact for non-root routes.
- Public policy says `load`, not `mmap`; host strategy is an implementation receipt.
- G1 startup ratios pass on pinned qualification hosts.

### 18.2 Composition and aspects

- Presence, placement, and activation are separate typed policies.
- Auto placement chooses matching static code and exact dynamic code on mismatch.
- Full rebuild automatically folds configured defaults static.
- Dynamic-always remains external.
- Disabled aspects have zero code/string/callsite/load-plan residue.
- Core imports no aspect implementation.
- Static/dynamic facet parity and corrupt-pack security tests pass.

### 18.3 Config-driven CLI surface

- Adding/renaming a command, exact option, alias, help summary, value map, completion entry, or extension namespace regenerates SCI without compiling modules or linking objects.
- The immutable `simple-core` digest remains unchanged for those edits.
- `--x<namespace>-<key>[=<value>]` routes only to an exact configured/admitted provider; no filesystem scan or shell forwarding occurs.
- Namespaced values require `=`; a bare form is a flag.
- Unknown options/namespaces and missing required providers fail closed; optional missing behavior is explicit and receipt-visible.
- Reserved core spellings and `--x` cannot be overridden; aliases/namespaces are collision-free.
- `--` prevents all later interception, and direct-entry application argument compatibility passes.
- Root help/version remain zero-I/O; index help loads no provider; full provider help loads only the requested provider.
- Option semantic classes produce exact cache-key projections.
- ABI-compatible provider option changes rebuild only the provider; release auto-fold stays inside its owning capsule, never stage-0.

### 18.4 Loader

- Ordinary V2 load constructs no compiler/JIT/hot-reload service.
- Code is mapped per segment, not per symbol.
- W^X, non-executable stack, exact dependencies, and eager selected-module binding are enforced.
- V2 emitter produces real callable artifacts, not hollow stubs.
- Static/dynamic providers share one ABI and conformance suite.
- V1 compatibility is explicit and removable from tiny builds.

### 18.5 Interpreter and JIT

- ExecIR schema, generator, verifier, and interpreter are versioned and deterministic.
- Fast frames use dense typed storage.
- Production dispatcher has no debug/log/profile branch.
- Quickening/inline caches/deopt are semantically equal to base opcodes.
- Reference/fast/Tier1/Tier2 parity passes for supported semantics.
- Cold programs load no JIT backend.
- Tier 1/2 compile typed IR without source reread.
- OSR/deopt and exact code cache are proven.
- G1 interpreter and warm-tier targets pass or remain explicitly blocked—not waived.

### 18.6 Compiler

- Compiler engine is separate from CLI/tools/UI.
- SIF supports indexed direct-dependency metadata.
- Exact red-green query DAG and existing CAS integration are live.
- Body-only changes do not invalidate importers when public results remain green.
- Aspect invalidation uses exact match-set identities.
- Dynamic frontend/MIR/backend optimizers execute real code and can be updated without a core rebuild.
- Full rebuild folds auto optimizers static.
- Dev-fast and release pipelines preserve the same semantic checks.
- Compiler performance reports meet sample/identity/evidence contracts.

### 18.7 Profiles

- `normal` is the default, complete expected behavior, lazily activated.
- `tiny` is explicit and fails on incompatible requirements.
- `full` makes capabilities available without eager startup loading.
- instrumentation is an overlay with truthful readiness.
- tiny native closure can be compared fairly with Go/Rust native output.

### 18.8 Verification and documentation

- All requirement IDs have executable specs.
- Every major path has a sabotage probe.
- Explicit result/scenario counts are present.
- `BLOCKED`, `INCONCLUSIVE`, and `UNVERIFIED` are not reported as pass.
- Modern SSpec manuals are generated and reviewed.
- Formal schema properties pass and list assumptions.
- Release report names exact merged SHA and artifact digests.
- One independent certifier signs the final claim set.

---

## Appendix A. Proposed configuration model

Human-readable source configuration, compiled to SCI:

```yaml
profile: normal

startup:
  index: auto
  diagnose: false
  direct_native_exec: true

cli:
  exact_options:
    - name: --execution
      aliases: [--exec-mode]
      scope: global
      value_mode: required
      action: select_route_variant
      values:
        auto: route.source.auto
        interpret: route.source.interpret
        jit: route.source.jit
        native: route.source.native
      help: Select source execution mode
      semantic_class: runtime_selection

    - name: --backend
      scope: [compile, run-source]
      value_mode: required
      provider: compiler.cli
      action: provider_forward
      forward_name: --backend
      semantic_class: compile_semantic
      after_entry: true

  extension_namespaces:
    - namespace: llvm
      provider: backend.llvm
      binding: cli.extension.llvm
      availability: optional
      missing_policy: error
      help: LLVM backend extensions

    - namespace: log
      provider: aspect.log
      binding: cli.extension.log
      availability: optional
      missing_policy: warn_skip
      semantic_class: instrumentation

    - namespace: vectorize
      provider: optimizer.vectorize
      binding: cli.extension.vectorize
      availability: optional
      missing_policy: error
      semantic_class: compile_semantic

components:
  compiler.frontend:
    presence: auto
    placement: auto
    activation: command

  interpreter.fast:
    presence: auto
    placement: auto
    activation: command

  loader.base:
    presence: auto
    placement: auto
    activation: command

  backend.cranelift:
    presence: auto
    placement: auto
    activation: hotspot

  backend.llvm:
    presence: auto
    placement: dynamic
    activation: hotspot

  optimizer.vectorize:
    presence: auto
    placement: auto
    activation: command

aspects:
  log.error:
    presence: auto
    placement: auto
    activation: first_use

  log.debug:
    presence: off

  interp.trace:
    presence: off

security:
  exact_paths: true
  require_digest: true
  require_interface_hash: true
  allow_directory_scan: false
  allow_module_unload: false
```

After editing only `optimizer.vectorize`, the developer build emits a new optimizer artifact and SCI descriptor. A later full compiler rebuild embeds the matching implementation and no longer loads the artifact unless placement is `dynamic`. Adding `--xvectorize-cost=high` to the existing optimizer provider requires only that provider artifact; adding an ergonomic exact alias such as `--vector-cost` regenerates the CLI option SCI section, still without rebuilding `simple-core`.

---

## Appendix B. Startup closure examples

### B.1 Root version

```text
simple --version

loaded:
    stage0

not loaded:
    SCI
    compiler
    interpreter
    loader
    JIT
    aspects
    UI/tools
```

### B.2 SMF execution

```text
simple app.smf

loaded:
    stage0
    SCI only if route/config requires
    loader.base
    exact direct dependencies

not loaded by default:
    compiler
    interpreter
    JIT
    hot reload
    generic instantiation
    debug aspects
```

### B.3 Fresh interpreted source

```text
simple app.spl --execution=interpret

loaded:
    stage0
    source route capsule
    compiler.frontend/semantic/MIR-or-ExecIR-lowering required by cache state
    interpreter.fast
    required runtime capabilities

not loaded:
    Cranelift/LLVM
    release optimizer packs
    compiler tools/UI
```

### B.4 Cached ExecIR source

```text
simple app.spl --execution=interpret

valid exact ExecIR cache hit:
    stage0
    cache/index reader
    interpreter.fast
    required runtime

frontend/compiler engine not loaded
```

### B.5 Compilation

```text
simple compile app.spl --backend=cranelift

loaded:
    stage0
    compile CLI capsule
    frontend/semantic/MIR
    selected optimizer plan
    backend.cranelift
    linker/emitter

not loaded:
    interpreter
    LLVM
    GUI/Office/IDE
    debug aspects unless requested
```

### B.6 Config-added exact option

```text
edit cli.sdn: add --new-mode
simple build

work:
    parse/validate composition config
    regenerate CLI option SCI section
    atomic SCI replace

compiled modules: 0
linked objects:    0
simple-core digest: unchanged
```

### B.7 Namespaced provider option

```text
simple compile app.spl --xllvm-pass=gvn

stage0:
    parse x namespace/key/value shape
    resolve namespace llvm in SCI
    admit only backend.llvm provider
    forward structured {key: pass, value: gvn}

not loaded merely for parsing:
    other backends
    interpreter
    Office/UI/tools
```

### B.8 Optional missing module

```text
--xlog-level=debug
namespace log: availability=optional, missing_policy=warn_skip
provider absent:
    emit one warning + compact receipt
    do not scan directories
    do not silently claim logging enabled

release/mission-critical:
    warn_skip/silent_skip may be prohibited by policy
```

---

## Appendix C. Best-of-system mapping

| Goal | External best idea | Simple implementation |
|---|---|---|
| native startup | Go/Rust move compiler out of runtime | closed native/tiny closure; direct exec |
| source startup | Bun native launcher and bytecode caching | stage-0 + exact ExecIR/SMF/native cache |
| interpreter dispatch | CPython generated dispatch/tail calls | generated switch/computed-goto/tail-call variants |
| dynamic specialization | CPython PEP 659 | typed adaptive families and inline caches |
| tiered hot execution | JavaScriptCore LLInt/Baseline/DFG/FTL | ExecIR Tier0A/0B, Cranelift Tier1, LLVM Tier2 |
| compiler dependency metadata | Go unified indexed export data | indexed SIF with direct dependencies |
| incremental compilation | rustc red-green query DAG | exact block/query DAG over existing CAS |
| backend substitution | rustc backend-agnostic codegen | versioned backend port/components |
| development/release tradeoff | Cargo profiles | dev-fast/release/tiny/normal/full composition |
| dynamic-loader robustness | glibc explicit binding/hardening | exact module admission, eager module binding, W^X, pinning |
| optional instrumentation | link-time stripping + provider packs | aspect facets, stripped/instrumented variants, auto static fold |
| CLI extensibility | GCC plugin arg namespace, Cargo subcommands, LLVM static/dynamic plugin parity | SCI exact options + `--x<namespace>-...` + one provider ABI, no core relink |

---

## Appendix D. Required benchmark report header

```text
report_schema_version:
date_utc:
repo_sha:
source_tree_dirty:
compiler_binary_path:
compiler_binary_digest:
launcher_binary_digest:
SCI_digest:
SMF/ExecIR schema versions:
profile:
target:
host OS/kernel:
CPU/model/microcode:
logical/physical CPUs:
CPU affinity/governor:
memory limit:
container metadata:
run count/warmup count:
cache state:
reference tool versions:
output/checksum contract:
explicit result count:
fallback count:
blocked lanes:
```

---

## Appendix E. Research and repository references

### External primary sources

1. Go compiler architecture and unified export data: <https://go.dev/src/cmd/compile/README>
2. Go compile command and direct-dependency compiled metadata: <https://go.dev/src/cmd/compile/doc.go>
3. Bun runtime startup documentation: <https://bun.com/docs/runtime>
4. Bun benchmarking guidance: <https://bun.com/docs/project/benchmarking>
5. Bun compiled executables and bytecode: <https://bun.com/docs/bundler/executables>
6. JavaScriptCore compact bytecode: <https://webkit.org/blog/9329/a-new-bytecode-format-for-javascriptcore/>
7. JavaScriptCore speculation and tiers: <https://webkit.org/blog/10308/speculation-in-javascriptcore/>
8. CPython interpreter internals: <https://github.com/python/cpython/blob/main/InternalDocs/interpreter.md>
9. PEP 659 specializing adaptive interpreter: <https://peps.python.org/pep-0659/>
10. rustc incremental compilation: <https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation.html>
11. rustc backend-agnostic codegen: <https://rustc-dev-guide.rust-lang.org/backend/backend-agnostic.html>
12. rustc parallel compilation: <https://rustc-dev-guide.rust-lang.org/parallel-rustc.html>
13. Cargo build profiles: <https://doc.rust-lang.org/book/ch14-01-release-profiles.html>
14. GNU C Library dynamic-linker hardening: <https://sourceware.org/glibc/manual/latest/html_node/Dynamic-Linker-Hardening.html>
15. Rust embedded `no_std` runtime model: <https://doc.rust-lang.org/stable/embedded-book/intro/no-std.html>
16. Rust panic/abort behavior: <https://doc.rust-lang.org/stable/reference/panic.html>
17. Python command-line startup/import timing options: <https://docs.python.org/3/using/cmdline.html>
18. Python `site` startup behavior and `-S`: <https://docs.python.org/3/library/site.html>
19. GCC plugin loading and namespaced plugin arguments: <https://gcc.gnu.org/onlinedocs/gccint/Plugins-loading.html>
20. LLVM new-pass-manager plugins, dynamic and static registration: <https://llvm.org/docs/WritingAnLLVMNewPMPass.html>
21. Cargo external/custom subcommands: <https://doc.rust-lang.org/beta/book/ch14-05-extending-cargo.html>
22. rustc tracked/untracked compiler option model: <https://doc.rust-lang.org/stable/nightly-rustc/rustc_session/config/struct.Options.html>
23. Go build cache implementation: <https://go.dev/src/cmd/go/internal/cache/cache.go>
24. Go compiler SSA reusable caches: <https://go.dev/src/cmd/compile/internal/ssa/cache.go>
25. Go linker dead-code elimination: <https://go.dev/src/cmd/link/internal/ld/deadcode.go>

### Inspected Simple repository paths

- `src/app/cli/_CliMain/main_and_help.spl`
- `src/app/cli/__init__.spl`
- `src/app/startup/host_startup.spl`
- `src/app/startup/launch_metadata.spl`
- `src/app/startup/dynsmf_autoload.spl`
- `src/os/smf/dynsmf_session.spl`
- `src/os/smf/provider_loader.spl`
- `src/os/smf/provider_activation.spl`
- `src/lib/nogc_sync_mut/composition/types.spl`
- `src/lib/nogc_sync_mut/composition/source.spl`
- `src/lib/nogc_sync_mut/composition/codec.spl`
- `src/lib/nogc_sync_mut/composition/provider_contract.spl`
- `src/lib/nogc_sync_mut/composition/cli_command_wire.spl`
- `src/lib/nogc_sync_mut/composition/cli_provider_wire.spl`
- `src/lib/nogc_sync_mut/composition/cli_registry.spl`
- `src/compiler/99.loader/loader/module_loader.spl`
- `src/compiler/95.interp/mir_interpreter.spl`
- `src/compiler/95.interp/execution/tiered_jit.spl`
- `src/compiler/95.interp/execution/tiered_jit_manager.spl`
- `src/compiler/60.mir_opt/optimizer_plugin.spl`
- `src/compiler/60.mir_opt/optimizer_manifest.spl`
- `src/compiler/60.mir_opt/mir_opt/mod.spl`
- `src/compiler/10.frontend/syntax_opt/README.md`
- `src/compiler/90.tools/aop.spl`
- `test/README.md`
- `doc/07_guide/infra/sspec_scenario_manual.md`
- `test/05_perf/README.md`
- `test/05_perf/compiler_loader_script_crosslang_perf_spec.spl`
- `test/05_perf/cli_dispatch_perf_spec.spl`
- `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`
- `doc/09_report/startup_size_performance_audit_2026-05-27.md`

### Prior design decisions incorporated

- minimal rebuild and ad-hoc bootstrap speed plan;
- SCI/provider-only config updates;
- aspect/facet dynload SMF pack design;
- exact semantic incremental build/cache and AOP invalidation design;
- memory/parallel MDSOC+ ownership and one-file-owner agent policy;
- Modern SSpec GUI/TUI/network/binary evidence and generated-manual rules;
- debugging evidence rule that raw exit zero is not a passing result.

---

## Final recommendation

Implement the plan in this order:

```text
freeze contracts and rebaseline
    -> stage-0 + SCI/static/dynamic resolver
    -> config-driven command/exact-option/`--x` provider routing
    -> SMF V2 segment loader
    -> zero-residue aspect packs
    -> ExecIR fast interpreter
    -> exact query/SIF compiler
    -> Tier 1/Tier 2 + OSR/code cache
    -> complete command/profile migration
    -> multi-platform competitive qualification
```

The design can make Simple lighter than Go in a qualified tiny-native lane, faster than the Go tool in a qualified stage-0 route lane, substantially faster than CPython in a typed interpreter lane, competitive with Bun on cached/fresh source startup, and competitive with Go/Rust in native and incremental compiler lanes. Config-driven options ensure that CLI surface growth does not reverse those gains by pulling provider behavior back into the launcher. Those outcomes are plausible because the architecture removes work rather than hiding it, but every claim remains conditional on the exact Modern SSpec and repeated benchmark gates defined above.

## Verification addendum (2026-08-17)

Each current-code claim in this document was re-verified against the working tree on 2026-08-17. Verdicts with evidence:

1. **Launch metadata exposes `mmap_hint`, `include_mmap_cache`, and a cache strategy named `mmap` — CONFIRMED.** `src/app/startup/launch_metadata.spl:13` (`mmap_hint: bool`), `:25` (`include_mmap_cache: bool`), `:110-111` (`_cache_strategy` returns `"mmap"` when host mmap is supported). Script/SMF entries default `mmap_hint` to true (`:57`, `:86`).
2. **Unified CLI main directly imports build/compile/check/browser/UI/Office/IDE/play/T32/stats/OS command families — CONFIRMED.** `src/app/cli/_CliMain/main_and_help.spl:10` (`cli_compile`), `:23` (`app.build.cli_entry`), `:24` (`app.cli.check`), `:32` (`app.cli.browser`), `:34` (`app.ui.cli_entry`), `:35` (`app.office.mod`), `:36` (`app.ide.main`), `:37` (`app.play.main`), `:38` (`app.t32_cli.mod`), `:39`/`:41` (stats), `:44` (`os.cli`). A minority of imports are `lazy` (`:45-48`).
3. **Module loader constructs ObjTaker, object provider, JIT instantiator, exec mapper, cache manager, and lifecycle manager at creation; default config enables JIT+cache; per-symbol alloc/copy/protect — CONFIRMED.** `src/compiler/99.loader/loader/module_loader.spl:145-180` (`moduleloader_new` builds `ObjTaker.with_compiler_context`, `JitInstantiator.new`, `LoaderMapper.new`, cache manager and `lifecycle_new` eagerly); `:94-96` (`moduleloaderconfig_default` sets `enable_jit: true`); `:20` imports `native_alloc_rw_memory`/`native_make_executable`/`native_write_exec_memory`, used per symbol via `moduleloader_allocate_exec_module` (`:235`).
4. **MIR interpreter uses dictionaries for locals/blocks/functions and imports a logging facade — CONFIRMED.** `src/compiler/95.interp/mir_interpreter.spl:89` (`locals: {i64: i64}`), `:91` (`blocks: {i64: MirBlock}`), `:209` (dict-based function table), `:17` (`use std.log.{debug}`) with debug calls e.g. `:209`.
5. **Tiered JIT manager creates the JIT handle eagerly and compiles retained source text at threshold; Tier 2 transition is state-only — CONFIRMED.** `src/compiler/95.interp/execution/tiered_jit_manager.spl:33-35` (`create` calls `rt_jit_create()` at construction), `:12` (`rt_jit_compile_source(handle, source: text)`), `:82` (`_compile_function(decision.compile_source)` at `tier1_threshold`), `:86-89` (Fast→Optimized branch only sets `new_tier` and increments `tier2_compilations`; no compile call). Profiles retain `source: text` (`tiered_jit.spl:45`).
6. **Optimizer dynamic manifest is a skeleton; built-in passes directly imported; a dynamic descriptor without a typed `PassKind` can pass without executing — CONFIRMED.** `src/compiler/60.mir_opt/optimizer_manifest.spl:1` ("Skeleton Implementation") with direct imports `:14-28`; `src/compiler/60.mir_opt/optimizer_plugin.spl:80` (`mir_pass_kind: PassKind?`), `:141-149` (`optimizer_plugin_from_dynamic_descriptor` sets `mir_pass_kind: nil`), `:254-266` (run adapters return the function/module unchanged when `mir_pass_kind` is `nil`).
7. **SCI composition has a sectioned decoder, `SimpleCliCommandV1` wire, provider admission separate from activation, and no option-route section — CONFIRMED.** `src/lib/nogc_sync_mut/composition/codec.spl:451-486` (section directory, bounds/overlap/digest checks); `SimpleCliCommandV1` in `cli_command_wire.spl` (also re-exported via `__init__.spl`, used by `cli_registry.spl`); admission vs activation separated in `provider_generation.spl:68-73` (`SIMPLE_GENERATION_ADMISSION_REQUIRED` validation receipt) vs `:91-119` (`provider_generation_activate_v1`); grep for `option_route`/`OptionRoute` across `src/lib/nogc_sync_mut/composition/` returns nothing.
8. **dynSMF default manifest entries are on-demand, not autoloaded — CONFIRMED.** `src/os/smf/dynsmf_session.spl:69-88` — every entry in `dynsmf_default_manifest()` has `default_autoload: false` (comment at `:78-80` states toolchain entries are "on-demand only"); `src/app/startup/dynsmf_autoload.spl:59-67` only queues missing background compiles and runs `dynsmf_session_autoload_checked` without spawning compiler children at startup.

No inline corrections were required: all eight claims matched current source.

---

## Status addendum 2026-08-18 (claims re-verified; history above unchanged)

- Claim 6 (optimizer nil `PassKind` passes without executing) — **FIXED**:
  `25a48297651` makes nil PassKind fail closed in the plugin adapters;
  `e985aceeacf` adds entry_symbol registry routing (also fail-closed).
- Claim 8 (dynSMF default manifest on-demand / autoload consumption) —
  **superseded by config**: `a663c1145b1` + `281d8adde3b` land the
  presence/placement/activation dynload axes with SDN+env config and
  fail-closed resolution.
- §0/§5 load_policy and CLI option-route recommendations — landed
  (`e5b58f7efc3`, `63f19a30473`, `131721fb924`, `0927c2e6ec7`).
- Still open from §10/§14: `interface_digest_of` remains zero-caller;
  SmfManifest is still unverified on load; `test/05_perf/startup/` lanes
  do not exist. See the plan doc's "Status 2026-08-18" for the full table.
