# Simple Compiler and Interpreter Performance Program

**Status:** integrated architecture and parallel implementation plan
**Repository baseline inspected:** ormastes/simple, August 9, 2026
**Primary targets:** fast compiler iteration, sub-Bun/Python cached startup, substantially faster interpreter throughput, demand-loaded aspects, and safe background SMF generation.

Companion docs:
- `doc/05_design/compiler/semantic_incremental_build_cache_aop_formal_2026-08-09.md` (cache/formal design)
- `doc/03_plan/compiler/cache/semantic_incremental_build_v2_plan_2026-08-09.md` (C0–C11 cache waves)
- `doc/03_plan/compiler/build_system/targeted_build_interface_compat_minimal_bootstrap_2026-08-10.md` (targeted build / minimal bootstrap)

---

## 1. Executive decision

Simple should converge on one performance architecture, rather than independently adding a shared-memory cache, compiler daemon, SMF cache, bytecode engine, JIT, and dynamic-aspect loader.

The architecture has six cooperating layers:

```text
1. Canonical semantic identity
   ActionDigest / InterfaceDigest / ArtifactDigest / RuntimeGeneration

2. Immutable artifact storage and sharing
   workspace index → machine CAS → trusted remote-main CAS
   read-only mmap on Linux/macOS/Windows

3. Semantic incremental compiler
   demand-driven red/green queries
   declaration/function/AOP/macro dependency granularity

4. Tiered execution
   tree-walk oracle
   → register bytecode
   → adaptive quickened bytecode
   → low-latency native tier
   → optimized Cranelift/AOT

5. Demand-loaded capabilities and aspect packs
   tiny catalog at startup
   no aspect payload until requested
   precomputed join-point plans instead of runtime pointcut scans

6. Persistent compiler service
   workspace query graph
   filesystem watcher
   foreground compiler queue
   budgeted background SMF/native artifact warming
```

Central rules:

1. **Do not create a second cache or second action-key scheme.** Extend the existing Option-C SHA/CAS identity model and semantic-cache v2 work (workspace state / machine-global immutable CAS / trust-scoped remote action mappings).
2. **Do not use the daemon heap as the cross-process cache.** Immutable compiler/runtime artifacts should be canonical frozen SMF/CAS images mapped read-only by any compiler, interpreter, IDE, or daemon process.
3. **Do not keep the tree-walk interpreter as the production fast engine.** It remains the semantic oracle, debugger-friendly fallback, and compatibility engine. The existing bytecode VM and MIR-to-bytecode compiler become the production baseline.
4. **No unused aspect or optional runtime library** should be opened, mapped, decompressed, initialized, or pointcut-matched at startup.
5. **Background compilation may accelerate the next run, but may never compete materially with the current foreground run.**

---

## 2. Current performance position

Cross-language startup baseline (single-run profile — diagnostic, not release-grade):

| Mode | Current hello startup |
|---|---:|
| Simple interpreter | 27.337 ms |
| Simple SMF | 19.528 ms |
| Simple native | 3.533 ms |
| Python | 24.291 ms |
| C | 3.032 ms |

The 20-run startup audit measured Simple core-native hello at ~3.129 ms and the mmap/preload lane at ~4.681 ms — the OS loader and minimal native runtime already operate near the target range; the problem is work in the interpreter/driver/startup stack, not process-launch floor.

Comparison versions as of 2026-08-09: Bun 1.3.14 (2026-05-13), Python 3.14.6 (2026-06-10). Bun's documented 5.2 ms Linux hello is an engineering target, not directly comparable evidence.

### Current high-cost paths

**2.1 Startup eagerly initializes dynSMF.** `src/app/main.spl` calls `dynsmf_startup_session(...)` before determining whether the command needs any dynamic library. The default dynSMF manifest marks seven general libraries `default_autoload: true` (file, network, 2D rendering, GUI, web, TUI, HTML UI). Startup can also spawn a separate shell + `bin/simple compile` process per missing queued entry.

**2.2 Interpreter AOP is a hot-path algorithm.** The interpreter tokenizes raw pointcut text, evaluates glob/boolean selectors, scans advice lists, priority-sorts, and resolves advice by function-name scan — around interpreted calls. Correct as compatibility path; incompatible with a fast VM. A production VM must execute a precomputed advice chain.

**2.3 The bytecode engine exists but is not the normal `simple run` baseline.** The run path checks for a cached SMF else uses `CompileMode.Interpret`. The existing VM mixes destination-indexed loads with PUSH/POP stack arithmetic; the MIR compiler emits push/push/op/pop for operations MIR already holds in SSA form.

**2.4 Cache identities exist but normal compilation is not driven through them.** Action-key/CAS implementations exist but are not wired into normal callers; live incremental still uses `.build_cache.sdn` and an ad hoc function-name MIR cache. Missing: normalized pointcuts, stable block identities, per-target weave artifacts, reusable dataflow framework.

---

## 3. Performance target definition

"Faster than Bun and Python" must be testable, not "every feature beats every workload."

### 3.1 Startup targets (designated Linux x86-64 reference machine)

| Scenario | Required target |
|---|---|
| `simple --help` / no-op | No daemon connection, no aspect load, no SMF validation |
| Warm cached `simple run hello.spl` | p50 ≤ 4.5 ms |
| Warm cached `simple run hello.spl` | Faster than same-host Bun 1.3.14 and Python 3.14.6 |
| p95 cached startup | ≤ 1.10× the faster external runtime |
| Cold filesystem-cache SMF launch | p50 ≤ 12 ms |
| First uncached small source launch | Faster than Python; Bun parity is a stretch gate |
| No-aspect application | Zero aspect-pack payload bytes mapped |
| Second launch after background generation | No parse/HIR/MIR/codegen work |
| Foreground run while warmer operates | p95 regression < 2% |

4.5 ms is an engineering budget, not a present claim — validate per platform.

### 3.2 Runtime targets

1. **Bytecode baseline:** faster geomean than CPython 3.14.6 on the declared language-core suite.
2. **Adaptive bytecode:** ≥ 20% faster than initial bytecode on dynamic dispatch, field access, calls, mixed-type workloads.
3. **Native hot tier:** faster geomean than Bun 1.3.14 on a declared typed-compute + server-kernel suite.
4. **No catastrophic outliers:** no accepted workload > 1.25× slower than the relevant comparison without an explicit architecture explanation.
5. **AOT:** approach or exceed Go on typed workloads; reduce the remaining gap to optimized C.

Report Python default, tail-call interpreter, and JIT-enabled lanes separately.

---

## 4. Integrated target architecture

```text
                          TRUSTED REMOTE
                    ┌────────────────────────────┐
                    │ remote-main action index   │
                    │ optional branch index      │
                    │ immutable remote CAS       │
                    └──────────────┬─────────────┘
                                   │ verify/backfill
                                   ▼
                             MACHINE GLOBAL
                    ┌────────────────────────────┐
                    │ $SIMPLE_CACHE              │
                    │ immutable CAS              │
                    │ frozen runtime images      │
                    │ bytecode/SMF/native code   │
                    │ module/interface summaries │
                    │ aspect packs               │
                    └──────────────┬─────────────┘
                                   │ read-only mmap
             ┌─────────────────────┼─────────────────────┐
             ▼                     ▼                     ▼
      direct run fast path    compiler daemon       IDE/interpreter
             │                     │
             │             workspace query graph
             │             persistent overlays
             │             watcher generations
             │             worker scheduler
             │             artifact warm queue
             ▼
      fresh RuntimeGeneration
             │
      register bytecode → adaptive quickening → low-latency native → optimized Cranelift/AOT
```

Branch/commit identity governs admission and provenance only; it never enters the semantic action key (see cache design doc §14.3).

---

## 5. Fast startup design

### 5.1 Direct-hit path must not require a daemon round trip

```text
simple run app.spl
    ├─ minimal native command decoding
    ├─ read compact LaunchMetadata
    ├─ check workspace freshness receipt
    ├─ exact action-index lookup: L1 workspace → L2 machine → optional L3 remote
    ├─ mmap bytecode/SMF artifact
    ├─ create fresh RuntimeGeneration
    └─ invoke entry
```

Only on an artifact miss: connect to a compatible compiler daemon (self-launch current binary if absent), compile minimum bytecode closure, publish, execute, enqueue optimized SMF/native artifact. A newly rebuilt compiler uses a different `DaemonCompatibilityId` and never consumes stale state from the old binary.

### 5.2 Minimal startup dispatcher

The first startup code parses only: command kind, entry artifact kind, target runtime, required capabilities, argument-parser requirement, cache/mmap hint, explicit startup aspects.

Change the current sequence from `init log stack → init dynSMF → possibly launch compilers → determine command` to `determine command → read launch metadata → load only required mechanisms`.

### 5.3 Frozen Simple runtime image

Canonical SMF profile `kind=runtime_image`:

- **Header:** format/schema, compiler/runtime compatibility, ArtifactDigest, target flags.
- **Read-only sections:** compact string pool, identifier/type tables, builtin function table, opcode metadata, minimal stdlib interfaces, fallback parser tables, bytecode function metadata, aspect **catalog only**.
- **Optional/lazy:** debug/source maps, full AST/HIR, extended stdlib modules, diagnostics tables.

Rules: relative offsets or stable IDs, never native pointers; directly usable from a read-only mapping; platform-neutral sections shared across OSes; native code/relocation/ABI target-keyed; loading must not rebuild a large HAMT or deserialize thousands of heap objects; validate once, expose typed mapped views. (Precedent: Clang PCH/modules lazy deserialization.)

### 5.4 Stable base plus persistent overlay

```text
Bulk construction: mutable transient builder → freeze
Stable state:      compact frozen flat index in mmap
Evolving state:    persistent HAMT/tree overlay

Lookup: workspace overlay → frozen base → new query/parse result
```

Compact a large overlay into a new immutable image generation periodically; old processes keep the old generation (MVCC snapshots). Freeze logical segments (module/symbol/type/macro/aspect indexes), not per-node CAS objects.

---

## 6. Demand-loaded aspects and optional libraries

### 6.1 Separate capability libraries from aspect packs

```simple
enum RuntimeComponentKind:
    Core        # required
    Capability  # import/first-call
    Renderer    # LaunchMetadata-selected
    Tool        # explicit invocation
    AspectPack  # explicit, lazy facet, or predeclared lazy join point
    DebugOnly   # manual
```

The seven currently eager dynSMF entries default to **not autoloaded** unless launch metadata proves one is required.

### 6.2 Aspect semantic classification

| Aspect mode | Load after startup? | Required treatment |
|---|---|---|
| Static structural aspect changing layout/type conformance | No | Build-time weave; in action identity |
| Static target selection, lazy advice impl | Yes | Precompute target slots; load impl pack on demand |
| Explicit dynamic facet | Yes | Acquire via `FacetRef`; no unrelated business-path overhead |
| Dynamic observational advice | Yes, with declared slots | Patchpoint or activation-slot guard |
| Tool/debug aspect | Yes | Manual or profile-triggered |
| Arbitrary late pointcut over undeclared targets | No efficient safe form | Reject or require static weaving |

### 6.3 Tiny startup Aspect Catalog

The core application SMF contains only: AspectId/FacetId/JoinPointSlot, activation policy, pack ArtifactDigest, module/chunk offset, ABI/capability requirements, dependency pack IDs, contract/selection digest. No implementation code, no full pointcut text, no decompressed metadata, no runtime registries, no initialized state. Each pack module/cluster is independently addressable and independently compressed.

### 6.4 Precomputed join-point plans

```text
FunctionId → JoinPointPlan
    before_chain[] / after_success_chain[] / after_error_chain[] / around_chain[]
    required_activation_slots[]
    selection_digest
```

Chains hold direct AdviceFunctionId references in final priority order. The production runtime must not tokenize pointcut strings, glob-match, scan advice, sort priorities, or locate advice by name — those happen at compile/selection time.

### 6.5 Runtime activation state machine

```text
Catalogued → Loading(ticket, single-flight:
    fetch/map pack → verify manifest+hashes → verify ABI/capability/deps →
    relocate/resolve → construct witnesses/advice tables)
→ Staged → (one atomic publication) → Active(generation)
Failure → Failed(reason, retry_policy)
```

No thread observes a partially resolved aspect; concurrent callers wait on the ticket or follow declared fallback. (Precedents: LLVM ORC lazy reexports; OSGi lazy activation.)

### 6.6 Disabled-path cost

- **Explicit facet acquisition** (`cache.try_facet<Debuggable>()`) — zero overhead in unrelated functions.
- **Transparent dynamic advice** — predeclared join point has a bytecode activation-slot opcode, an indirect function slot, or a native patchable NOP/jump site. Near-zero dormant cost (Linux static-keys tradeoff).

---

## 7. Background SMF cache for the next launch

### 7.1 Replace startup shell spawning

Remove `startup → process_spawn_async("sh", ...) → one bin/simple per missing entry`. Replace with one **ArtifactWarmService** (foreground compile queue, background warm queue, single-flight ActionDigest table, resource budget, cancellation by source generation, CAS publisher) living in the compatible compiler daemon.

### 7.2 Background task model

```simple
struct WarmRequest:
    action_digest: Digest
    source_generation: Digest
    artifact_kind: WarmArtifactKind
    priority: WarmPriority   # P0 fg-required miss … P4 speculative
    reason: WarmReason
    estimated_saved_ms: u64
    estimated_compile_ms: u64
    last_use_count: u32
```

Scheduling score: `probability_of_reuse × expected_fg_time_saved ÷ (compile_cost + storage_cost + staleness_penalty)`.

### 7.3 Foreground protection

Defaults: one background worker; lower process/thread priority; low I/O priority; pause on foreground compile; no work under battery/thermal pressure; bounded memory; cancel on source-generation change; never one child compiler per artifact; never delay exit for speculative work.

First source run: generate minimum baseline bytecode synchronously, persist immediately, execute; leave optimized SMF/native to the daemon. On a warm hit, do not start a daemon solely to speculate.

### 7.4 Canonical publication transaction

`private temp output → hash while writing → embedded canonical manifest → verify → flush → atomic rename into CAS → publish ActionDigest → ResultManifest`. Failure/cancel leaves no ready action mapping.

### 7.5 Remove heuristic sidecars

Migrate `.srchash`/`.abi`/`.ifacehash` sidecars, exported-line heuristics, and the hard-coded stub-size check to the canonical embedded manifest (source digest, compiler identity, schema, target/options, dependency InterfaceDigests, macro root, AOP roots, export InterfaceDigest, artifact digest). Delete sidecars once authoritative.

### 7.6 Local/main trust unchanged

Background developer builds publish to L1/L2 only; read trusted remote-main; never publish remote-main mappings. Trusted CI main publishes signed promotion receipts. Trust belongs to the action mapping and provenance, not to duplicated content blobs.

---

## 8. Interpreter runtime optimization

### 8.1 Tier 0 — tree-walk semantic oracle

Retained for differential correctness, debugging, unsupported features, bootstrap recovery, experimentation. Do not micro-optimize beyond obvious regressions.

### 8.2 Tier 1 — register/slot bytecode baseline

```text
Current:  PUSH r1 / PUSH r2 / ADD_I64 / POP r3
Target:   ADD_I64 r3, r1, r2
```

Fixed 32-bit wordcode: `ABC opcode:8,A:8,B:8,C:8`; `ABx opcode:8,A:8,Bx:16`; `Ax opcode:8,Ax:24`; `WIDE` prefix for large functions. (Register-VM literature: ~46% fewer dispatched instructions at ~26% larger bytecode, 1.48× switch-dispatch speedup — benchmark, don't assume.)

Required Tier-1 changes: direct MIR-vreg→slot allocation with liveness reuse; contiguous register/local array per frame; bump-pointer frame stack + frame reuse; direct FunctionId/TypeId/ShapeId/SymbolId/SFFI indexes; tail-call opcode; no string-based function lookup; constants/strings in mapped read-only pools; validate bytecode once at load; execute mapped code slices (no Vec copy); debug maps in a cold section; generate decoder/encoder/disassembler/verifier/exec metadata from one opcode schema (Vmgen precedent).

### 8.3 Tier 1.5 — adaptive quickening

Immutable mapped bytecode + session-local quickened overlay:

```text
ADD_ANY → ADD_I64 | ADD_F64 | ADD_TEXT
LOAD_GLOBAL → LOAD_GLOBAL_SLOT
LOAD_FIELD → LOAD_FIELD_SHAPE_OFFSET
CALL → CALL_DIRECT | CALL_MONO | CALL_NATIVE
INDEX_GET → ARRAY_GET_I64 | DICT_GET_SYMBOL
JOIN_POINT → JP_INACTIVE | JP_ACTIVE_CHAIN
```

Guards: object shape generation, module/global namespace generation, function binding generation, aspect activation generation. On failure: specialized → adaptive → generic. (PEP 659 precedent: biggest wins around attribute access, globals, calls.)

### 8.4 Superinstructions

Profile-derived fused opcodes (e.g. `LOAD_SLOT+LOAD_CONST+ADD_I64+STORE_SLOT`, `COMPARE_I64+JMP_IF_NOT`, `LOAD_FIELD_SHAPE+CALL_DIRECT`, `ITER_RANGE_I64+LOOP_BRANCH`), all generated from the instruction schema with handlers and tests.

### 8.5 Tier 2 — low-latency native code

Decision gate: immediate lane = Cranelift at lowest-latency setting for hot functions (background). Research lane = copy-and-patch stencils for common bytecode ops (CPython experimental JIT precedent). Adopt copy-and-patch only if it beats low-opt Cranelift on compile latency, break-even invocation count, code speed, code size, debug/unwind support, platform cost.

### 8.6 Tier 3 — optimized native

`profile → optimized MIR → Cranelift optimized → native code CAS → entry-slot patch`. Requirements: OSR only after ordinary tiering works; deopt maps; W^X; function-level code cache; profile-class identity; native debug/unwind registration; invalidation via code/module/aspect generations.

### 8.7 Runtime allocation and data-layout work

Frame/temporary reuse; unboxed i64/f64/bool/nil in RuntimeValue; interned identifiers/symbols; compact shape tables; field offsets over name lookup; lazy ranges; string-concat builders; array/dict specialization by element/key family; hot/cold object-header split; barrier omission in verified no-GC ops; escape analysis + scalar replacement in the optimized tier.

---

## 9. Compiler speed beyond shared caching

### 9.1 Source discovery and filesystem state

Replace repeated multi-file snapshots with native watchers (Linux inotify, macOS FSEvents/kqueue, Windows ReadDirectoryChangesW, SimpleOS VFS generations, bounded-polling fallback). Track directory generations and exact ordered resolution witnesses; never rescan the whole tree per request.

### 9.2 Incremental lexer/parser

Source chunks → token chunk hashes → immutable green syntax tree → red contextual view. On edit: retokenize affected chunks + boundary context; reparse smallest enclosing recoverable region; preserve stable declaration identities; Merkle module roots. Clean builds: parallel parse + transient builders then freeze.

### 9.3 Module summaries and lazy frontend loading

`ModuleSummary`: exported symbols, type/layout contracts, effects/capabilities, CTFE-visible constants, macro contracts, public pointcut/aspect surfaces, dependency interface roots. Downstream consumes summaries, not full AST/HIR (ThinLTO pattern).

### 9.4 Semantic red/green query system

Queries: `source_text, parse, module_summary, resolve_name, type_of, const_eval, macro_expand, aop_candidates, aop_selection, lower_hir, lower_mir, analysis, codegen, link`. Each record: stable QueryKey, dependency keys, output fingerprint, result artifact, diagnostics fingerprint. Red/green propagation; stable names from semantic anchors (Nominal Adapton), never line numbers or transient indexes.

### 9.5 Macro and CTFE dependency read sets

Action key includes: qualified definition identity, definition digest, invocation tokens, hygiene context, imported interfaces, declared env vars, filesystem inputs, compiler/plugin versions, AOP-visible metadata. Dynamic read-set recording where static declaration is insufficient; undeclared nondeterministic inputs → workspace-only, non-promotable.

### 9.6 AOP incremental dependencies

`pointcut contract → candidate partitions`, `candidate target → selected advice`, `target → weave plan`, `advice body → implementation artifact`. Body change: rebind only. Contract change: re-evaluate relevant partitions. Broad unpublicized root: conservative invalidation.

### 9.7 MIR analysis and pass manager

Lazy analysis computation, result caching, `PreservedAnalyses` declarations, function/SCC/module scopes, precise invalidation (LLVM NPM pattern). Function-level reuse first; block/region reuse only for measured expensive dataflow after stable block identities exist.

### 9.8 Parallel scheduler

Dependency-aware work stealing: ready deques, single-flight per QueryKey, SCC-aware ordering, memory/I/O budgets, foreground priority, deterministic publication. One daemon with threads; isolated worker processes only for crash containment/sandboxing/backend isolation.

### 9.9 Backend and linking

Function-level object caching; parallel function codegen; compact cross-module summary index; ThinLTO-style parallel release backend; cache post-import optimized products; lld/mold; avoid relinking unchanged dynamic components; PGO on compiler/runtime; BOLT post-link layout after profiles stabilize; hot/cold page partitioning.

### 9.10 Build-system separation of concerns

Keep independent: dependency discovery, query evaluation, scheduling, artifact storage, trust/admission, GC, remote transport, diagnostics (Build Systems à la Carte).

---

## 10. Hashes, Bloom filters, and indexes

| Purpose | Hash |
|---|---|
| Persistent correctness and CAS | SHA-256 |
| Stable query/result fingerprint | Fast stable 128-bit fingerprint |
| Process-local tables | Fast 64-bit hash with equality check |

Bloom filters are negative accelerators only (NO = definitely absent; MAYBE = exact lookup). Uses: module exported-symbol filter, macro-name filter, AOP candidate-partition filter, reverse-index shard filter, remote CAS shard membership. Blocked/cache-line-local for large sets; sorted arrays/bitsets for small sets. Never proof of validity, applicability, or satisfaction.

---

## 11. Benchmark and observability program

### 11.1 Required lanes

**Startup:** no-op/help; hello no-cache / warm bytecode / warm SMF / native; 1 and 10 stdlib imports; no aspects; lazy aspect first+second activation; stale source; stale dependency interface; daemon absent/present; remote-main hit.

**Runtime:** recursion, int/float loops, branches, strings, arrays/dicts, struct fields, mono/poly calls, closures, async/coroutines, green scheduling, fs, net, HTTP server, AOP disabled/active.

**Compiler:** clean full; warm no-op; function-body edit; exported-signature edit; macro body/contract edit; advice-body edit; pointcut edit; common-module edit; link-only edit.

### 11.2 Measurement protocol

Pin Bun 1.3.14 and Python 3.14.6; run Python default and JIT lanes separately. ≥50 startup samples (100 for release). Report p50/p95/p99/mean/σ/CI. Separate cold-FS, warm-FS, in-process warmup. Pin CPU affinity, record governor/turbo. Record cycles, instructions, branch/cache misses, page faults, RSS, mapped bytes, files opened, bytes read. Identical workload semantics; store binary hashes and command lines; reject semantic mismatches. Keep the Docker lane; add a native host lane for realistic startup.

### 11.3 Startup phase trace

Optional per-launch: `process.entry, command.decode, launch_metadata, cache_index_lookup, artifact_verify, artifact_map, runtime_generation, imports, aspect_catalog, first_user_instruction, first_output, exit`.

Release gate for a no-aspect hello:

```text
aspect payload maps = 0
aspect pack opens   = 0
pointcut parses     = 0
background compilers = 0
daemon IPC on warm hit = 0
```

---

## 12. Parallel-agent development plan

All agents use isolated git worktrees. Shared schemas land before fan-out. No whole-stale-tree commits; no cross-agent file edits.

### Wave F — contracts, benchmarks, semantic oracle

| Agent | Ownership | Deliverable |
|---|---|---|
| F0 Performance architecture/schema owner | cache/runtime protocol schemas, generated identity types | Freeze RuntimeImageManifest, bytecode v2 schema, AspectCatalog, JoinPointPlan, WarmRequest, DaemonCompatibilityId, action-key fields |
| F1 Benchmark owner | `scripts/check/check-cross-language-perf.shs`, `test/05_perf/` | Multi-run Bun/Python/Simple matrix; p50/p95/p99; perf counters; version pinning |
| F2 Differential semantic oracle | new engine-equivalence tests only | Tree-walk vs bytecode vs SMF vs native equivalence corpus + fuzzing |
| F3 Startup observability owner | launch tracing and evidence schema | Phase timing, opened-file/mapped-byte evidence, no-aspect proof |
| F4 Formal model owner | Lean cache/runtime protocol models | Identity coverage, immutable/runtime separation, atomic publish/activation models |

**Gate F:** one canonical schema; golden vectors for Simple/Rust/Lean; baseline reproducible; oracle runs before engine changes; no behavioral optimization enabled yet.

### Wave S — startup, shared images, daemon, background artifacts

| Agent | Ownership | Deliverable |
|---|---|---|
| S1 Minimal launch dispatcher | `src/app/startup/`, root command dispatch | Command + launch metadata before logging/dynSMF; no-op/help fast path |
| S2 Frozen image and mmap | runtime-image serializer/reader, platform mapping adapters | Pointer-free read-only mapped SMF image on Linux/macOS/Windows |
| S3 Cache tier integration | `cas_store.spl`, tier router/action indexes | Exact L1/L2/L3 lookup, direct mmap, conflict detection, strict verification |
| S4 Compiler daemon | daemon SDK, compiler-service entry | Self-launch, compatibility socket, multi-workspace state, single-flight queries |
| S5 Background SMF service | `dynsmf_autoload.spl`, `dynsmf_session.spl`, warm scheduler | Remove shell spawning; direct compiler API; priorities, cancellation, CAS publication |
| S6 Filesystem watcher | watcher backends, directory-generation store | Native event adapters, bounded polling fallback, no full-tree steady-state scan |
| S7 Startup integration tests | startup system tests only | No-op, hit/miss, daemon absent/present, background failure, next-run hit |

**Gate S:** `--help` loads no dynSMF; no default aspect/renderer autoload; warm launch without daemon IPC; background failure cannot affect current execution; two processes map the same immutable image without deserialization; canonical manifest replaces sidecars for the first artifact kind.

### Wave V — production bytecode baseline

**V0 (serial):** freeze wordcode encoding, opcode families, register limits/wide form, frame ABI, constant layout, call ABI, SFFI ABI, exception/result semantics, debug mapping, fallback policy.

| Agent | Ownership | Deliverable |
|---|---|---|
| V1 MIR-to-bytecode compiler | `compiler/src/codegen/bytecode/` | Full supported MIR coverage, slot allocation, three-address instructions |
| V2 Bytecode dispatch | runtime decode/dispatch | Mapped code execution, generated decode, trusted fast loop |
| V3 Frames, calls, locals, SFFI | frame/call modules | Reusable contiguous frames, direct + tail calls, native function table |
| V4 Values and collections | bytecode value fast paths | Shape/field offsets, array/dict specialization hooks, range iteration |
| V5 SMF bytecode packaging | SMF bytecode sections + loader | Direct mapped code/constants/functions; no Vec copy |
| V6 Driver integration | execution-engine selection | `simple run` defaults to bytecode with explicit tree-walk fallback |
| V7 Bytecode verification | tests/fuzzing only | Malformed bytecode, bounds, unsupported-op fallback, engine equivalence |

**Gate V:** required corpus covered or fallbacks recorded; tree-walk/bytecode agreement; bytecode default; warm startup improved; geomean beats tree-walk gate; no mutable state in shared image.

### Wave A — precise AOP and aspect-pack lazy activation

| Agent | Ownership | Deliverable |
|---|---|---|
| A1 Pointcut IR + public contracts | frontend/HIR AOP parsing/normalization | Typed normalized selectors, `pub pointcut` identity, read sets |
| A2 Candidate and reverse indexes | semantic AOP index | MDSOC partitions, pointcut↔candidate and target↔selection indexes |
| A3 Per-target join-point plans | MIR/HIR weave planning | Stable JoinPointPlan with direct FunctionIds and sorted chains |
| A4 Aspect Catalog/pack emitter | SMF writer, pack layout | Tiny uncompressed catalog, independent hashed chunks |
| A5 Runtime aspect loader | dynload runtime | Single-flight loading, dependency verification, atomic generation publication |
| A6 Bytecode/native patchpoints | execution lowering | Inactive slot, active chain, explicit facet acquisition, native fallback slot |
| A7 AOP cache groups/formal model | cache identities, Lean model | Contract/candidate/selection/weave/implementation separation |
| A8 Adversarial AOP tests | tests only | Concurrent activation, failure, body-only update, selector update, unload safety |

**Gate A:** no runtime pointcut-string parsing in the optimized engine; zero aspect payloads at no-aspect startup; static structural aspects cannot activate late; body-only changes skip reselection; pointcut changes invalidate all-and-only affected partitions; atomic activation; explicit facets add no unrelated instruction.

### Wave Q — semantic compiler and memory architecture

| Agent | Ownership | Deliverable |
|---|---|---|
| Q1 Query engine | query store/evaluator | Demand-driven red/green graph, persisted fingerprints, strict shadow mode |
| Q2 Incremental parser/frozen AST | frontend parser/image | Token chunks, immutable syntax nodes, edit-aware reparse, mapped frontend image |
| Q3 Module summaries + resolution | module/interface layers | Compact summaries, resolution witnesses, SCC interface roots |
| Q4 Macro and CTFE queries | macro/compile-time engine | Qualified identities, read sets, hygiene-safe templates, declared env inputs |
| Q5 Persistent maps + interning | compiler data infrastructure | Frozen flat base, persistent overlay, transient builder, stable IDs |
| Q6 MIR analysis manager | MIR optimizer framework | Cached analyses, preserved-analysis sets, worklist/lattice framework |
| Q7 Parallel scheduler | query scheduler | Work stealing, memory budgets, SCC ordering, single-flight |
| Q8 Backend summaries/codegen/link | backend + linker | Function cache, parallel codegen, ThinLTO-like index, lld/mold |
| Q9 Query correctness tests | tests only | Clean/incremental equality, edit matrices, nondeterminism + stale-query injection |

**Gate Q:** clean/incremental byte-identical where deterministic; function-body edit does not re-run unrelated codegen; unchanged public interface stops invalidation; macro/AOP follow explicit read sets; zero shadow-mode divergence; no filename-sanitized cache key authoritative.

### Wave J — adaptive bytecode and native tiers

| Agent | Ownership | Deliverable |
|---|---|---|
| J1 Quickening framework | adaptive opcode engine | Counters, specialization, local deoptimization |
| J2 Inline caches + generations | shape/global/call caches | Mono/poly caches with module/aspect generation guards |
| J3 Superinstruction generator | opcode generation tooling | Profile-derived fused opcodes + generated handlers/tests |
| J4 Low-latency JIT experiment | isolated prototype | Cranelift-low-opt vs copy-and-patch on latency/break-even |
| J5 Cranelift optimized tier | native backend/JIT integration | Hot function compilation, entry patching, native code CAS |
| J6 Profiling + tier policy | runtime profiler | Hotness, cost-aware thresholds, background queue, speculation controls |
| J7 Deopt/debug/W^X | runtime safety tooling | Deopt maps, stack maps, unwind registration, executable-memory policy |
| J8 JIT/adaptive tests | tests only | Guard failures, invalidation, OSR later, debugger/profiler evidence |

**Gate J:** cold code pays no JIT cost; quickening never changes semantics; every specialization has tested deopt; native compile only after break-even; W^X/code-signing obeyed; differential tests pass.

### Wave R — release tuning and certification

| Agent | Ownership | Deliverable |
|---|---|---|
| R1 PGO + layout | release build pipeline | PGO, cold-code separation, BOLT where supported |
| R2 Linux certification | Linux profiles | x86-64 + AArch64 startup/runtime/compiler report |
| R3 macOS/Windows certification | platform profiles | file-mapping, daemon IPC, code-signing, patchpoint parity |
| R4 SimpleOS certification | SimpleOS/QEMU/board | frozen-image loading, cache, background scheduling, no host-only assumptions |
| R5 Cache security + GC | provenance, quota, leases | poisoning tests, conflict quarantine, disk-pressure recovery |
| R6 Final performance decision | report only | Bun/Python/Go/C comparison, release-readiness verdict |

**Gate R:** same-host cached startup beats pinned Bun and Python; bytecode broadly beats Python on the declared suite; adaptive/native tiers meet the Bun gate; foreground stable under warming; corruption → miss/quarantine, never false hit; cross-platform determinism.

---

## 13. Merge and coordination rules

```text
F0 → F1+F2+F3+F4 → S1–S7 + V0 → V1–V7 + Q1–Q9 → A1–A8 → J1–J8 → R1–R6
```

1. Every agent uses an isolated worktree.
2. F0 alone owns shared protocol schemas.
3. Integration files and export lists have one designated owner.
4. Test agents make no production fixes.
5. Every optimization PR includes before/after raw measurements and semantic-equivalence evidence.
6. A performance claim based on one run is rejected.
7. Every cache change supplies `cache explain` output for hit, miss, and invalidation.
8. Every negative test must first be observed failing against the injected bad state.
9. New engines remain feature-gated until their wave gate passes.
10. Strict/bootstrap/release modes keep full verification and clean recomputation.

Control flags:

```text
--engine=tree|bytecode|adaptive|jit|aot
--aspect-load=off|explicit|lazy|eager
--smf-warm=off|demand|idle|profile
--cache-strict  --cache-explain  --startup-trace  --query-trace
```

---

## 14. First integrated milestone

1. Multi-run same-host Bun/Python/Simple benchmark.
2. Move dynSMF initialization after command + LaunchMetadata resolution.
3. Optional libraries: eager autoload → metadata/import demand.
4. Remove startup shell compiler spawning.
5. One daemon-owned artifact warm queue.
6. Publish SMFs through canonical CAS manifests.
7. Wire MIR-to-bytecode and BytecodeVM into `simple run`.
8. Bytecode loading: copy → read-only mapped view.
9. Direct register arithmetic opcodes.
10. Per-function AOP advice plans.
11. No-aspect execution performs no runtime pointcut work.
12. Persist baseline bytecode immediately; optimized SMF in the daemon.
13. Startup phase tracing.
14. Strict tree-walk/bytecode differential verification in CI.

---

## 15. Priority order

**P0 — largest immediate return:** remove unconditional dynSMF startup work; stop eager loading of the seven optional libraries; replace shell background compilers with one daemon queue; integrate the existing bytecode compiler/VM; map bytecode/SMF without copying; canonical embedded SMF manifest + CAS publication; build-time JoinPointPlan, eliminate interpreter pointcut scans; establish trustworthy same-host benchmarks.

**P1 — major structural gains:** red/green semantic query engine; frozen module/interface/runtime images; incremental filesystem + parser state; persistent map overlays + transient builders; adaptive bytecode + inline caches; function-level MIR/object cache; parallel query/codegen scheduler; precise AOP reverse indexes.

**P2 — high-value later:** low-latency native tier; copy-and-patch if the prototype beats Cranelift; optimized Cranelift hot tier + OSR; ThinLTO-style release backend; PGO/BOLT layout; selected block/region analysis reuse; profile-guided aspect-pack clustering; Bloom filters after exact-path profiling demonstrates benefit.

---

## 16. Main risks and mitigations

| Risk | Mitigation |
|---|---|
| Frozen image too large, hurts startup | Minimal core image, lazy segments, no aspect payloads, profile-guided layout |
| Register bytecode increases file size | Compact 32-bit form, wide escape, slot reuse, measured tradeoff |
| Background compiler steals CPU/I/O | One low-priority worker, preemption, cancellation, budgets |
| Lazy aspect violates static type/layout | Strict classification; structural aspects build-time only |
| Runtime activation races | Single-flight loading + one atomic generation publication |
| Cache poisoning | Exact keys, verified manifests/blobs, trusted remote-main writers |
| Persistent map poor locality | Frozen flat base + small persistent overlay |
| Daemon serves stale compiler state | Compatibility ID incl. executable, source, schema, host ABI |
| JIT delays short programs | No JIT before measured hotness/break-even; background compile |
| JIT loses debug/profile quality | Deopt/stack maps, unwind registration, tree/bytecode fallback |
| Performance work changes semantics | Differential oracle across engines + strict shadow mode |
| "Faster than Bun" becomes gaming | Same-host versions, broad declared suite, p95/p99 + outlier gates |

---

## 17. Final recommendation

```text
remove startup work
    ↓ make bytecode the baseline
    ↓ make artifacts canonical and mmap-able
    ↓ load capabilities/aspects only on demand
    ↓ generate optimized SMF in one background service
    ↓ introduce semantic red/green compilation
    ↓ add quickening and inline caches
    ↓ add native hot tiers
```

- Largest immediate **startup** gain: eliminate unconditional dynSMF initialization, eager optional-library loading, startup shell compilation.
- Largest **interpreter** gain: replace the tree walker with the existing bytecode infrastructure as a compact direct register VM.
- Largest **incremental compiler** gain: demand-driven red/green query graph with stable declaration/function/AOP/macro identities.
- Largest **next-launch** gain: canonical, daemon-generated SMF/native artifact published atomically into the machine CAS.
- Largest **AOP** gain: move selector evaluation, advice discovery, ordering, and resolution out of the call path into cached per-function join-point plans.
