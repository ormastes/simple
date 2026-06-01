# Simple Optimization Architecture Roadmap

Lifecycle Profiling, HotSpot Optimization, Binary Optimization, and Algorithm Provider Framework

- **Status:** Proposal
- **Target:** https://github.com/ormastes/simple
- **Version:** 2.0
- **Date:** 2026-06-01

---

## 1. Goals

Simple should support optimization throughout the entire software lifecycle:

```
Source → Parser → HIR → MIR → SMF → Interpreter → JIT → Native → Runtime → Production Feedback → Next Build
```

Unlike traditional compilers that optimize only during compilation, Simple should continuously optimize using runtime feedback, persistent profiles, and version-aware migration.

### Primary Goals

1. Java HotSpot-like runtime optimization with tiered compilation.
2. Persistent SMF profile collection (`.sprof`).
3. Cross-version profile migration using MIR hash matching.
4. LLVM PGO + BOLT binary optimization.
5. Automatic CPU/SIMD/GPU/offload algorithm selection via provider framework.
6. Optimization traceability — fact-driven proof at every tier.
7. Safe deoptimization with interpreter fallback.
8. Long-term learning across releases.

### 1.1 Active SPipe Roadmap Control Plane

This roadmap is the live coordination document for the 2026-06-01 optimization push requested through `$sp_dev`: sync with GitHub often, optimize Simple across JS/WASM, GUI rendering, and interpreter mode, and keep progress visible here.

Current SPipe state: `.spipe/simple-optimization-architecture-roadmap-2026-06-01/state.md`.

#### Acceptance Gates

| Gate | Pass Evidence |
|------|---------------|
| Roadmap control | This file has dated progress, lane owners, deliverables, and current blockers. |
| Sync hygiene | `git status --short`, jj fetch/rebase evidence, file-count guard, and no push without explicit approval where release flow requires it. |
| JS/WASM | Focused JS, BrowserSession, WASM, WebGPU bridge, and generated `doc/06_spec` manuals pass or name release-blocking defects. |
| GUI rendering | Repeatable open/render/vector-font benchmark output with Simple and native-baseline fields, plus fallback evidence. |
| Interpreter speed | Focused interpreter hot-path checks, benchmark deltas, and no silent normalization of compiler/interpreter grammar workarounds. |
| Cross-lane regression | `bin/simple check`/`test` commands for touched compiler, lib, MCP/LSP, app, and system surfaces match the repo verify gates. |

#### Parallel Agent Plan

Run these lanes in parallel only when their file scopes are disjoint. Shared compiler/runtime edits require a lead integrator to serialize merges and rerun the cross-lane gates.

| Agent | Scope | Existing Evidence | Primary Deliverables | Metrics |
|-------|-------|-------------------|----------------------|---------|
| A: Sync/Integration | jj/git state, GitHub sync cadence, changelog handoff | `.codex/skills/sync/SKILL.md`, release rules in `AGENTS.md` | Keep main linear, fetch/rebase before major verification, record file-count guard results, prepare commit slices without bundling unrelated dirty files | zero unexpected file loss; no orphan commits; no unapproved push |
| B: JS/WASM Engine | Node-compatible JS, browser JS, WASM asset loading, WebGPU bridge | `.spipe/nodejs-js-wasm-hardening/state.md`, `test/feature/js/node_api_conformance_spec.spl`, `test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl`, `test/system/os/simpleos_ai_cli_js_node_port_spec.spl` | Harden positive and denial paths, optimize promise/native byte extraction, reduce redundant JS/WASM bridge work, regenerate manuals | scenario count stable or higher; deny paths explicit; bridge latency benchmark added before perf claims |
| C: GUI Rendering | Simple GUI 2D render, vector fonts, web/HTML-backed GUI render surfaces | `.spipe/simple-gui-2d-render-perf/state.md`, `scripts/check-gtk-gui-repeat-evidence.shs`, `doc/09_report/gtk_gui_size_speed_baseline_2026-05-30.md`, `doc/08_tracking/bug/simple_web_layout_corpus_perf_2026-05-31.md` | Broaden primitive fast paths for fill/copy/blit/text, capture fallback evidence, add render-corpus perf guard | open latency, frame latency, glyph throughput, non-empty deterministic output |
| D: Interpreter Runtime | Rust interpreter hot paths, Simple MIR interpreter, tiered JIT facts | `.spipe/interpreter-perf-gaps/state.md`, `doc/08_tracking/bug/interpreter_1460x_c_perf_gap_2026-05-18.md`, `src/compiler/95.interp/`, `src/compiler_rust/compiler/src/interpreter/` | Land low-risk hot-path fixes, evaluate bytecode VM connection path, keep safe deopt facts intact | before/after wall time; alloc count when available; no semantic divergence |
| E: Compiler/MIR/JIT | MIR optimization passes, hotspot planning, `.sprof`, PGO/BOLT | `src/compiler/60.mir_opt/`, `src/compiler/95.interp/execution/tiered_jit.spl`, `doc/07_guide/compiler_optimization_plugin.md` | Define `.sprof` schema slice, fact-gated profile migration, LLVM tier-2 cost evidence, pass ordering invariants | compile time, selected tier, deopt count, hot function speedup |
| F: Verification/Docs | SPipe specs, generated manuals, bug/feature tracking, perf reports | `doc/06_spec`, `doc/03_plan/sys_test`, `doc/08_tracking`, verify skill gates | Regenerate manuals for changed specs, reject stub tests, maintain traceability from requirements to implementation | `find doc/06_spec -name '*_spec.spl' | wc -l` remains `0`; no `pass_todo` evidence |

#### Lane Handoffs

1. Agents B, C, D, and E write benchmark or test evidence before claiming speedups.
2. Agent F reviews every new spec for real assertions and regenerates the mirrored `doc/06_spec/...md` manual.
3. Agent A syncs after a coherent verified slice, not after every speculative edit; "often" means after stable evidence, fetch/rebase, and file-count guard.
4. Any lane that touches `src/compiler/**`, `src/lib/**`, MCP, LSP, package, or release paths inherits the additional verify commands from `AGENTS.md`.
5. If a short grammar form, compact expression, or interpreter workaround fails, the owning agent fixes it or records a concrete bug before moving on.

#### Immediate Work Queue

| Priority | Lane | Task | Exit Criteria |
|----------|------|------|---------------|
| P0 | A/F | Establish roadmap state and progress log | `.spipe/.../state.md` exists and this section is updated. |
| P0 | B | Finish current dirty JS/WASM hardening slice without touching unrelated files | Existing modified JS/WASM files are tested and manuals regenerated. |
| P0 | C | Convert `simple-gui-2d-render-perf` remaining work into a primitive-level implementation plan | AC-3 and AC-6 blockers have exact files/tests or tracked bugs. |
| P1 | D | Re-audit interpreter hot-path quick wins after the May 20 state | Candidate fixes have before/after benchmark commands and semantic tests. |
| P1 | E | Split persistent profile work into schema, writer, loader, and migration steps | Requirements/design artifacts exist before implementation. |
| P1 | F | Build a cross-lane smoke command list | Commands cover JS/WASM, GUI, interpreter, compiler/lib checks, and doc layout. |

#### Progress Log

| Date | Lane | Progress | Evidence |
|------|------|----------|----------|
| 2026-06-01 | A/F | Created SPipe control state and added parallel-agent execution plan to this roadmap. | `.spipe/simple-optimization-architecture-roadmap-2026-06-01/state.md`, this section. |
| 2026-06-01 | B | Reused active JS/WASM hardening state rather than replacing it; current dirty files belong to `simpleos_ai_cli_js_node_port_spec` and `src/os/ai_cli_js_node_contract.spl`. | `.spipe/nodejs-js-wasm-hardening/state.md`, `git status --short`. |
| 2026-06-01 | B/F | Verified the current JS/WASM OS contract slice in interpreter mode. | PASS `SIMPLE_LIB=src bin/simple check src/os/ai_cli_js_node_contract.spl`; PASS `SIMPLE_LIB=src bin/simple test test/system/os/simpleos_ai_cli_js_node_port_spec.spl --mode=interpreter --clean` (23 scenarios). |
| 2026-06-01 | B/F | Fixed nested host-promise assimilation for fetched WASM instantiation callbacks returning `Promise.resolve(navigator.gpu.requestAdapter())`, so downstream callbacks receive the WebGPU adapter object. | PASS `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/js/engine/interpreter_async.spl src/lib/nogc_sync_mut/js/engine/interpreter_async.spl src/lib/nogc_async_mut/js/engine/interpreter_async.spl`; PASS `SIMPLE_LIB=src bin/simple test test/system/app/browser/feature/webgpu_js_wasm_simple_spec.spl --mode=interpreter --clean` (106 scenarios); regenerated `doc/06_spec/system/app/browser/feature/webgpu_js_wasm_simple_spec.md`. |
| 2026-06-01 | B/F | Re-verified Node-compatible JS after in-flight credential-env work at the previous green baseline, before restoring public credential grant API coverage. | PASS `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/runtime.spl test/feature/js/node_api_conformance_spec.spl`; PASS `SIMPLE_LIB=src bin/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean` (142 scenarios). |
| 2026-06-01 | B/F | Restored Node-compatible credential env grant coverage through the public `JsRuntime.grant_node_credential(...)` API; the conformance helper no longer mutates interpreter internals directly. | PASS `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/runtime.spl test/feature/js/node_api_conformance_spec.spl`; PASS `SIMPLE_LIB=src bin/simple test test/feature/js/node_api_conformance_spec.spl --mode=interpreter --clean` (143 scenarios); regenerated `doc/06_spec/feature/js/node_api_conformance_spec.md`. |
| 2026-06-01 | B/F | Wired the native Node-compatible `child_process.spawn` boundary to generic per-command process grant markers, so non-Node commands like `git` are allowed only when explicitly granted. | PASS `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter_native.spl src/lib/nogc_sync_mut/js/engine/runtime.spl test/feature/js/node_api_conformance_spec.spl`; PASS Node API conformance (149); PASS WebGPU JS/WASM Simple (106); PASS interpreter perf (10); PASS GTK GUI repeat evidence with vector checksum 212444 deterministic true. |
| 2026-06-01 | B/F | Added a single-entry last-hit cache to Node-compatible `require()` so repeated canonical module requests bypass the reverse cache-array scan while keeping `path` and `node:path` aliases on the same module object. | PASS `SIMPLE_LIB=src bin/simple check src/lib/nogc_sync_mut/js/engine/interpreter.spl src/lib/nogc_sync_mut/js/engine/interpreter_native.spl test/feature/js/node_api_conformance_spec.spl`; PASS Node API conformance (150); regenerated `doc/06_spec/feature/js/node_api_conformance_spec.md`; PASS WebGPU JS/WASM Simple (106); PASS interpreter perf (10); PASS GTK GUI repeat evidence with Simple open 224 us, GTK open 75025 us, vector checksum 212444 deterministic true. |
| 2026-06-01 | B/F | Routed JS `String.startsWith`/`String.endsWith` through runtime text primitives across sync/async JS families, removing duplicated manual per-character loops. | PASS string-method family check; PASS Node API conformance (151); regenerated `doc/06_spec/feature/js/node_api_conformance_spec.md`; PASS WebGPU JS/WASM Simple (106); PASS interpreter perf (10); PASS GTK GUI repeat evidence with Simple open 210 us, GTK open 77889 us, Simple frame 1 us, GTK frame 27 us, vector checksum 212444 deterministic true; ES5 conformance remains a pre-existing 54/54 harness failure returning `nil`. |
| 2026-06-01 | C | Identified GUI perf state with remaining primitive fast-path and fallback-evidence work. | `.spipe/simple-gui-2d-render-perf/state.md`. |
| 2026-06-01 | C/F | Verified current GUI repeat evidence: Simple open 203 us vs GTK open 68904 us, Simple frame 1 us vs GTK frame 26 us, Simple text 11 us vs GTK text 26 us, vector text checksum 212444 deterministic true. | PASS `scripts/check-gtk-gui-repeat-evidence.shs`; report `build/gtk_gui_repeat_evidence/report.md`. |
| 2026-06-01 | C/F | Advanced the browser GUI rendering lane: text painter now wraps famous-site corpus text using pixel-width glyph estimates instead of character columns, and the existing scanline y-coordinate probe is restored. | PASS `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl test/unit/browser_engine/text_painter_spec.spl`; PASS `SIMPLE_LIB=src bin/simple test test/unit/browser_engine/text_painter_spec.spl --mode=interpreter --clean --force-rebuild` (2 scenarios); generated `doc/06_spec/unit/browser_engine/text_painter_spec.md` as a stub-style manual. |
| 2026-06-01 | C/F | Added explicit vector-font unavailable fallback evidence to the GTK repeat gate without changing the broader famous-site corpus production baseline. | PASS `GTK_EVIDENCE_FALLBACK_PROBE_ONLY=1 GTK_EVIDENCE_FORCE_VECTOR_FONT_UNAVAILABLE=1 ... sh scripts/check-gtk-gui-size-speed-baseline.shs`; PASS `scripts/check-gtk-gui-repeat-evidence.shs` with fallback probe `forced-vector-font-unavailable`, Simple open 203 us, GTK open 68904 us, vector checksum 212444; tracked report `doc/09_report/gtk_gui_repeat_fallback_evidence_2026-06-01.md`. |
| 2026-06-01 | C/F | Optimized the GUI static-shell plan cache hot path to reuse retained decoded SWBC metadata and prepared primitive command lists on memory hits. | PASS `SIMPLE_LIB=src bin/simple check src/app/ui.web/render_cache.spl test/system/app/ui/feature/html_css_binary_caching_spec.spl`; PASS `SIMPLE_LIB=src bin/simple test test/system/app/ui/feature/html_css_binary_caching_spec.spl --mode=interpreter --clean` (10); PASS GTK GUI repeat evidence with Simple open 222 us, GTK open 70284 us, vector checksum 212444; PASS WebGPU JS/WASM Simple (106); PASS interpreter perf (10). |
| 2026-06-01 | C/F | Hardened bounded JPEG XL color metadata routing so non-default structured color headers fail closed instead of being accepted as default sRGB; explicit available/required bit counts prevent absent padded bits from changing default fixtures. | PASS `SIMPLE_LIB=src bin/simple check src/lib/common/image/image_info.spl examples/browser/test/paint/image_decode_spec.spl`; PASS image decode spec (75); regenerated `doc/06_spec/paint/image_decode_spec.md`; PASS Node API conformance (150); PASS WebGPU JS/WASM Simple (106); PASS interpreter perf (10); PASS GTK GUI repeat evidence with Simple open 220 us, GTK open 72130 us, vector checksum 212444 deterministic true. |
| 2026-06-01 | C/F | Tightened the focused Google corpus Arial width calibration so `Google search` reports width 105 against Chrome's 104.0625 canvas metric, moving the 122px first wrapped-line miss from `site_0_google` to `site_2_facebook`. | PASS text painter check; PASS text painter spec (3); PASS famous-site corpus spec (37); PASS renderer smoke (9); regenerated text-painter and famous-site manuals; PASS Node API conformance (151); PASS WebGPU JS/WASM Simple (106); PASS interpreter perf (10); PASS GTK GUI repeat evidence with Simple open 243 us, GTK open 77948 us, Simple frame 1 us, GTK frame 28 us, vector checksum 212444 deterministic true. |
| 2026-06-01 | D | Identified closed interpreter perf state plus remaining architectural candidates: string allocation, SeqCst extern checks, block-scope TLS, watchdog ordering, and bytecode VM connection. | `.spipe/interpreter-perf-gaps/state.md`. |
| 2026-06-01 | D/F | Verified current interpreter perf and tiered hotspot smoke coverage before further optimization work. | PASS `SIMPLE_LIB=src bin/simple test test/unit/app/interpreter/perf_spec.spl --mode=interpreter --clean` (10 scenarios); PASS `SIMPLE_LIB=src bin/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean` (51 scenarios). |
| 2026-06-01 | D/F | Removed `SeqCst` fences from the `DIAGRAM_ENABLED` trace-recording flag fast path in the Rust runtime; recorded data remains lock protected. | PASS `cargo check -p simple-runtime --manifest-path src/compiler_rust/Cargo.toml`; PASS `cargo test -p simple-runtime diagram_sffi --manifest-path src/compiler_rust/Cargo.toml` (3 tests); PASS interpreter perf and tiered JIT smoke specs. |
| 2026-06-01 | D/F | Replaced the interpreter watchdog timeout flag `SeqCst` operations with `Release` stores and an `Acquire` read, preserving inter-thread visibility without a global total-order fence. | PASS `cargo check -p simple-compiler -p simple-common --manifest-path src/compiler_rust/Cargo.toml`; PASS `cargo test -p simple-common timeout --manifest-path src/compiler_rust/Cargo.toml`; PASS `cargo test -p simple-compiler watchdog --manifest-path src/compiler_rust/Cargo.toml -- --test-threads=1`; PASS interpreter perf (10); PASS tiered JIT hotspot (51). |
| 2026-06-01 | D/F | Replaced formatter-based interpreter string concatenation with capacity-sized `String` growth in the Rust interpreter binary `+` path. | PASS `cargo check -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml`; PASS `SIMPLE_LIB=src bin/simple test test/system/features/string_system_spec.spl --mode=interpreter --clean` (33); PASS interpreter perf (10); PASS tiered JIT hotspot (51). |
| 2026-06-01 | D/F | Removed boxed iterator allocation from merged `CowEnv` environment scans by routing `iter()`, `keys()`, and `values()` through the existing concrete `CowEnvIter`. | PASS `cargo check -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml`; PASS interpreter perf (10); PASS tiered JIT hotspot (51); PASS string system (33); PASS Node API conformance (145); PASS WebGPU JS/WASM Simple (106); PASS GTK GUI repeat evidence. |
| 2026-06-01 | A | Recorded non-mutating sync-safety state before any future sync: tracked file count is 77108, `jj status` has uncommitted working-copy changes on top of `main` parent `test: tighten ai cli credential grant boundary`; no fetch/rebase/push attempted in this slice. | `git ls-files | wc -l`, `jj status`, `jj log -r 'main@origin | @ | @-' --no-graph --limit 8`. |
| 2026-06-01 | A/F | Updated sync guard after removing the local credential debug scratch file; current tracked file count is 77107, whitespace checks pass, generated spec layout is clean, and the broad multi-lane worktree remains uncommitted. | PASS `git diff --check`; PASS `find doc/06_spec -name '*_spec.spl' \| wc -l` = 0; `jj status`. |
| 2026-06-01 | F | Re-ran the full focused checkpoint for the current optimization slice across SPipe routing, JS/WASM, GUI text rendering, interpreter perf, Rust runtime, and GUI repeat evidence. | PASS `sh scripts/install-spipe-dev-command.shs --check`; PASS Node API conformance (143); PASS WebGPU JS/WASM (106); PASS text painter (2); PASS interpreter perf (10); PASS tiered JIT hotspot (51); PASS `cargo check`; PASS `cargo test -p simple-runtime diagram_sffi` (3); PASS GUI repeat evidence (Simple open 203 us, GTK open 68904 us, vector checksum 212444); PASS `git diff --check`; PASS `doc/06_spec` stray `.spl` count 0. |
| 2026-06-01 | A/F | Synced the verified optimization checkpoint to GitHub `main` with jj, resolved the remote restart-plan overlap, and confirmed the post-push repository is clean. | Pushed `d826cf69e0f4 perf: advance simple optimization checkpoint`; post-push `jj git fetch` confirmed `main`/`main@origin`; PASS `git diff --check`; PASS `find doc/06_spec -name '*_spec.spl' \| wc -l` = 0; tracked file count 77107. |

---

## 2. MDSOC+ Optimization Architecture

### 2.1 Architecture Principle

The optimization subsystem follows the MDSOC+ pattern established project-wide (adopted 2026-04-17):

| Layer | Pattern | Optimization Role |
|---|---|---|
| **Kernel (ring 0)** | MDSOC only | No optimization runtime; static analysis only |
| **Compiler layers** | MDSOC capsule per layer | Layer 60 (MIR Opt), Layer 85 (MDSOC feature/optimization) |
| **Userland services** | MDSOC outer + ECS inner | Profile database entities, provider registries as ECS |
| **Apps** | MDSOC outer + ECS inner | Per-app optimization providers, session-local profiles |

### 2.2 Compiler Layer Mapping

The optimization pipeline maps onto the existing numbered compiler layers:

| Layer | Name | Optimization Responsibility |
|---|---|---|
| 00 | Common | DI slots for optimization config |
| 10 | Frontend | Syntax sugar optimization (desugar plugin kind) |
| 20 | HIR | Type-aware simplification (hir plugin kind) |
| 35 | Semantics | Lint: `mdsoc_plus_ecs_advisory.spl` for MDSOC+ conformance |
| 50 | MIR | MIR data, instructions, serialization |
| 55 | Borrow | Escape analysis facts for JIT (`escape.analyzed`, `escape.no_escape`) |
| 60 | MIR Opt | **Core optimization passes** — constant folding, DCE, CSE, GVN, inlining, loop opts, SIMD lowering, strength reduction, collection opt, target opt planning |
| 70 | Backend | Backend-specific passes (LLVM, Cranelift, WASM, CUDA, Vulkan), PGO instrumentation |
| 85 | MDSOC | Feature dimension: `feature/optimization/` — SIMD provider metadata, MirOptView entity view, ports |
| 90 | Tools | Perf tools: `profiler.spl`, `optimizer.spl`, API surface analysis |
| 95 | Interp | Interpreter execution, **tiered JIT manager** (`tiered_jit.spl`) |
| 99 | Loader | JIT context, JIT instantiator, module resolver |

### 2.3 MDSOC Feature Dimension for Optimization

The MDSOC layer (85) organizes optimization as a feature dimension:

```
src/compiler/85.mdsoc/feature/optimization/
├── __init__.spl
├── simd_provider.spl          # SIMD provider MDSOC metadata
└── app/
    ├── __init__.spl
    ├── optimize_input_port.spl  # Input port contract
    ├── optimize_output_port.spl # Output port contract
    └── ports.spl                # Port wiring

src/compiler/85.mdsoc/transform/feature/mir_to_optimizer/
├── __init__.spl
└── entity_view/
    ├── __init__.spl
    └── MirOptView.spl           # ECS entity view over MIR for optimization
```

This separation ensures optimization providers declare explicit port contracts and required facts, enabling the MDSOC checker to verify layer separation without importing backend types.

### 2.4 Optimization Plugin Contract

Established in `doc/07_guide/compiler_optimization_plugin.md`, the plugin system supports seven stages:

| Kind | Stage | Existing Source |
|------|-------|----------------|
| `syntax` | Frontend normalization | `src/compiler/10.frontend/` |
| `hir` | HIR simplification | `src/compiler/20.hir/` |
| `mir` | MIR optimization | `src/compiler/60.mir_opt/optimization_passes*.spl` |
| `pattern` | MIR pattern engine | `src/compiler/60.mir_opt/mir_opt/pattern_dispatch.spl` |
| `interpreter` | Interpreter runtime | `src/compiler/95.interp/` |
| `jit-hotspot` | JIT runtime planning | `src/compiler/95.interp/execution/tiered_jit.spl` |
| `backend-metadata` | Backend boundary | `src/compiler/70.backend/backend/optimization_passes.spl` |

Each plugin provides `OptimizationRuleProvider` metadata with:
- `required_facts`: preconditions that must be proven before the pass runs
- `produced_facts`: postconditions the pass guarantees
- `purity`: whether the pass is side-effect-free
- Capability gating (e.g., `["x86.aes", "x86.pclmul"]`)

---

## 3. Runtime HotSpot Optimization (Tiered JIT)

### 3.1 Current Implementation

The tiered JIT is implemented in pure Simple at `src/compiler/95.interp/execution/tiered_jit.spl` with the following tiers:

```
Tier 0: Interpreted (default)
  ↓ call_count >= tier1_threshold
Tier 1: Cranelift-compiled (fast compile, moderate runtime perf)
  ↓ call_count >= tier2_threshold
Tier 2: LLVM-compiled (slow compile, fully optimized runtime)
```

#### Core Types (existing)

```
enum JitTier:
    Interpreted    # Tier 0
    Fast           # Tier 1 (Cranelift)
    Optimized      # Tier 2 (LLVM)

struct FunctionProfile:
    name: text
    call_count: i64
    tier: JitTier
    compile_time_ms: f64
    source: text
    typed_mir: bool
    safe_deopt: bool
    hotspot_specialized_source: text
    hotspot_semantic_proof: bool
    var_facts: JitVarOptimizationFacts

struct TieredJitConfig:
    tier1_threshold: i64
    tier2_threshold: i64
```

### 3.2 Hotspot Plan Pipeline

The hotspot planning system is fact-driven (not heuristic). A function becomes eligible for optimization only when explicit proof facts are available:

```
Profile Collection
  ↓ profile.hot_count (call_count >= threshold)
Fact Gathering
  ↓ typed_mir (MIR is type-annotated)
  ↓ safe_deopt (deoptimization is safe)
Plan Construction
  ↓ JitHotspotPlan { eligible, facts, reason }
Provider Selection
  ↓ JitHotspotSpecializationProvider { semantic_proof }
Compile Decision
  ↓ JitHotspotCompileDecision { compile_source, provider_used }
Backend Choice
  ↓ JitHotspotRebuildChoice { selected_backend, cost_class }
```

#### Var Reassignment Optimization Facts

The var-reassignment hotspot path requires additional proof:
- `ssa.var_transform` — SSA conversion for reassigned variables
- `escape.analyzed` + `escape.no_escape` — stack/local assumptions verified
- `borrow.reassign_safe` — no outstanding borrows invalidated

Source: `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl` (SSA transform, phi planning, backend policy, provider factory), `var_reassign_analysis.spl` (raw analysis, JIT fact extraction).

### 3.3 Roadmap: Additional Tiers

| Tier | Status | Description |
|------|--------|-------------|
| Tier 0 (Interpreted) | **Implemented** | Fast startup, minimal memory, profile collection |
| Tier 1 (Cranelift) | **Implemented** | Baseline JIT via `rt_jit_*` externs (Rust bridge) |
| Tier 2 (LLVM) | **Planned** | Cost-gated (high compile cost), tier-2 threshold required |
| Tier 3 (Production) | **Roadmap** | Persistent profile + cross-version history → AOT-optimized SMF |

#### Tier 2 Cost Gating (existing policy)

LLVM rebuilds are explicitly cost-gated:
- Cranelift tier-1 rebuilds: medium cost, accepted immediately
- LLVM tier-2 rebuilds: high cost, deferred until tier-2 threshold AND LLVM backend available AND caller allows high compile cost
- `jit_hotspot_rebuild_choice` prefers LLVM only when all gates pass; falls back to Cranelift

### 3.4 Deoptimization

Optimized code assumptions may become invalid. The system supports safe deoptimization:

**Causes:**
- Module reload (hot code replacement)
- Library upgrade (ABI change)
- Hardware change (AVX512 → SSE4 fallback)
- Type feedback invalidation
- Profile corruption
- Borrow safety violation for var-reassignment optimizations

**Mechanism:**
- `jit_hotspot_plan_invalidate` marks a plan as invalidated
- `safe_deopt` fact must be proven before any optimization
- Missing `safe_deopt` rejects planning without dropping `hot_count` facts
- Fallback always preserves original (unoptimized) source path

---

## 4. MIR Optimization Passes

### 4.1 Current Passes (Layer 60)

Implemented in pure Simple at `src/compiler/60.mir_opt/`:

| Pass | File | Description |
|------|------|-------------|
| Constant Folding | `optimization_passes_part1.spl` | Evaluate constants at compile time |
| Copy Propagation | `optimization_passes_part1.spl` | Replace copies with originals |
| Dead Code Elimination | `optimization_passes_part1.spl` | Remove unreachable/unused code |
| Global Value Numbering | `optimization_passes_part2.spl` | Detect congruent expressions |
| Common Subexpression Elimination | `optimization_passes_part2.spl` | Reuse computed values |
| Inlining | `optimization_passes_part2.spl` | Inline small/hot functions |
| Loop Optimizations | `optimization_passes_part2.spl` | LICM, unswitching, unrolling |
| Outlining | `optimization_passes_part2.spl` | Extract cold paths to reduce code size |
| Strength Reduction | `optimization_passes_part1.spl` | `x * 2 → x << 1`, `% power_of_two → & mask` |
| Algebraic Simplification | `optimization_passes_part1.spl` | `x + 0 → x`, `x * 1 → x` |
| Peephole Optimization | `optimization_passes_part1.spl` | Local instruction combining |
| SIMD Lowering | `mir_opt/auto_vectorize_provider.spl` | Loop vectorization for contiguous data |
| Collection Optimization | `mir_opt/collection_opt_core.spl`, `collection_opt_patterns.spl` | Container-specific rewrites |
| Target Optimization | `mir_opt/target_opt_planner.spl` | Target-aware pass selection |
| SIMD Metadata | `mir_opt/simd_opt_metadata.spl` | SIMD target feature analysis |
| Pattern Dispatch | `mir_opt/pattern_dispatch.spl` | Idiom recognition engine |

### 4.2 Optimization Levels

Defined in `doc/07_guide/compiler_optimization_levels.md`:

| Level | Syntax | MIR | Native |
|-------|--------|-----|--------|
| `none` | — | — | `-O0` |
| `basic` | sugar desugar | const fold, DCE | `-O1` |
| `standard` | + normalize | + inline, CSE, GVN | `-O2` |
| `aggressive` | + all | + all passes | `-O3 -flto` |

### 4.3 Versioned Dynamic Optimizer Manifest

External plugins declare themselves via `.opt-manifest` files (design: `doc/05_design/optimizer_manifest_versioned_design.md`):

```
schema_version: 1
compiler_abi: "simple.opt.mir.v1"
name: "my-crypto-passes"
version: "0.3.1"
min_compiler_version: "0.9.0"
passes:
  - stable_name: "my_aes_fold"
    scope: "module"
    capability_requires: ["x86.aes", "x86.pclmul"]
    contract:
      inputs: ["typed_mir"]
      outputs: ["canonical_mir"]
      purity: "pure"
```

Registry types at `src/compiler/60.mir_opt/optimizer_manifest.spl`:
- `ManifestPassEntry`, `OptimizerManifest`, `ManifestError`
- `DynamicPassRegistry` — session-scoped, built-in passes always take precedence

---

## 5. Algorithm Provider Framework

### 5.1 Existing Provider Infrastructure

Simple already has provider selection at multiple levels:

#### Compiler-Level Providers

| Provider | Source | Selection |
|----------|--------|-----------|
| SIMD auto-vectorization | `src/compiler/60.mir_opt/mir_opt/auto_vectorize_provider.spl` | Target feature gating (`sse2`, `avx2`, `neon`) |
| MDSOC SIMD feature | `src/compiler/85.mdsoc/feature/optimization/simd_provider.spl` | MDSOC dimension metadata |
| Target opt planner | `src/compiler/60.mir_opt/mir_opt/target_opt_planner.spl` | Architecture-aware pass selection |

#### Runtime-Level Providers (stdlib)

| Provider | Source | Selection |
|----------|--------|-----------|
| BLAS | `src/lib/common/science_math/blas_provider.spl` | `BlasProvider` trait: Mock → CpuBlas → OpenBlas → cuBLAS |
| CUDA/cuBLAS | `src/lib/common/science_math/cuda_provider.spl` | `SIMPLE_BLAS_BACKEND` env var + waterfall probe |
| LAPACK | `src/lib/common/science_math/lapack_provider.spl` | Provider selection |
| GPU Graphics | `src/lib/gc_async_mut/gpu/session/optimization_provider.spl` | `GraphicsOptProvider` with per-target metadata |
| GPU Registry | `src/lib/gc_async_mut/gpu/session/optimization_registry.spl` | `GraphicsOptRegistry` — flat 4-slot registry |
| Rendering Opt | `src/lib/gc_async_mut/gpu/engine2d/rendering_opt_provider.spl` | Hit/miss/change counters per provider |
| SIMD variant | `src/lib/nogc_sync_mut/simd/variant_dispatch.spl` | ISA variant dispatch |

### 5.2 Provider Selection Pattern

The CUDA provider establishes the canonical selection pattern:

```
"auto" or "" → waterfall: CUDA if probe passes → CPU if probe passes → Mock

Provider hierarchy:
  Mock   — deterministic CPU stubs; always available
  Cpu    — OpenBLAS host backend; probe: openblas_available
  Cuda   — cuBLAS/cuSOLVER; probe: cuda_available AND device present
```

### 5.3 Graphics Optimization Provider Types

`GraphicsOptProvider` supports factory methods for:
- `shader_specialization(backend, arch)` — shader variant selection
- `pipeline_cache(backend, arch)` — PSO/pipeline cache
- `cpu_simd(arch, bits)` — CPU SIMD vectorization facts
- `cuda_kernel(arch)` — CUDA kernel specialization

Each provider stores: `provider_id`, `provider_kind`, `backend_kind`, `target_arch`, `target_bits`, `session_mode`, `policy_hash`, fact key/value pairs, and active/persistent flags.

### 5.4 Roadmap: Unified Algorithm Registry

Extend the existing provider pattern to a unified algorithm registry:

```
@algorithm("std.linalg.matmul")
fn matmul(...)

Providers:
  cpu.scalar     — always available
  cpu.simd       — probe: target_has_simd
  gpu.cuda       — probe: cuda_available
  gpu.vulkan     — probe: vulkan_available
  gpu.webgpu     — probe: webgpu_available
  gpu.metal      — probe: metal_available
  remote.cluster — probe: cluster_endpoint configured
```

Selection priority:
1. Manual override (`@use_provider("gpu.cuda")`)
2. Capability match (hardware probes)
3. Profile history (`.sprof` performance database)
4. Cost model (input shape → estimated time)
5. Fallback (always-available scalar)

### 5.5 Capability Detection

**CPU:** AVX2, AVX512, SSE2, NEON, SVE, RVV — already gated in `SIMDOptProvider.target_features`

**GPU:** CUDA, ROCm, Vulkan, WebGPU, Metal — session backends at `src/lib/nogc_sync_mut/gpu/engine2d/` (`cuda_session.spl`, `vulkan_session.spl`, `metal_session.spl`, `webgpu_session.spl`, `cpu_simd_session.spl`, `arm_riscv_session.spl`)

**Remote:** Cluster, Cloud, Distributed Runtime — future extension

### 5.6 Runtime Family Considerations

Each runtime family may provide different providers and cost models:

| Runtime | Provider Scope | Notes |
|---------|---------------|-------|
| Native | Full — CPU/SIMD/GPU/Remote | All backends available |
| Sandbox | CPU only | No device access |
| Browser (WASM) | WebGPU, CPU scalar | No CUDA/Vulkan |
| Embedded | CPU scalar, maybe SIMD | Memory constrained |
| Kernel | None | Static analysis only per MDSOC+ rules |

---

## 6. Persistent SMF Profile (`.sprof`)

### 6.1 New Files

```
module.smf         # Existing compiled module
module.sprof       # NEW: persistent profile database
```

### 6.2 Purpose

Store execution statistics, optimization decisions, and runtime feedback between runs:
- Call counts, self/total time per function
- Branch taken/not-taken ratios
- Loop iteration counts (min/max/avg)
- Inline cache hit/miss rates
- Provider selection history (which GPU/SIMD path was fastest)
- JIT tier transition history

### 6.3 SMF Integration

New sections for the SMF format (shared structural types at `src/compiler_rust/common/src/smf/`):

| Section | Purpose |
|---------|---------|
| `SMF_SECTION_PROFILE` | Symbol profiles, hotness, provider selection |
| `SMF_SECTION_MIGRATION` | Old hash → new hash mapping with confidence |

### 6.4 Cross-Version Profile Migration

| Match Level | Condition | Profile Reuse |
|-------------|-----------|---------------|
| Exact | Same MIR hash | 100% |
| Rename | Function renamed, body identical | 90% |
| Similar Body | Control flow graph similar | 50% |
| Signature Changed | Incompatible | 0% |

Migration report ties into the optimizer manifest versioning system, using `stable_name` identifiers for cross-version symbol identity.

---

## 7. Binary Optimization

### 7.1 LLVM PGO

Mapped to Simple's optimization levels (from `doc/07_guide/backend/llvm_optimization_workflow.md`):

| Simple Level | LLVM Flags |
|---|---|
| `none` | `-O0` |
| `basic` | `-O1` |
| `standard` | `-O2` |
| `aggressive` | `-O3 -flto` |

PGO workflow:
```bash
simple build --pgo-generate     # Stage 1: instrumented build
./app.exe <workload>            # Stage 2: collect .profraw
simple build --pgo-use          # Stage 3: profile-guided rebuild
```

### 7.2 BOLT Integration

Post-link optimization:
```
EXE → Profile Collection → BOLT → Optimized EXE
```

Improvements: function reordering, basic block reordering, ICache optimization, branch optimization.

### 7.3 IR Quality Checklist (existing)

From the LLVM workflow guide, verification before any backend change:
- Correct `nsw`/`nuw`/`noalias`/`nonnull` attributes (never invented for benchmark wins)
- Benchmark acceptance gate with before/after comparison
- Hot-path optimization pattern verification

---

## 8. Profiling Infrastructure

### 8.1 Existing Profiler Sources

| Component | Source |
|-----------|--------|
| Compiler profiler | `src/compiler/90.tools/perf/profiler.spl` |
| App profiler | `src/app/profiling/profile.spl`, `src/app/io/profiler_simple.spl` |
| Hotspot analyzer | `src/app/profiling/analyze_hotspots.spl` |
| SIMD profiler | `src/lib/nogc_sync_mut/simd/profile.spl`, `fp_profile.spl` |
| Engine profiler | `src/lib/nogc_sync_mut/engine/core/profiler.spl` |
| MDSOC adapter | `src/compiler/85.mdsoc/adapters/in/profiler_adapter.spl` |
| Rust runtime profile | `src/compiler_rust/compiler/src/runtime_profile/profiler.rs` |

### 8.2 Profile Data Model

```
FunctionProfile:
    call_count, self_time, total_time
    branch_taken, branch_not_taken
    loop_count (iterations, max, avg)
    deopt_count, jit_count
    inline_cache (target_count, miss_count)

Call Graph:
    caller → callee, count
    main ├─ parse: 50000
         ├─ execute: 30000
         └─ write: 20000
```

---

## 9. Optimize App (CLI Tool)

Existing CLI tool at `src/app/optimize/`:

| File | Purpose |
|------|---------|
| `main.spl` | Entry point |
| `analyze.spl` | Profile analysis |
| `compare.spl` | Before/after comparison |
| `apply.spl` | Apply optimization decisions |

Accessible via: `bin/simple optimize [analyze|compare|apply]`

---

## 10. Known Issues and Bugs

From `doc/08_tracking/bug/`:

| Bug | Date | Status |
|-----|------|--------|
| `jit_hotspot_optimization_plan_interpreter_cost` | 2026-05-28 | Interpreter cost model inaccurate |
| `jit_hotspot_shared_policy_plan_cost` | 2026-05-28 | Shared policy cost estimation |
| `jit_hotspot_verification_process_storm` | 2026-05-29 | Verification process storm under load |
| `optimize_native_cli_stub_segfault` | 2026-05-27 | Native CLI stub segfault |

---

## 11. Milestones

| Milestone | Description | Status |
|-----------|-------------|--------|
| M1 | Runtime Profile Infrastructure — call/loop/branch count, `.sprof` | **Partial** — `FunctionProfile` exists, `.sprof` file format TBD |
| M2 | Tiered HotSpot Runtime — Cold→Warm→Hot→VeryHot | **Implemented** — 3-tier (Interpreted/Fast/Optimized) with fact-driven planning |
| M3 | Persistent SMF Profiles — save/load/merge | **Planned** |
| M4 | Profile Migration — version diff, identity mapping, count reuse | **Planned** — manifest `stable_name` provides identity anchor |
| M5 | LLVM PGO — instrumentation + optimization | **Planned** — LLVM backend integration ready |
| M6 | BOLT Integration — post-link optimization | **Planned** |
| M7 | Unified Algorithm Provider Registry — CPU/SIMD/GPU/Remote | **Partial** — BLAS/CUDA/Graphics providers exist, unified registry TBD |
| M8 | Self-Learning Optimization — profile-guided runtime + compilation + algorithm selection | **Roadmap** |

---

## 12. Expected Benefits

| Category | Improvement | Mechanism |
|----------|-------------|-----------|
| Startup | 20–50% faster | Tiered JIT: interpret first, compile hot paths |
| Hot Loops | 2×–20× faster | Profile-guided inlining + LLVM tier-2 |
| SIMD Algorithms | 2×–16× faster | Auto-vectorization provider + target gating |
| GPU Algorithms | 10×–1000× faster | CUDA/Vulkan provider waterfall |
| Production Native | 10–30% faster | PGO + ThinLTO + BOLT |
| Long-Term Learning | Cumulative | Runtime knowledge preserved and migrated across releases |

---

## 13. Related Documents

### Research
- `doc/01_research/domain/optimization_plugin_jit_hotspot.md`
- `doc/01_research/domain/compiler_optimization_infra_refactor_2026-05-13.md`
- `doc/01_research/domain/llvm_optimization_best_practices_2026.md`
- `doc/01_research/domain/binary_size_optimization_across_languages.md`
- `doc/01_research/domain/target_instruction_optimization_32bit.md`
- `doc/01_research/local/bootstrap_size_optimization_research_2026-01-31.md`

### Design
- `doc/05_design/optimization_plugin_jit_hotspot.md`
- `doc/05_design/optimizer_manifest_versioned_design.md`
- `doc/05_design/target_instruction_optimization_32bit.md`
- `doc/05_design/baremetal_critical_app_profile.md`

### Guides
- `doc/07_guide/compiler_optimization_plugin.md`
- `doc/07_guide/compiler_optimization_levels.md`
- `doc/07_guide/backend/llvm_optimization_workflow.md`

### Architecture
- `doc/04_architecture/mdsoc_architecture_tobe.md` (Part 3: MDSOC+ ECS Business Layer)

### Plans
- `doc/03_plan/agent_tasks/optimization_plugin_jit_hotspot.md`
- `doc/03_plan/simple_db_jit_optimization_plan_2026-05-27.md`
- `doc/03_plan/render_2d_optimization_plan_2026-05-30.md`
- `doc/03_plan/simd_utf8_text_api_optimization.md`
