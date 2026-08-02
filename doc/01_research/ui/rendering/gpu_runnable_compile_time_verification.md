# Compile-Time Verification of GPU-Runnable Renderer Logic

**Status:** Research (2026-08-01). No code changes.
**Question:** How to verify at compile/lint time — not runtime — that web/2D renderer
logic is GPU-offloadable, and inventory what is not. Sketch: register a function (and
all overloads) as "must be GPU-runnable", verify the property transitively.

---

## Part A — In-repo prior art

### A1. The @gpu_event plan (documented, not implemented)

`doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md`:

- :110-126 proposes `@gpu_event(max_steps, max_mutations, max_host_effects, deterministic)`;
  :124 states plainly "This syntax does not exist yet".
- :136-146 pipeline: Simple fn → HIR effect+bound analysis → GpuEventIR → ProcessingIR →
  {CPU oracle, SPIR-V, CUDA, MSL, DXIL, SIMD}.
- :162-174 accept/reject table — accepted: arithmetic, bounded loops; host-effect-ized:
  network/clipboard/file/IME/a11y; **rejected:** arbitrary FFI/syscall (:172), runtime
  recursion (:173), GC/heap allocation (:174).
- :887-925 W1 lane: parse/validate `@gpu_event`, effect analysis + bounded-loop proof,
  reject heap/GC/recursion/exceptions/virtual dispatch/host pointers/unbounded output
  (:901-909); acceptance requires "compile-time rejection includes exact unsupported
  construct" (:913-919). Futhark/Taichi cited as models (:739-740).
- `doc/03_plan/platform/structural_compute/webrender_gpu_offload_plan.md:15` restates the
  pipeline; `simple_compiler_offload_plan.md:36` wants a generic "legality verifier".

**Implementation reality:** none of the W1 directories exist (`src/compiler/20.hir/gpu_event/`
etc.); no GpuEventIR, no compiler-side ProcessingIR, no bound checking. What DOES exist:

**`src/compiler/35.semantics/gpu_checker.spl`** (419 lines) — a checker for the
pre-existing `@gpu`/`@gpu_kernel` subset. `GpuKernelChecker` (:198) rejects per-construct:
heap alloc :250, array `[]` :256, dict `{}` :260, set `s{}` :264, string concat :268 /
interpolation :272, closures/lambdas :280/:284, direct self-recursion :293 (no SCC — mutual
recursion passes), dynamic dispatch/`dyn` :301/:306, calls outside a **prefix whitelist**
`fn_name.starts_with("gpu_")` :174-180 (externs :320, print family :325, `rt_*` :330),
async/await/spawn :338-346, throw/try-catch :350-354, yield :358, params outside
`GPU_SCALAR_TYPES` (:86-91: i8..u64, f32, f64, bool) :229, target names :234.

**Critical gap:** the `check_*` methods are never invoked by any AST/HIR walk. The only
production importer is `src/compiler/50.mir/_MirLowering/function_lowering.spl:30`, which
imports `parse_gpu_kernel_target` only. The rejection logic is a passive library exercised
solely by `test/01_unit/compiler/semantics/gpu_target_contract_spec.spl:75`. Runtime-side,
`src/lib/common/ui/gpu_web_event_model.spl:172-179` confirms the `@gpu_event` frontend
"does not exist yet" and consumes hand-lowered mutation tables instead.

### A2. Lint framework — capability assessment

- Entry: `src/app/cli/lint_entry.spl:37` → `src/app/io/cli_lint_commands.spl:44`, looping
  **one file at a time** (:165). `run_lint_file`
  (`src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:327`) parses the single file
  (:45); on parse failure all AST lints are skipped (:47-59).
- No rule-object registry: rules are plain functions re-exported via
  `src/compiler/35.semantics/lint/__init__.spl`, hand-called in
  `90.tools/lint/_LintMain/lint_checks.spl` (only fix-rules have a registry, :22/:231).
- Rules see either raw source lines or **flat-AST decl indices** into a per-file arena
  (`ignored_return.spl:76`, accessors `10.frontend/core/_Ast/decl_nodes.spl:833,887`).
  A rule CAN walk calls within one body (`lint/ignored_return.spl:158-181` dispatches on
  `EXPR_CALL`/`EXPR_METHOD_CALL`), but the arena holds only the current file — **lint is
  strictly per-file; cross-module call-graph closure is impossible under `bin/simple lint`
  as-is.**
- The flat AST has **no attribute field at all**; annotation-reading lint rules
  string-match source lines (`lint/param_tag.spl:81-89`).
- Whole-program machinery lives OUTSIDE lint:
  `10.frontend/core/call_graph.spl:55` (`call_graph_analyze`, cycle DFS :101-166) and
  **`10.frontend/core/alloc_inference.spl:174-194`** — a fixpoint worklist that
  transitively propagates "allocating" through the call graph. This is exactly the closure
  algorithm the sketch needs, already written.

### A3. Annotations, traits, overloads

- `@name(args)` **lexes and parses today with zero grammar changes** — the production
  parser reads any decorator generically
  (`10.frontend/core/_ParserDecls/enum_module_body.spl:555-714`) but dispatch is a
  hardcoded `elif` chain (`gpu_kernel`/`gpu` at :668); unknown names are consumed and
  **silently discarded** (:708-713). Adding `@gpu_runnable` = one `elif` branch + a
  flat-AST slot (cf. `decl_is_gpu_kernel`, `_Ast/decl_nodes.spl:277`, accessor :1059).
- Tree-parser side already has generic `Attribute{name,args,span}`
  (`10.frontend/parser_types.spl:181-198`) digested by
  `parse_function_attrs → FunctionAttr` (`00.common/_Attributes/decl_attrs.spl:718`),
  including GPU args (`parse_gpu_function_attr_args` :830). `HirFunction`
  (`20.hir/hir_definitions.spl:26-59`) carries digested fields only — `is_gpu_kernel`,
  `gpu_target`, `gpu_backend_order` (:57-59) — so a new bool is a one-field addition.
- **Traits attach to types only** (`syntax_quick_reference.md:1283-1312`;
  `20.hir/hir_types.spl:38-39`) — no capability marker on free functions. Not usable.
- **Runtime-family checker** (`35.semantics/gc_boundary_check.spl`): static manifest
  `RUNTIME_FAMILY_MANIFEST` :94-106 (rank per module-path prefix), violation on
  `imported.rank > source.rank` (:182-183, `higher_layer_runtime_family`). It checks
  **direct imports only** — never function bodies, never transitively. Call sites: the
  interpreter module loader (`module_loader_core.spl:505-525`, `[gc-warning]`) and the
  lint-query/LSP path (`src/app/cli/query_lint.spl:265,294-306`, which regex-scrapes `use`
  lines). Adding a `"gpu"` family row buys a coarse import fence for free, but no
  call-graph power.
- **Overloads:** no overload-set structure exists. `SymbolTable.define`
  (`20.hir/hir_types.spl:246-299`) appends shadowing entries; `lookup` returns newest only.
  Enumerating "all fns named N" = linear scan of `HirModule.functions` (:29). The existing
  GPU metadata side table `gpu_function_targets` (:30-31, :233-244) is keyed by **name
  text, not SymbolId** — inherently overload-blind. Dup-symbol diagnostics are link-time
  only (`70.backend/linker/sym_resolver.spl:105`).
- **Closest template:** `35.semantics/noalloc_checker.spl` — annotation-marked fns
  (`is_noalloc` :97), `check_noalloc_violations(fn_name, expr_tags, callee_names,
  manifest)` :161, transitive-call violations :196-215, whole-set driver
  `check_all_noalloc_fns` :221, closure deferred to `alloc_inference`'s fixpoint. Exported
  (`35.semantics/__init__.spl:115-120`) but, like `gpu_checker`, has no production caller.

## Part B — External art (brief)

- **CUDA `__device__`:** the exact per-function marker model. nvcc checks at compile time
  that a `__device__`/`__global__` fn calls only `__device__` fns; host calls are hard
  errors at the call site. Maps 1:1 onto `@gpu_runnable` + call check; note nvcc reports
  the immediate bad call, not the chain — we can do better.
- **SYCL:** no marker; device code = everything reachable from the kernel lambda. The
  compiler computes the reachable closure and rejects banned constructs anywhere in it
  (RTTI, exceptions, virtual calls, function pointers, dynamic alloc). Same closure, marker
  inferred from the entry point — matches "mark the paint entry, check reachability".
- **rust-gpu / Slang:** capability sets propagate bottom-up through the call graph; an
  entry point's required capabilities must be a subset of the target's. Slang's
  `[require(...)]` decorations are checked transitively. Justifies whitelisting intrinsics
  as capability atoms rather than name prefixes.
- **Koka effect system:** effects are inferred and part of the type; `total`/`div` vs
  `io` rows make "no heap, no exceptions, terminates" a checkable signature. Overkill for
  Simple today, but the accept/reject table in the W1 plan (:162-174) is effectively a
  two-row effect system (gpu-pure vs host-effect) — keep that framing.
- **OpenCL C:** subset-by-language: no recursion, no function pointers, no dynamic alloc,
  restricted stdlib. Confirms the ban list in `gpu_checker.spl` is the industry-standard
  set; the deltas Simple must add are Dict/Set/text machinery (GC-language constructs
  OpenCL never had).

## Part C — Recommendation (simple logic)

**(1) Marker: the annotation `@gpu_runnable`** (not a trait, not a runtime family).
Traits can't mark free functions (A3); the family checker is import-granularity only and
can't see calls (A3). The annotation parses today, and every piece of plumbing it needs
already has a worked example in the `@gpu_kernel` path: parser branch
(`enum_module_body.spl:668`), flat-AST slot (`decl_nodes.spl:277`), `FunctionAttr` field
(`decl_attrs.spl:668-830`), `HirFunction` bool (`hir_definitions.spl:57`).
Optionally ALSO add a `"gpu"` row to `RUNTIME_FAMILY_MANIFEST` so gpu-family modules get
the existing import fence as a cheap first gate — complementary, not the mechanism.

**(2) Transitive rule.** A `@gpu_runnable` fn may contain only:
calls to `@gpu_runnable` fns, whitelisted gpu intrinsics (replace the `gpu_` prefix hack
at `gpu_checker.spl:174-180` with an explicit manifest, per rust-gpu/Slang), and
registered gpu externs. **Ban list** (= `gpu_checker.spl` today, which already matches the
W1 plan and SPIR-V reality): heap alloc; array/dict/set literals and any Dict/Set use;
closures/lambdas; string concat/interpolation/formatting; recursion — upgraded from
direct-only (:293) to SCC detection via `call_graph.spl:101-166`; dynamic dispatch/`dyn`;
async/await/spawn; throw/try-catch; yield; print family; non-whitelisted FFI; params
outside `GPU_SCALAR_TYPES` plus fixed-size buffer types. Bounded-loop proof
(`max_steps`) is phase 2 — accept `while` with a lint warning until the W1 bound analysis
exists. Closure algorithm: reuse `alloc_inference.spl:174-194`'s fixpoint verbatim —
seed = marked fns, propagate "tainted" backward from any fn containing a banned construct
or calling an unmarked fn.

**(3) Overload rule.** Registration is by NAME: when any fn named N is `@gpu_runnable`
(or N is registered in a manifest), enumerate ALL fns named N by scanning
`HirModule.functions` and require every one to pass; report each failing signature
separately. Do NOT reuse the name-keyed `gpu_function_targets` table as-is — key the new
side table by `name + arity` (the overload-blindness at `hir_types.spl:233-244` is a known
trap), and emit one diagnostic per offending overload so a green result means the whole
overload set is green.

**(4) Where it runs: a driver-side semantic pass in `35.semantics/`** (sibling of
`gpu_checker.spl` / `noalloc_checker.spl`), invoked after HIR module merge where the
whole-program function map exists — NOT a `bin/simple lint` rule (per-file arena, no
attributes in flat AST, A2). Surface it in lint UX via the same route the family checker
uses (`query_lint.spl:294-306`) so editors see it. First step is wiring: `gpu_checker.spl`
is already written and dead — extending and *calling* it is most of the work.
**Failure UX:** keep a parent-edge map during the fixpoint and print the chain:
`error[gpu-runnable]: 'draw_rect' is @gpu_runnable but reaches banned construct
'string interpolation' at painter.spl:88 via draw_rect → paint_label → format_glyph`.
Every message names the exact construct + site, per the W1 acceptance bar (plan :913-919).

**(5) Web/2D renderer application.** Mark only the entry points — paint/primitive
functions in the draw pipeline (DrawIR emitters, rect/glyph/gradient/image primitive fns)
— and let the closure do the inventory. Run the pass in **inventory mode** first
(warnings, not errors): the emitted violation list IS the non-offloadable inventory,
grouped by construct (expect: text formatting, Dict-based style lookup, dynamic dispatch
in scene traversal, allocating list builders). Burn the list down; flip to error mode;
from then on any newly non-offloadable code fails the build with its call chain.

## Bottom line

Everything needed exists in pieces, none of it wired: the ban list (`gpu_checker.spl`),
the transitive fixpoint (`alloc_inference.spl`), the marker plumbing pattern
(`@gpu_kernel` path), and the per-fn manifest template (`noalloc_checker.spl`). The work
is composition plus one new annotation branch — not new analysis machinery.
