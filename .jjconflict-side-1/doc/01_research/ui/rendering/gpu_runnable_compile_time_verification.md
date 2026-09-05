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

---

## Deployment options (follow-up, 2026-08-01)

### D1. Lint-only path: cost and the incremental variant

**Scope sizing.** The target trees are ~293 files / ~112K lines
(`src/lib/gc_async_mut/gpu/browser_engine` 154 files / 68K lines,
`src/lib/gc_async_mut/gpu/engine2d` 113 / 38K, `src/lib/nogc_sync_mut/gpu/engine2d`
26 / 5.2K) against 11,373 `.spl` files repo-wide — a scoped closure touches ~2.6% of the
repo. Cost is parse-dominated (the fixpoint itself is a function-level worklist, linear in
call edges), so scoping to the two dirs is the difference between "hundreds of ms class"
and "whole-repo build class"; never run the closure repo-wide per lint invocation.

**alloc_inference is whole-program and dormant.** `alloc_inference_analyze()` takes no
arguments and reads module-level global state populated by `ceu_register_functions()`
(`10.frontend/core/alloc_inference.spl:41,:31-38,:47-52`), shared with
`call_graph_analyze` via `call_edge_utils.spl`. It is not invoked anywhere in-tree today
(only re-exports, `core/__init__.spl:150-153`). So the fixpoint pattern is reusable, but
it is driver-shaped, not per-file-lint-shaped.

**Incremental design (recommended for lint):** per-file summary = {functions defined
(name + arity + gpu_runnable flag), calls made (callee names), ban-list hits
(construct + line)}, cached on disk keyed by file content hash; the fixpoint runs over
summaries only, so an edit re-parses one file and re-runs a cheap reduce. No cache infra
exists today — `cli_lint_commands.spl` and `query_lint.spl` have zero cache logic, and the
LSP caches only document text by URI+version (`src/app/lsp/server.spl:12-80`) — so the
summary store is new (a `.sdn` file under `build/` suffices).

**Minimal lint-infra change: a POST-pass is feasible.** The per-file loop
(`src/app/io/cli_lint_commands.spl:165-199`) is followed by an end-of-run aggregation
block (`:201-215+`, fail-closed `not_linted_files` logic + `lint-summary` JSON emit), and
`lint_files` is fully materialized before the loop (`:151-156`). Insert: (1) per-file
step emitting the summary row (source-text scan, since the flat AST lacks attributes —
A2), (2) after-loop reduce loading cached summaries for unvisited target-dir files and
running the fixpoint. First run must seed the whole target dirs; thereafter cost ≈ changed
files + reduce. The same summaries serve the `query_lint`/LSP path for per-keystroke UX.

### D2. AOP / weave-time enforcement

What exists: pointcut/advice declarations `on pc{ execution(...) } before|around <handler>`
(`10.frontend/core/_ParserDecls/bitfield_aop_arch_decls.spl:186-240`); pointcut matching
is **glob over function names only** (`10.frontend/core/aop.spl:120,:347-421`); weaving
inserts **runtime calls** to advice functions at MIR level
(`50.mir/mir_aop_injection.spl:38-151`) plus an interpreter weave
(`70.backend/backend/interpreter_aop_weave.spl`); typed model in
`85.mdsoc/weaving/`. MDSOC proper is structural — layer/import checkers
(`85.mdsoc/layer_checker.spl`, `construct_checker.spl`) and SDN-driven dependency rules
(`70.backend/arch_rules.spl:20-88`).

**Verdict: not a path today.** Advice can wrap a function's *execution*; nothing can
introspect a function's *body* at compile time. A rule-checking aspect would need three
missing pieces: body/AST predicates in pointcuts, a compile-time reflection API over
HIR bodies, and a diagnostic-emitting advice form. Absent those, "AOP enforcement" reduces
to the module-family/arch-rules import fence — which Option C already covers more cheaply.
Related non-option: `comptime` blocks and `@static_assert` exist
(`10.frontend/core/parser_stmts.spl:415`,
`interpreter/eval_builtins.spl:203-219`) but `__traits` reflection is type-shaped
(`eval_builtins.spl:232-582`) — no query returns a function body, and there is no derive
hook, so per-function assertions would have to be hand-written inside every body.

### D3. Zero-compiler-change combo

**(a) Family fence — NOT actually zero-compiler-change.** `RUNTIME_FAMILY_MANIFEST` is a
hardcoded `val` table in the `.spl` (`35.semantics/gc_boundary_check.spl:94-106`), not
config-driven, and the family/prefix logic is duplicated: `00.common/gc_config.spl:146-228`
hardcodes the prefix classes; the interpreter loader has an independent if-chain of path
substrings that returns `""` for unknown families and **silently skips the check**
(`interpreter/module_loader_core.spl:446-480,:497-498`); sibling loaders and
`90.tools/verify/noalloc_reachable.spl` carry their own family strings. (An alias
`"gpu"` → `gc_async_mut` already exists, `gc_boundary_check.spl:64-70` — today the gpu dirs
are just gc-family.) Creating a real `gpu` family = small edits in ~5 compiler files.
Import-granularity only regardless. Classify as a cheap add-on to Option A, not part of C.

**(b) Standalone scanner + pre-commit — genuinely zero-compiler-change, and prototyped.**
`src/app/gpu_lint/gpu_runnable_scan.spl` exists (self-described prototype, :1-7):
text-level scan over hardcoded target dirs (:183-188), conservative name-match call graph
(`extract_callees` :97) with blockage-chain propagation (:367), intrinsic/banned-FFI
classification (:113-124), report writer (:438-466). Run:
`bin/simple run src/app/gpu_lint/gpu_runnable_scan.spl`. Wiring = one line
`sh scripts/check/check-gpu-runnable.shs` in `scripts/hooks/pre-commit` (installed via
`scripts/setup/install-workspace-guard-hook.shs:43-60`; examples at pre-commit :30,:35,:48)
plus a CI step. Cost is per-commit, not per-edit.

**(c) comptime/macro:** non-option (D2).

### D4. Matrix and staged recommendation

| | Compiler changes | Latency | Soundness |
|---|---|---|---|
| **A** semantic pass (35.semantics + fixpoint) | annotation branch, HirFunction bool, wire `gpu_checker`+`alloc_inference` | per-edit OK if scoped/incremental (D1) | high: real AST, arity-aware overloads |
| **B** AOP/weave | build body-predicate pointcuts + HIR reflection + diagnostic advice | n/a | **infeasible today — reject** |
| **C** scanner + pre-commit (+CI) | **none** | per-commit | gaps: text-level name matching (overload/arity-blind, alias/import renames invisible, method-call ambiguity → false positives AND misses) |

**Staged path: C now → A later.** C is running-code distance from deployment: harden the
prototype's callee matching slightly, add the check script + pre-commit/CI line, run in
inventory (warning) mode to produce the non-offloadable list immediately, with zero risk
to the compiler. Its name-match soundness gaps are acceptable for an inventory/ratchet
gate but not for the W1 acceptance bar ("exact unsupported construct"). When the W1
`@gpu_event` lane starts, build A (Part C design: annotation + `gpu_checker` wiring +
fixpoint, with the D1 summary cache if lint-time UX is wanted); keep C as the independent
out-of-band cross-check. Fold the `gpu` family-fence edits (D3a) into A's change set.
