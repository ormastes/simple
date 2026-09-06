# GPU-Runnable Check — Design

**Date:** 2026-08-02 · **Status:** Proposed (implements Stage 2 of
`doc/03_plan/ui/rendering/gpu_runnable_check_impl_plan.md`).
**Research base:** `doc/01_research/ui/rendering/gpu_runnable_compile_time_verification.md`
(Part C mechanism choices; §Deployment options D1 incremental design).

## 1. Annotation semantics

`@gpu_runnable` on a free function or method declares: *this function's body,
and everything it transitively calls, uses only constructs expressible in a GPU
compute kernel*. It is a checked assertion, not a codegen directive — it does
not by itself lower anything to SPIR-V/CUDA (that remains the `@gpu_kernel`
path, `src/compiler/50.mir/_MirLowering/function_lowering.spl:30`). Relation to
existing markers:

- `@gpu_kernel`/`@gpu` — entry points that ARE lowered; implicitly
  `@gpu_runnable` and checked under the same rule.
- `@gpu_runnable` — helper tier: callable from kernels; checked, never lowered
  standalone.

Parsing: one `elif` in the decorator chain
(`10.frontend/core/_ParserDecls/enum_module_body.spl:668`; unknown decorators
are consumed and discarded at :708-713, so the seed and older binaries
tolerate the annotation by construction — verify, don't assume). Storage: flat-AST
bool slot mirroring `decl_is_gpu_kernel`
(`10.frontend/core/_Ast/decl_nodes.spl:277`, accessor :1059); tree-parser
`FunctionAttr` field (`00.common/_Attributes/decl_attrs.spl:718`);
`HirFunction.is_gpu_runnable: bool` beside `is_gpu_kernel`
(`20.hir/hir_definitions.spl:57-59`).

## 2. Transitive rule

A function F with `is_gpu_runnable` passes iff every statement/expression in
its body is clean AND every callee is one of:

1. a function that itself passes (any module),
2. an entry in the **intrinsic whitelist manifest** (§4),
3. a registered gpu extern.

Closure algorithm: fixpoint worklist over the whole-program function map after
HIR module merge, reusing the taint-propagation shape of
`10.frontend/core/alloc_inference.spl:174-194` (backward propagation:
seed = fns containing a banned construct or calling an unknown/unclean name;
propagate "tainted" to callers until stable). Recursion is detected by SCC over
`10.frontend/core/call_graph.spl:55` (cycle DFS :101-166) — upgrading
`gpu_checker.spl:293`'s direct-self-recursion-only check; any marked fn inside
or reaching a cycle containing a marked fn is a violation.

## 3. Overload rule — name + arity, all-must-pass

Registration is by name+arity: when any overload of `(N, arity)` is marked,
ALL functions with that name+arity (enumerated by scanning
`HirModule.functions`, `20.hir/hir_types.spl:29`) must pass, and each failing
signature gets its own diagnostic. Rationale: call sites resolve late and a
green result must mean the whole resolvable set is green (research Part C(3)).
The side table is new and keyed `name + "/" + arity` — explicitly NOT the
existing `gpu_function_targets` table, which is keyed by bare name text
(`20.hir/hir_types.spl:30-31,:233-244`) and therefore overload-blind. The
scanner prototype's any-def-blocked rule (133 tainted names in the 2026-08-02
report) is the conservative text-level approximation of this same rule.

## 4. Ban list and intrinsic whitelist manifest

**Ban list** = `src/compiler/35.semantics/gpu_checker.spl` (the checks exist,
currently uncalled by any walk — research A1): heap alloc :250, array literal
:256, dict literal :260, set literal :264, string concat :268, string
interpolation :272, closures/lambdas :280/:284, recursion :293 (upgraded to
SCC, §2), dynamic dispatch/`dyn` :301/:306, async/await/spawn :338-346,
throw/try-catch :350-354, yield :358, print family :325, param/return types
outside `GPU_SCALAR_TYPES` (:86-91) plus fixed-size buffer types :229.
Additions vs today: Dict/Set method use (not just literals), `List.push`
(growth = heap alloc; the report's 442 list-push hits), unbounded `while`
accepted with a warning until W1 bound analysis exists (research Part C(2)).

**Whitelist manifest** replaces the `fn_name.starts_with("gpu_")` prefix hack
(`gpu_checker.spl:174-180`) with an explicit data table (per rust-gpu/Slang
capability atoms, research Part B): families `vulkan_sffi_*`, `cuda_sffi_*`,
`webgpu_sffi_*`, `metal_sffi_*`, plus named singletons (e.g.
`rt_time_now_micros` if profiling inside kernels is accepted — default NO;
`rt_*` stays banned, cf. `gpu_checker.spl:330`). The scanner's calibration gap
— `is_gpu_intrinsic` at `src/app/gpu_lint/gpu_runnable_scan.spl:113-116`
accepts vulkan/cuda spellings only, falsely flagging `webgpu_sffi_compute_draw`
(`…engine2d/backend_webgpu.spl:309,:336`) and ~112 `metal_sffi_*` calls — is
exactly the failure mode the manifest prevents: one table, shared by scanner
(Stage 1) and semantic pass (Stage 2), reviewed in one place.

## 5. Incremental summary design (D1)

Per research D1: closure cost is parse-dominated; scope to the gpu dirs
(~293 files / ~112K lines, 2.6% of repo) and never run repo-wide per edit.

- **Per-file summary** (pure function of file content):
  `{path, content_hash, fns: [{name, arity, gpu_runnable, gpu_kernel}],
  calls: [(caller, callee_name)], hits: [(fn, construct, line)]}`.
- **Store:** `.sdn` file under `build/` keyed by content hash (no cache infra
  exists today — `cli_lint_commands.spl` and `query_lint.spl` have none, LSP
  caches only document text, `src/app/lsp/server.spl:12-80`).
- **Fixpoint runs over summaries only**: an edit re-parses one file and re-runs
  a cheap reduce; first run seeds the target dirs. The same summaries back the
  `query_lint`/LSP surfacing path (`src/app/cli/query_lint.spl:265,294-306`)
  for editor UX without re-closure per keystroke.
- Cache poisoning guard: summary format carries a version int; version bump
  invalidates wholesale.

## 6. Failure UX — call-chain diagnostics

Keep a parent-edge map during taint propagation (first-parent is enough; this
is a diagnostic, not a proof). Every violation reports exact construct + site +
chain, meeting the W1 acceptance bar
(`doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md:913-919`):

```text
error[gpu-runnable]: 'draw_rect' is @gpu_runnable but reaches banned construct
  'string interpolation' at generated_kernel_dispatch.spl:500
  via draw_rect -> launch_plan -> module_artifact_name
note: overload draw_rect/4 at backend_metal.spl:210 passes; draw_rect/5 fails
```

One diagnostic per (marked root, first blocking site) and one per failing
overload (§3). Inventory mode demotes `error` to `warning` — the warning
stream, grouped by construct, IS the GPU-ification burn-down list.

## 7. AOP separation pattern for renderer code

Pattern: split each blocked renderer function into a **gpu core** (pure
scalar/buffer arithmetic, `@gpu_runnable`) and a **CPU shell** (same public
name/signature) owning everything host-shaped: logging/print, string
formatting, budget checks, command-list recording (`.push`), fallback routing.
This is AOP-style separation of concerns done by hand — research D2 shows the
in-repo AOP weaver cannot enforce or generate it (pointcuts match names only,
`10.frontend/core/aop.spl:120,:347-421`; advice wraps execution, cannot
inspect bodies), so the checker verifies the core and the shell stays ordinary
CPU code.

**Before** — real blocked root from the 2026-08-02 report:
`cull_face` (`src/lib/gc_async_mut/gpu/browser_engine/webgl_context.spl:997`),
blocked by list-push at :1004:

```simple
me cull_face(mode: i32) -> bool:
    if not self.ensure_context_available(): return false
    if mode != WEBGL_BACK and mode != WEBGL_FRONT and mode != WEBGL_FRONT_AND_BACK:
        self.last_error = WEBGL_INVALID_ENUM
        return false
    self.cull_face_mode = mode
    self.render_commands.push(webgl_render_command_cull_face(mode))  # :1004 — blocked
    true
```

**After** — validation becomes a gpu-runnable core; recording stays in the
shell:

```simple
@gpu_runnable
fn cull_face_validate(mode: i32) -> bool:            # pure, scalar-only
    mode == WEBGL_BACK or mode == WEBGL_FRONT or mode == WEBGL_FRONT_AND_BACK

me cull_face(mode: i32) -> bool:                     # CPU shell, unchanged API
    if not self.ensure_context_available(): return false
    if not cull_face_validate(mode):
        self.last_error = WEBGL_INVALID_ENUM
        return false
    self.cull_face_mode = mode
    self.render_commands.push(webgl_render_command_cull_face(mode))
    true
```

The same split applies at scale to the report's dominant blockers: string-op
(1089) and print (101) move into shells (e.g. `module_artifact_name`
interpolation at `…engine2d/generated_kernel_dispatch.spl:500` moves to the
dispatch-setup shell); list-push command recording (442) stays shell-side while
per-pixel/per-vertex math becomes cores. Rule of thumb: cores take scalars and
fixed-size buffers in, return scalars/writes into preallocated buffers out;
shells own all allocation and I/O.
