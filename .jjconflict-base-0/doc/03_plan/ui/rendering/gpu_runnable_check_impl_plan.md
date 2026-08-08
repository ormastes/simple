# GPU-Runnable Check — Implementation Plan

**Date:** 2026-08-02 · **Status:** Proposed · **Owner lane:** W1 subset of
`doc/03_plan/platform/structural_compute/webrender_gpu_offload_plan.md` (W1 row, :15).
**Research (authoritative for mechanism choices):**
`doc/01_research/ui/rendering/gpu_runnable_compile_time_verification.md` — Part C
recommendation + §Deployment options D4 ("C now → A later", :284-292).
**Design:** `doc/05_design/ui/rendering/gpu_runnable_check_design.md`.
**Prototype:** `src/app/gpu_lint/gpu_runnable_scan.spl` (484 lines, landed).

## Baseline (scanner inventory, 2026-08-02)

Scan of engine2d + browser_engine (187 files, 4142 fn defs): **1463/3146 names
blocked (46%)**; 133 overloaded names tainted by the any-def-blocked rule; roots
10 BLOCKED / 14 OFFLOADABLE. Top blockers: string-op 1089, list-push 442,
text-interpolation 437, recursion-cycle 422, closure 170, print 101, io-call 55,
then `metal_sffi_*`/`webgpu_sffi_*` FFI hits that are whitelist-calibration
artifacts, not real blockers (see Stage 1).

## Stage 1 — Scanner productionization (zero compiler change)

Per research D3b/D4: the standalone scanner is running-code distance from a
deployable inventory/ratchet gate; its name-match soundness gaps are acceptable
for that role only.

1. **Whitelist calibration.** `is_gpu_intrinsic`
   (`src/app/gpu_lint/gpu_runnable_scan.spl:113-116`) accepts only
   `vulkan_*`/`cuda_*` spellings, so `webgpu_sffi_*` and `metal_sffi_*` fall
   into `is_banned_ffi` (:118-123). This falsely blocks real device dispatch:
   report roots `clear` and `draw_rect_filled` are "blocked" solely by
   `webgpu_sffi_compute_draw` at
   `src/lib/gc_async_mut/gpu/engine2d/backend_webgpu.spl:309` and `:336`, and
   ~112 `metal_sffi_*` hits pollute the top-blocker table. Add
   `webgpu_sffi_`/`metal_sffi_`/`webgpu_`/`metal_` to the intrinsic set;
   keep `rt_*` banned except an explicit exception list (report shows
   `rt_time_now_micros` ×16 — decide per design §Whitelist manifest).
2. **False-positive reduction, receiver-aware where cheap.** The call graph is
   conservative name-match (`extract_callees` :97; caveats in report header):
   same-name methods on unrelated types merge, which manufactures
   recursion-cycle verdicts (422 hits; e.g. `draw_line`
   `backend_baremetal.spl:180` "recurses" only because 16 backends define
   `draw_line`). Cheap fixes, in order: (a) `self.foo(...)` calls resolve
   against same-file defs only; (b) trait signature decls (no body) stop
   counting as runnable definitions; (c) cycle marking distinguishes "in cycle"
   from "reaches cycle". No import resolution — that is Stage 2's job.
3. **Gate script, warning mode.** New `scripts/check/check-gpu-runnable.shs`
   (does not exist yet): runs
   `bin/simple run src/app/gpu_lint/gpu_runnable_scan.spl`, writes the report
   under `build/`, exits 0 always but prints the blocked-root count and a delta
   vs the committed baseline count. Wire one line into
   `scripts/hooks/pre-commit` via the installer pattern at
   `scripts/setup/install-workspace-guard-hook.shs:43-60`. Ratchet (exit 1 on
   regression) only after Stage 3 wave 1 lands.

**Acceptance gates.**
- Re-scan shows zero `ffi-call:webgpu_sffi_*` / `ffi-call:metal_sffi_*` rows in
  top blockers; `clear`/`draw_rect_filled` verdicts no longer cite backend FFI.
- recursion-cycle count drops materially (expect ≥50% of the 422 to be
  same-name-merge artifacts); each surviving cycle spot-checked ×5.
- `sh scripts/check/check-gpu-runnable.shs` runs clean from a fresh checkout.

**Verify:** `bin/simple run src/app/gpu_lint/gpu_runnable_scan.spl` then diff
the report; `sh scripts/check/check-gpu-runnable.shs; echo $?`.

## Stage 2 — `@gpu_runnable` annotation + 35.semantics pass (Option A)

Per research Part C + D1. All plumbing has a worked `@gpu_kernel` example.

1. **Annotation.** One `elif` branch in the decorator dispatch chain
   (`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:668`;
   unknown names are silently discarded at :708-713 today). Flat-AST slot
   mirroring `decl_is_gpu_kernel`
   (`10.frontend/core/_Ast/decl_nodes.spl:277`, accessor :1059). Tree-parser:
   `FunctionAttr` field (`00.common/_Attributes/decl_attrs.spl:718`).
   `HirFunction` bool next to `is_gpu_kernel`
   (`20.hir/hir_definitions.spl:57-59`).
2. **Pass.** New driver-side pass in `src/compiler/35.semantics/` (sibling of
   `gpu_checker.spl`/`noalloc_checker.spl`), wired after HIR module merge —
   NOT a `bin/simple lint` rule (per-file arena, no attributes in flat AST;
   research A2). Reuse: ban-list checks from `gpu_checker.spl:250-358`
   (currently dead — no production caller; research A1), fixpoint worklist
   pattern from `10.frontend/core/alloc_inference.spl:174-194`, SCC recursion
   via `call_graph.spl:101-166` (upgrades gpu_checker's direct-only :293).
3. **Overload table keyed by name+arity** — do not reuse the name-keyed
   `gpu_function_targets` (`20.hir/hir_types.spl:233-244`, overload-blind).
   All-must-pass rule per design §Overloads; one diagnostic per failing
   signature.
4. **Chain diagnostics.** Parent-edge map during fixpoint; every error names
   exact construct + site + call chain (W1 acceptance bar,
   `doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md:913-919`).
5. **Editor surfacing** via the `query_lint`/LSP route the family checker uses
   (`src/app/cli/query_lint.spl:265,294-306`). If per-keystroke UX is wanted,
   add the D1 incremental summary cache (design §Incremental); otherwise the
   pass runs on build/check only. Fold the `gpu` runtime-family row into this
   change set (research D3a: ~5 compiler files, import-fence add-on only).

**Acceptance gates.**
- `@gpu_runnable` on a fn calling `print` fails compile with a chain
  diagnostic naming `print` and the site; removing the call goes green.
- Overload test: 2 same-name/same-arity fns, one dirty → exactly one error
  citing the dirty signature.
- Scanner (Stage 1) and pass agree on marked engine2d roots, modulo documented
  scanner false positives; disagreements triaged before error-mode.
- `bin/simple build bootstrap` green (extern/annotation additions need seed
  parity — the decorator must at minimum parse-and-ignore on the seed path).

**Verify:** targeted specs beside
`test/01_unit/compiler/semantics/gpu_target_contract_spec.spl:75`;
`bin/simple test test/01_unit/compiler/semantics/`; `bin/simple build`.

## Stage 3 — Renderer GPU-ification waves

Inventory mode first: warnings ARE the burn-down list (research Part C(5)).
Pattern for all waves: AOP-style separation — `@gpu_runnable` core fn (pure
arithmetic on scalars/buffers) + CPU shell wrapper owning logging, budget,
command recording, fallback (design §AOP separation).

**Wave 1 — engine2d primitive paths.** Evict string-op (1089), print (101),
closure (170), list-push (442) from hot paths into shells. Priority roots from
the report: `draw_rect_filled`/`draw_line`/`draw_ellipse`(+`_filled`)
(`src/lib/gc_async_mut/gpu/engine2d/backend_baremetal.spl:131,:180,:435,:438`),
and the diagnostic-formatting chain
`_vector_font_glyph_readback_with_checksum → … → module_artifact_name`
text-interpolation at
`src/lib/gc_async_mut/gpu/engine2d/generated_kernel_dispatch.spl:500` (move
artifact-name formatting to the shell/setup path). Gate: all 24 scanner roots
in engine2d green or shell-split, blocked-name count for engine2d down ≥30%.

**Wave 2 — DrawIR exec + tile checksum.** Checksum roots are already green
(`…paint_tiles.spl:190,:206`, `…paint_tiles_gpu.spl:82`,
`backend_screenshot_capture.spl:32`) — mark them `@gpu_runnable` to lock them.
Fix the two blocked DrawIR runtime roots
(`draw_ir_runtime_adv.spl:27,:37`, recursion-cycle — likely Stage-1
false positives; re-triage first). Then, per phase audit #6, promote the tile
GPU lane: `SIMPLE_WEB_TILE_GPU` default-off gate at
`simple_web_html_layout_renderer_paint_tiles_gpu.spl:34-47` flips to
vulkan-lane default once its spec is green, and route verdicts propagate into
render evidence. Gate: tile-lane spec green with device provenance
(`source=device_readback`, cf. phase-audit probes).

**Wave 3 — orphaned gpu_web CUDA layout wiring.** Per phase audit #5/#3: real
device code at `gpu_web/layout/cuda_execution_port.spl:389-433` (session init,
PTX load, htod/kernel/dtoh, `executed_backend="hybrid_vector_gpu"`) is imported
only by `gpu_web/*/__init__.spl`. Wire `web_layout_run_full` into the
production layout path behind a flag; make a consumer read
`LayoutExecutionProof.reason` (fallback reasons at :393,:400,:424 currently
unread); mark the kernel-adjacent host fns `@gpu_runnable`. Vulkan layout port
is follow-on, not in this campaign. Gate: production render with flag on shows
`executed_backend="hybrid_vector_gpu"` + oracle parity on the fixture page;
flag off byte-identical.

**Campaign exit:** scanner gate flips from warning to ratchet; Stage 2 pass in
error mode for `src/lib/gc_async_mut/gpu/engine2d/**` marked roots.

## Risks

- Name-match scanner keeps residual false positives after Stage 1 — never use
  it for the W1 "exact construct" bar; that is Stage 2's job (research D4).
- Seed/bootstrap parity for the new decorator (Stage 2 gate above).
- Wave 3 depends on the sibling `auto→cuda→software` degrade fix (phase audit
  #5 note) — coordinate, don't duplicate.
