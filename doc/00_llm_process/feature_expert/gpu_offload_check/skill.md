# GPU Offload Check Feature Expert

## Role

Own process knowledge for the **gpu-runnable compile-time check**: verifying at
scan/lint time — not runtime — that web/2D renderer functions are
GPU-offloadable, and maintaining the inventory of what is not. The model is
CUDA `__device__` / SYCL reachability: register root functions as
"must be GPU-runnable" and require the whole transitive call closure to avoid a
ban list of host-only constructs. Staged policy (research doc D4):
**scanner now (Option C, zero compiler changes) → semantic pass later (Option A,
`35.semantics` + `@gpu_runnable` annotation)**. AOP/weave enforcement was
evaluated and rejected as infeasible today (research D2).

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Feature Links

- Research (authoritative design): [doc/01_research/ui/rendering/gpu_runnable_compile_time_verification.md](../../../01_research/ui/rendering/gpu_runnable_compile_time_verification.md)
- Plan hook: [doc/03_plan/platform/structural_compute/webrender_gpu_offload_plan.md](../../../03_plan/platform/structural_compute/webrender_gpu_offload_plan.md) § Compile-time offloadability check (W1 lane owns the eventual `@gpu_event` compiler)
- Scanner (landed prototype): [src/app/gpu_lint/gpu_runnable_scan.spl](../../../../src/app/gpu_lint/gpu_runnable_scan.spl)
- Dormant pieces the Option-A pass composes: `src/compiler/35.semantics/gpu_checker.spl`
  (ban list, never wired), `src/compiler/10.frontend/core/alloc_inference.spl:174-194`
  (transitive fixpoint), `src/compiler/35.semantics/noalloc_checker.spl` (manifest template)
- Layer expert: [browser_engine](../../layer_expert/browser_engine/skill.md)
  (owns `src/lib/gc_async_mut/gpu/browser_engine`; the engine2d half has no layer expert yet)

## The tool: how to run

```bash
bin/simple run src/app/gpu_lint/gpu_runnable_scan.spl -- --report=PATH  # full ranked report (default /tmp path)
sh scripts/check/check-gpu-runnable.shs   # warn-only gate; report at build/gpu_runnable_report.txt
```

Productionized 2026-08-02 (`2e3e249e1e3`): scans **top-level `.spl` files** of
`src/lib/gc_async_mut/gpu/engine2d` + `src/lib/gc_async_mut/gpu/browser_engine`,
builds an **owner-aware, import-filtered** call graph (see next section), and
propagates blockage transitively from roots (`is_root_name`: draw primitives,
tile/pixel/glyph checksums, draw_ir exec/apply/dispatch, cull).
Prints a ≤30-line summary to stdout; `--report=PATH` writes the full ranked
report (no session-scratchpad hardcode anymore). The pre-commit-shaped gate
`scripts/check/check-gpu-runnable.shs` runs the same scan and reports BLOCKED
names but is **warn-only** (`gpu_runnable_gate=warn_only_pass`) per the staged
plan `doc/03_plan/ui/rendering/gpu_runnable_check_impl_plan.md` — inventory and
ratchet first, hard-fail only after whitelist calibration settles. Known
caveats (in the report header): dotted calls with unresolvable receivers still
weak-edge to all reachable same-name defs (over-connects taint); the import
filter is a line-based substring match on file basenames (short names like
`mod` over-match; re-exports not followed transitively); trait signature decls
count as empty runnable bodies.

## Ban list / whitelist (scanner `line_violations`)

- **Banned:** text interpolation; `.push(` (list alloc); Dict use
  (`Dict<`/`contains_key`/`keys`/`values`); string ops
  (`split/replace/trim/join/starts_with/ends_with/index_of/to_text/to_upper/
  to_lower/chars/substring`); `print`; io calls (`file_*`, `dir_*`, `http_`,
  `socket`, `shell_run`, `process_run`, `getenv/env_get`, `read_line`);
  closures (`=>`, `\`); higher-order calls (`.map/.filter/.flat_map/.each/.sort`);
  recursion or any call cycle; **non-GPU FFI** — any `*sffi*`, `ffi_*`, `rt_*`,
  `extern_*` not on the whitelist.
- **Whitelisted GPU intrinsics** (`is_gpu_intrinsic`): `vulkan_*`, `cuda_*`,
  `vk_*`, `sffi_vulkan*`, `sffi_cuda*`, anything containing `vulkan_sffi` /
  `cuda_sffi`, and — since `2e3e249e1e3` — `webgpu_sffi_*` and `metal_sffi_*`
  (the earlier banned-FFI classification of metal hits was a calibration gap,
  now resolved deliberately in the whitelist).
- This mirrors `gpu_checker.spl`'s set (heap alloc, literals, closures, string
  machinery, recursion, dyn dispatch, async, throw, yield, print, FFI,
  non-scalar params), which matches the W1 plan's accept/reject table and
  SPIR-V reality.

## Owner-aware graph + overload-taint rule (2026-08-02, `7f9fe07e9be`)

Graph nodes are **per-def `(file, name)`**, with receiver-kind-prefixed
callees:

- **Strong (resolved) edges:** plain/`self` calls resolve same-file first,
  then import-reachable. Cycle detection runs on strong edges ONLY — real
  recursion is always a resolved call. This killed the merged-name self-loop
  false positives: recursion-cycle blocked names **249 → 40**; all five paint
  roots (`clear`, `draw_rect_filled`, `draw_line`, `emu_draw_line`,
  `emu_draw_ellipse`) lost their phantom recursion verdicts and now report
  owner-tagged chains ending in real FFI violations. True-recursion control
  (`be_dom_find_by_id`, self-call `dom_accessors.spl:310`) stays BLOCKED.
- **Weak edges:** dotted calls with unresolvable receivers edge to every
  reachable same-name def EXCEPT the caller — so delegation like
  `engine.clear -> backend.clear` is a **cross edge, never a self-loop**.
  Weak edges skip cycle detection but still propagate the **any-def-blocked
  overload taint**: if any def of N is blocked, every caller of N is tainted.
- **Documented residual:** ambiguous dotted MUTUAL recursion is not
  cycle-checked (weak edges don't feed cycle detection) — the conservative
  trade for −209 false positives.

Option A must still key by name+arity and report per-signature (the
name-keyed `gpu_function_targets` table is a known overload-blind trap,
`hir_types.spl:233-244`).

## Current inventory (scan of 2026-08-02, post owner-aware graph)

4155 defs (3159 unique names, 4155 graph nodes); **1398/3159 names blocked**;
**113 tainted overloaded names**; roots: 28 total → **14 BLOCKED,
14 OFFLOADABLE**. Dominant blockers remain string ops, list-push, and
text-interpolation; recursion-cycle is down to 40 names (was 422 under the
name-merged graph, 249 immediately before the owner-aware fix). Healthy roots
include the vector/bitmap font checksum lanes and draw_ir dispatch-only entry
points; the vulkan clear/draw_line dispatch chain
(`_enqueue_framebuffer_compute`/`_dispatch_framebuffer_checked`/
`_flush_pending_compute`) was cleared by the `b0ef8e6aee5` pending-compute
preallocation (`.push()` growth → 16-slot arrays + live-count cursor).

## Phase-audit reality (2026-08-02 — which phases have real GPU impls)

From the vulkan-lane probe audit (headless RTX A6000 host):

- **Naming-only, no GPU code:** phase 1 HTML tokenize/parse, phase 2 CSS
  "GPU tables", phase 4 style/decl apply (plus silent wall-clock budget drops
  styling, `renderer_core.spl:2556`).
- **Real GPU code but ORPHANED (zero production callers):** the whole
  `gpu_web` lane — phase 3 DOM arena build (CPU oracle + capacity plan only)
  and phase 5 CUDA layout port (`gpu_web/layout/cuda_execution_port.spl:389-433`
  does real PTX load/alloc/dispatch with provenance; CUDA-only, no Vulkan port;
  nothing outside `gpu_web` imports it).
- **Real but gated OFF by default:** phase 6 paint — tile GPU lane
  (`SIMPLE_WEB_TILE_GPU=1`) and presenter GPU-paint (`SIMPLE_WEB_GPU_PAINT` +
  economics gate that declines typical text frames); default html→pixels path
  is CPU software raster even when the caller says "vulkan".
- **Genuine end-to-end GPU:** phases 7-8 — engine2d `backend_vulkan.spl` real
  `vulkan_sffi_*` dispatch, present + `read_pixels_with_source()` provenance
  (probe: `source=device_readback`, positive checksum).

Consequence for this feature: mark/scan effort pays off first on the engine2d
primitive/paint closure (the code that actually reaches a device), and the
inventory doubles as the burn-down list for making phases 1-5 honest.

## Verification commands

- Re-run the scanner (above) after any refactor in the two scanned dirs; the
  diff of blocked-name count and per-root verdicts is the ratchet.
- Inventory-mode-first policy: warnings, not errors, until the list is burned
  down (research Part C(5)); the W1 acceptance bar ("exact unsupported
  construct" per rejection) applies to Option A, not this scanner.
- SPipe skill for agents: `.claude/skills/gpu-offload-check.md`.

## Update Rule

When the project process creates or changes research, requirements,
architecture, design, tests, implementation, verification, or release artifacts
for this feature, update this skill with the new links, current inventory
numbers, and handoff notes BEFORE committing.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
