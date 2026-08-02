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
bin/simple run src/app/gpu_lint/gpu_runnable_scan.spl
```

Text-level prototype: scans **top-level `.spl` files** of
`src/lib/gc_async_mut/gpu/engine2d` + `src/lib/gc_async_mut/gpu/browser_engine`
(hardcoded in `main()`), builds a conservative **name-match** call graph, and
propagates blockage transitively from roots (`is_root_name`: draw primitives,
tile/pixel/glyph checksums, draw_ir exec/apply/dispatch, cull).
Prints a ≤30-line summary to stdout; the full report `file_write` path near the
end of `main()` is **hardcoded to a session scratchpad** — repoint `out_path`
before running. Known caveats (in the report header): same-name defs on
unrelated types are merged; trait signature decls count as empty runnable
bodies; cycle marking includes nodes that merely reach a cycle.

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
  `vk_*`, `sffi_vulkan*`, `sffi_cuda*`, and anything containing `vulkan_sffi` /
  `cuda_sffi`. (Metal SFFI is currently NOT whitelisted — the
  `metal_sffi_*` hits in the report are classified banned-FFI; decide
  deliberately before "fixing" those rows.)
- This mirrors `gpu_checker.spl`'s set (heap alloc, literals, closures, string
  machinery, recursion, dyn dispatch, async, throw, yield, print, FFI,
  non-scalar params), which matches the W1 plan's accept/reject table and
  SPIR-V reality.

## Overload-taint rule

Registration is **by NAME**: if any function named N is a root (or reachable),
ALL defs of N are checked, and if **any def of N is blocked, every caller of N
is tainted** ("any-def-blocked"). This is deliberate: the name-keyed call graph
cannot resolve which overload a call hits. Option A must key by name+arity and
report per-signature (the name-keyed `gpu_function_targets` table is a known
overload-blind trap, `hir_types.spl:233-244`).

## Current inventory (scan of 2026-08-02)

187 files, 4142 defs (3146 unique names); **1463/3146 names blocked**;
**133 tainted overloaded names**; roots: 24 total → **10 BLOCKED,
14 OFFLOADABLE**. Top blocking constructs: string-op 1089, list-push 442,
text-interpolation 437, recursion-cycle 422, closure 170, print 101, io-call 55,
then metal_sffi_* / rt_time_now_micros FFI. Healthy roots include the
vector/bitmap font checksum lanes and draw_ir dispatch-only entry points;
blocked roots include `clear`/`draw_rect_filled` (reach
`webgpu_sffi_compute_draw`) and the baremetal draw_* family (cycles).

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
