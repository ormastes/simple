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

### UI performance evidence rules

For Engine2D/web optimization, separately report: retained GPU allocation
bytes/count, upload bytes, readback bytes, submits, fence polls/waits, frames in
flight, damage area, and fallback reason. A backend name or completed host queue
packet is not device execution. Require a device identity plus a backend fence
or timeline receipt. Keep steady device-present measurements readback-free and
run exact pixel capture as a separate correctness sample.

Chrome comparison is admitted only when both Chrome and Simple artifacts are
measured and share interval/sample/viewport/device metadata. Cold Chrome
process-plus-PNG time cannot be divided by warm in-process Simple paint time.
The current `perf_chrome_runner.spl` synthetic ratio is never publishable.

### Renderer comparison admission traps (2026-09-08)

- The selected Vulkan budget is latency-directional:
  `Simple p95 / C p95 <= 2.0`. A threshold expressed as Simple FPS being at
  least 10% of C is a different requirement and must not be used.
- `measured` is not `admitted`. A ratio requires identical fixture/event hashes,
  viewport, RGBA format, timing boundary, warmups/samples, and physical device;
  source/binary identity; real fence completion; a 2–3-slot ring; no fallback;
  and the full allocation/residency/upload/readback/damage receipt. Unknown
  counters are `-1` and reject the row; never coerce them to zero.
- Timed display admits zero framebuffer readback, zero buffer allocation, zero
  full-frame host upload, and no unconditional submit-and-wait. Correctness may
  perform one exact RGBA8 capture after timing. Its byte count is exactly
  `width * height * 4`.
- A blocking `vkWaitForFences` after each timed submit is not asynchronous even
  when three command buffers exist. Observe completion with nonblocking fence
  or timeline polling and report poll and blocking-wait counts separately.
- Never run renderer performance through a Rust seed. `bin/simple` resolving
  under `src/compiler_rust` is an explicit unavailable reason, not permission
  to use a Vulkan-feature seed.

### Chromium oracle SFFI rules (2026-09-08)

The owned reference bridge has exactly five C symbols and remains test-only.
Hash the explicit library before and after load, resolve every symbol once,
validate ABI identity before create, bound request/response storage, and destroy
then close exactly once. Ordinary Simple `[u8]` literals may be boxed and have
no stable native data pointer in the interpreter. Use the canonical one-call
`spl_wffi_call_i64_with_bytes` pin for immutable input and
`rt_byte_array_new_len` for mutable output/length slots. A passing fixture with
`oracle_identity=fixture-not-chromium` proves transport only—never Chrome or GPU.

### Residency and event-driven scheduling checklist

For every claimed GPU-resident renderer path, identify the owner and lifetime
of the device-local target, persistent mapped staging ring, and any readback
buffer. A mapped staging allocation is not a resident render target. The
steady path must not allocate, map/unmap, upload a full framebuffer, or copy a
frame to the CPU. Record allocation count, retained/staging bytes, upload
bytes, and teardown bytes; unknown values are `-1` and fail admission.

When transfer and graphics queues differ, the receipt must identify both queue
owners and the release/acquire barrier (or an explicit single-queue policy),
plus the fence/timeline value that makes the handoff visible. A host queue
packet, backend name, or `submit` return is not a device receipt.

The event path is host-owned: normalize and coalesce events, clip bounded
damage, tag the scene generation, freeze it into one frame slot, and schedule
the next available ring slot. Completion is a nonblocking fence/timeline poll;
only the matching monotonic token retires the slot. Do not drain or wait from
each event, and do not let stale input mutate an in-flight frame.

Parity has two independent lanes. C Vulkan and Simple Vulkan need identical
fixture/event hashes, viewport, format, queue/device identity, warmups, samples,
timing boundary, ring depth, and capture policy. Simple Web and Chrome need an
identical semantic primitive/event trace plus a device-origin receipt. Missing
canonical Chrome library or runner is an explicit **non-admission**; a fixture,
Electron DOM/paint result, or bootstrap diagnostic dylib cannot become a Chrome
GPU ratio.

- Re-run the scanner (above) after any refactor in the two scanned dirs; the
  diff of blocked-name count and per-root verdicts is the ratchet.
- Inventory-mode-first policy: warnings, not errors, until the list is burned
  down (research Part C(5)); the W1 acceptance bar ("exact unsupported
  construct" per rejection) applies to Option A, not this scanner.
- SPipe skill for agents: `.claude/skills/gpu-offload-check.md`.

## Campaign evidence map — seven green GPU-offload lanes (2026-08-02)

Authoritative record (counts transcribed from it, do not re-derive):
[doc/03_plan/platform/structural_compute/webrender_gpu_offload_plan.md](../../../03_plan/platform/structural_compute/webrender_gpu_offload_plan.md)
§ evidence table (lines ~93-102). All spec paths below were confirmed to exist.

| Lane | Spec | Result |
|------|------|--------|
| HTML parser GPU (flat projection, CPU-oracle parity) | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl` | 24/24 |
| CSS parser GPU tables (style_block_parse + selector) | `.../css_parser_gpu_tables_spec.spl` | 47/47 |
| DOM build GPU offload | `.../dom_build_gpu_offload_spec.spl` | 38/38 |
| CSS apply + transform (decl_apply lane) | `.../css_decl_apply_transform_spec.spl` | 69/69 |
| GPU script load + animation ticks | `.../browser_script_animation_gpu_spec.spl` | 22/22 |
| 2D rendering GPU offload parity (device provenance) | `test/02_integration/rendering/web_engine2d_gpu_offload_parity_spec.spl` | 17/17 |
| Full-GPU-offload web showcase + capture verification | `test/03_system/gui/web_showcase_full_gpu_offload_spec.spl` | 13/13 |

Supporting gates: engine2d renderer unit spec 23/23, backend resolver spec 6/6
(viable-probe auto-resolution, `b0ef8e6aee5`), plus
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_gpu_lane_spec.spl`
(tile grid + paint).

Read this table together with the **phase-audit reality** section above: a green
lane proves the *parity oracle* holds, NOT that the phase reaches a device.
Phases 1-2 and 4 are still naming-only per that audit.

## Auto-resolution names a lane that must actually serve the frame (2026-08-05)

`Engine2D.detect_best_backend_viable()` promises to commit "only to a PROVABLY
working backend", but its deep probe used to exercise a solid fill and nothing
else — so it was FAIL-OPEN against the render lane's real op set. Measured on
the dual-GPU dev host (TITAN RTX + RTX A6000, Vulkan 1.4):

- `auto` selected **cuda** (its 8x8 fill round-tripped `device_readback`).
- Every real web frame on that lane came back **`source=cpu_fallback handle=0
  identity=0`**. Bisecting the op sequence — clear / fill / sub-blit /
  full-blit / blend-blit all stayed `device_readback`, the **clipped fill**
  flipped it — showed `CudaBackend.set_clip` only mutates the CPU mirror, so
  the next paint takes `_begin_cpu_path`/`_finish_cpu_path` and latches
  `cpu_fallback_used` for the whole surface. Every page with text paints under
  a clip, so on cuda every page was CPU-served.
- `vulkan`/`qualcomm`, the next candidates, served the identical frame
  on-device — and were never reached.

The probe now requires a fill, a **CLIPPED** fill and a `draw_image` blit, all
device-proven, with four disjoint pixel witnesses. Auto now resolves to a lane
whose showcase frame reads back `host_cache_after_device_present` with real
credentials, **bit-identical to the CPU ground truth** (checksum `413538218`,
unique=18, nonbg=5565).

Reading rule for any lane that reports a GPU backend: a resolved lane NAME is
not evidence. Only the readback source is. `resolved=cuda` with
`source=cpu_fallback` is a routing defect, not a host condition.

## Two measurement traps in these lanes (READ BEFORE running or editing)

Both are silent — they produce a plausible wrong answer, not an error. They are
the single most expensive things to rediscover in this campaign.

### 0. A "full GPU offload" suite that silently retargets itself to the CPU

`web_showcase_full_gpu_offload_spec.spl` carried a private
`_executed_render_backend()` that **silently retargeted all 13 examples to the
`"software"` lane** whenever its probe was not `device_readback`. The suite then
printed `13 examples, 0 failures` under a "full GPU offload" title with nothing
in the output disclosing that no pixel had been near a device — and its one
diagnostic field (`probe_source=`) printed EMPTY, because a module-level `var`
written inside an example is not visible when read back (the same trap the
parity gate records; the spec's `_base_px_cache`/`_mutated_px_cache` memos never
worked either). Fixed 2026-08-05: the retarget is gone, the suite runs on the
lane the resolver names, and every example emits exactly one greppable receipt:

```
grep -c '^.showcase-lane. '                -> receipts emitted (expect 13)
grep -c '^.showcase-lane. .*GPU-PROVEN'    -> strict device_readback proofs
grep -c '^.showcase-lane. .*DEVICE-SERVED' -> device-presented frames
grep -c '^.showcase-lane. .*CPU LANE'      -> examples that prove NOTHING
```

**Anchor these.** The closing `[showcase-verdict]` lines name the tokens on
purpose (different prefix, never counted); an unanchored `grep -c 'GPU-PROVEN'`
reads 2 on a run whose true count is 0.

Fail-vs-inconclusive split, deliberately NOT the parity gate's uniform
"inconclusive": a resolver-named **CPU** lane is inconclusive-but-green (genuine
host condition, keeps the suite runnable device-free), while a resolver-named
**GPU** lane that serves a CPU frame is a **hard fail** (`LANE INTEGRITY
FAILURE`) — the resolver broke its own contract.

### 1. `# @exec_limit <N>` — the ONLY way to raise a spec's op cap

`rt_fault_set_execution_limit` called from inside a spec is **INERT**: the
driver reads `SIMPLE_EXECUTION_LIMIT` once at startup
(`src/compiler_rust/driver/src/cli/init.rs:163`), so a spec cannot raise its own
cap in-process. The sanctioned mechanism is the spec-header directive, parsed by
`spec_exec_limit_directive` (`src/app/test_runner_new/test_runner_single.spl:190`)
and forwarded into the child env by the env setup in `main()` (same file,
~line 599):

```
# @exec_limit 2000000000
```

- Plain comment line, anywhere in the file; parser does a raw `find_raw` for the
  literal `"# @exec_limit "` then reads consecutive ASCII digits.
- Non-numeric / absent ⇒ 0 ⇒ no directive.
- **Raise-only**: an already-higher `SIMPLE_EXECUTION_LIMIT` in the environment
  wins; the directive never lowers the cap.
- Live example (and the doc-comment explaining why): `tile_gpu_lane_spec.spl`,
  whose two 600x400 readback + per-tile checksum passes exceed the default
  10M-operation cap.

### 2. Render-budget floor — a tripped budget silently publishes truncated styles

`WEB_RENDER_BUDGET_MS = 10000`
(`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl:81`)
trips under interpreter load and then **silently publishes truncated styles** —
the spec sees a plausible, wrong render, exit 0.

- Sanctioned opt-in: the spec calls
  `simple_web_layout_set_render_budget_floor_ms(900000)`
  (exported at `..._foundation.spl:176`). The setter is **raise-only** (`ms > 0`).
  Scoped-restore counterpart for bounded degraded-retry callers:
  `simple_web_layout_restore_render_budget_floor_ms(ms)` (accepts `>= 0`, so it
  can lower back to "no floor"); read the current floor with
  `simple_web_layout_render_budget_floor_ms()`.
- This is a **calibration knob, not a budget bypass** — the budget still expires
  past the floored deadline.
- **Raising the in-tree default `WEB_RENDER_BUDGET_MS` is forbidden.** Arm the
  floor from the spec instead.
- Live example: `web_showcase_full_gpu_offload_spec.spl` (arms it, 2 call sites).
  In-tree production precedent for the scoped raise/restore pattern:
  `simple_web_layout_engine2d_fast.spl:306`.
- There is also a `SIMPLE_WEB_RENDER_BUDGET_MS` env override read at
  `..._foundation.spl:127`; unset or non-numeric falls back to the default.

## Coverage tooling status

Working `SIMPLE_COVERAGE=1` statement coverage landed as `1a6c1e362a5`
(pure-`.spl` wiring), with the instance-method attribution fix in `d905ebdb7aa`.
Details and the attribution model:
[statement_coverage feature expert](../statement_coverage/skill.md).
Caveat carried by the plan doc: `dom.spl` still measures 1% despite the 38/38
DOM lane exercising it heavily — treat low coverage on a green lane as an
attribution question first.

## Adjacent tooling landed with this campaign

- `src/app/clean/main.spl` — `simple clean`, manual + auto temp/cache cleanup.
  Auto mode is **opt-in via `SIMPLE_AUTO_CLEAN=1`** (runs at `simple build`
  start; `SIMPLE_CACHE_MAX_GB` default 20).

## Vulkan rect batch + pinned-shader workflow (2026-09-11)

- Batch API: `Engine2D.draw_rect_list_filled(rects: [i32], colors: [u32])` —
  frozen host layout `rects[4k..4k+4]`, `colors[k]`. At `n >= 2` it becomes ONE
  compute dispatch reading a GPU storage buffer; below that, and on any decline,
  the F4 per-rect host loop runs with identical pixels.
  Observables: `vulkan_last_frame_dispatch_count()` (rect/framebuffer lanes only,
  read AFTER finalize) and `vulkan_rect_batch_fallback_reason()` (`""` = installed).
- Pinned shader: edit `shaders/rect_batch.comp`, then ALWAYS
  `sh scripts/tool/gen-rect-batch-spirv.shs`, then
  `sh scripts/check/check-rect-batch-spirv-pinned.shs` (fail-closed; no
  glslangValidator = ERROR). The `.spv` is never committed. The pin catches a
  stale blob, NOT a semantic change — the painter-order example in
  `backend_vulkan_rect_batch_edges_spec.spl` is what catches that.
- Open, wall clock is FLAT at 900x760/64 (6.663 -> 6.686 ms): `copy_to_buffer`
  is its OWN blocking queue submit (`vulkan/buffer.rs:338`), so the lane is not
  one submit per frame; host `[u8]` packing has no typed-upload alternative; the
  per-pixel walk is O(bbox x N). All three in
  `doc/08_tracking/bug/vulkan_draw_rect_interpreter_overhead_2026-09-11.md`.

## CPU<->GPU boundary fix campaign (F1/F2, same day)

Plan: `doc/03_plan/ui/gpu_offload/web_vulkan_cpu_gpu_boundary_fix_plan_2026-09-11.md`;
census: `doc/01_research/ui/gpu_offload/cpu_gpu_boundary_census_2026-09-11.md`.

- **Device verification pattern**: `SIMPLE_EXECUTION_MODE=interpreter
  SIMPLE_TIMEOUT_SECONDS=0 bin/release/aarch64-apple-darwin-macho/simple run
  <spec>` (resolved triple for the host), reading
  `observed_device_submit_count` / `observed_device_fence_count` after
  `finalize_compute_frame_no_readback()` — never a static/no-op count.
- **Zero-length-readback vs pixel-mismatch lesson**: `vk2d_bench.spl` used to
  print a hardcoded `status=blocked reason=unconditional-submit-wait` string
  regardless of backend behaviour (fixed:
  `doc/08_tracking/bug/vk2d_bench_hardcoded_block_reason_2026-09-11.md`; now
  `vk2d_verdict()` computes the verdict from real fence-completion counts). A
  run with 0 frames or a fence/frame mismatch is `status=blocked
  reason=zero-frames`/`multi-submit-per-frame:N` — never silently reported as
  a passing pixel comparison. That is distinct from a genuine pixel MISMATCH
  (comparator ran, values disagree): a zero-length readback is an evidence
  gap, not a correctness verdict, and must never be laundered into `passed`.
- **F1** (route-key re-arm): `_web_draw_ir_key` was keyed on a per-mutation
  counter so the sampler route re-armed on every composition generation even
  when geometry didn't change — fixed, see
  `doc/08_tracking/bug/web_draw_ir_sampler_rearms_on_generation_2026-09-11.md`.
- **F2** (mid-frame fences): `draw_text_bg` used to fence-wait before every
  background band on a mistaken pipeline-barrier premise (21 submits/21
  fences for 300 rects + 20 bands); `rt_vulkan_dispatch` already inserts a
  `VkMemoryBarrier` on every dispatch, so the extra fence was redundant and is
  now deleted (1 submit/1 fence) — see
  `doc/08_tracking/bug/vulkan_backend_midframe_fence_and_clip_text_fallback_2026-09-11.md`.
- **Runtime-owned blockers still open** (not fixable in pure Simple without a
  runtime/SFFI change) — read these two bug docs directly rather than trusting
  a paraphrase here: `doc/08_tracking/bug/engine2d_vulkan_pixels_upload_slower_than_cpu_2026-09-11.md`
  and `doc/08_tracking/bug/indexed_field_assignment_unsupported_2026-09-11.md`.

## R1 round 2 — root cause, opt-in typed upload, wall clock (2026-09-11)

- **R1 root cause found**: a pooled `Engine2D` resumed the next frame with
  `pending_compute_command` still naming the PREVIOUS frame's already-freed
  command buffer, so `rt_vulkan_bind_pipeline` refused it and the backend
  latched `cpu_fallback`. Fix: `slot.engine.vulkan_discard_stale_pending_compute()`
  at the pool acquire site. Same family as
  `doc/08_tracking/bug/class_instances_copy_on_bind_and_for_loop_drops_mutation_2026-08-04.md`
  (class-field write-back dropped on bind) — the fix only clears the
  pending-compute fields it knows about, so any OTHER `VulkanBackend` field can
  rewind the same way and would not be caught.
- Route authorization is now proven correct by `probe_authorize.spl`, but the
  real page-render path still reports `timing-unavailable` — proof and use
  diverge, do not conflate them.
- New typed-upload lane is opt-in: `SIMPLE_VK_RECT_UPLOAD=u32`. WHY opt-in, not
  default: an unknown extern is an uncatchable interpreter abort, so the fast
  path must not run unless explicitly requested.
- A fresh seed for this lane needs `--features vulkan,vulkan-graphics`.
- Honest wall clock: 900x760 steady-state 7.2s GPU vs 7.9s CPU; 4K cold start
  87.7s. The bottleneck is interpreter-bound Draw IR/layout, not raster —
  do not read the GPU win as proof the raster path is fast end-to-end.

## Update Rule

When the project process creates or changes research, requirements,
architecture, design, tests, implementation, verification, or release artifacts
for this feature, update this skill with the new links, current inventory
numbers, and handoff notes BEFORE committing.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
