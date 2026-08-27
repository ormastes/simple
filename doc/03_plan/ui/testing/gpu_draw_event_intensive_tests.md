# Intensive GPU / Drawing / Event Test Plan

**Status:** planning (2026-07-06). Goal: near-100% branch coverage of GPU
processing, 2D drawing, and UI event handling across backend combinations, via
SSpec integration + environmental tests. Shared parameterized bodies + a small
set of system-specific check points. Plus one new debug-log feature and the
UI→drawing fixes that the coverage exposes.

Research inputs (scratchpad, this session):
`research_gpu_processing.md`, `research_drawing.md`, `research_events_scheduler.md`.

## 1. Architecture as it actually is (honest baseline)

| Area | Reality | Absolute oracle |
|------|---------|-----------------|
| GPU compute (`std.compute`/ExecTarget) | **Payload-gated simulation** — computes CPU reference, *reports* GPU provenance; not wired to real device launches | value == CPU oracle in both branches + provenance flag |
| Kernel emission `gpu_portable_compute.spl:455-461` | Real, host-portable: one `match`, per-backend markers | source contains marker (CUDA `__global__`, HIP/OpenCL `__kernel`, Metal `[[thread_position_in_grid]]`, WGSL `@compute`) |
| Font/Draw-IR offload | Real per-backend sessions + checksum readback; **real device only proven on Metal** | `gpu_returned==1`/`cpu_fallback==0` w/ matching payload; reject on corrupt checksum |
| GPU job/event scheduler | Real state machine `host_gpu_event_queue.spl` (EMPTY→QUEUED→SUBMITTED→COMPLETED); dispatch `draw_ir_runtime_queue.spl:100-125` | pure-model transitions + `rt_host_gpu_queue_*` round-trip (backend-handle + payload-hash + `schema=simple-draw-ir-v2`) |
| 2D drawing backends | CPU/SW honest-complete; Metal real (macOS, `clip` no-op); Vulkan 6 real SPIR-V but **line/circle_outline/rounded_rect = validated EMPTY shader**; DirectX honest CPU-emu; WebGPU/Intel/OpenGL fake-or-crash | `read_pixels()`→`encode_ppm_p6` framebuffer download |
| UI events | CPU-side: `event.spl` → `widget_hit.spl` hit-test → reducers; GPU layer only *classifies* coarse batches (semantic events stay host) | reducer `(state,event)->state` + hit-test topmost-wins |
| `std.diag` | Complete + tested, **wired into zero GPU/event paths** | `dbg_*` accessor emission counts |

**False-green history** (must avoid): software-vs-itself "GPU parity", scalar
paths claiming `has_neon`, memorized pixel tables, all-black==all-black. Every
parity assertion pairs with an absolute oracle or proof-the-producer-ran flag.

## 2. New feature: GPU scheduler debug-log (`std.diag` instrumentation)

Minimal, honest observability (no fabricated metrics). Plug-in points:
- `host_gpu_event_queue.spl` transitions: `dbg_stage("gpu_queue", <state>)` +
  `dbg_event_hop(batch_id, <hop>, detail)` at schedule/submit/complete/drain.
- `draw_ir_runtime_queue.spl:100-125`: same at schedule(:106)/submit(:119)/complete(:123).
- `dbg_count` on queue depth / dispatch / completion; `dbg_summary_dump` accessor.
- **Always-on** `dbg_provenance("gpu_batched", actual, ctx)` at dispatch — must
  never log the fabricated `estimated_ms` (removed by the honesty fix).
- Gate: reuse `SIMPLE_DIAG=events,stage` (no new facet). Zero-overhead when off.

## 3. Test matrix

**Combinations.** Processing {Vulkan, Metal, CUDA, HIP} × Drawing {Metal,
Vulkan, DirectX}. Each cell runs the SHARED body; system-specific checkpoints
gate on a device-availability probe and record `host-unavailable` with a
concrete reason (fail-closed — never silent `skip()`).

**Shared (portable — runs on Linux CI, the bulk of branch coverage):**
1. Kernel emission markers, per backend (+ reject/unknown-backend branch).
2. Offload payload-gating: no-payload→CPU, matching→GPU, corrupt→reject — per backend.
3. ExecTarget suggest (falls back, `resolved=true`) vs require-absent (fail-closed `resolved=false`→exit 70).
4. Scheduler state machine: every transition + dispatch-failure branch; diag emission asserted.
5. CPU/SW per-primitive readback: each primitive → known fixed-point pixel (fill center==color, background==bg).
6. Draw-IR item dispatch (post HTML/CSS fix): rect/border/gradient/shadow/image each reach its primitive, not a flat fill.
7. Event hit-test semantics: topmost/last-wins, half-open edges, miss, overlap, hover-clear; dispatch router branches.
8. CPU↔GPU message passing: `rt_host_gpu_queue_*` round-trip — payload-hash match, schema validate, receipt (`committed_on_host`), corrupt-payload reject.

**System-specific check points (record availability honestly):**
- Metal device draw+readback (macOS); Vulkan device draw+readback (Linux/Win w/ device);
  CUDA/HIP real compute dispatch; DirectX (Windows). Each: probe → run real device path OR `host-unavailable(reason)`.

## 4. UI→drawing fixes (exposed by coverage)

- **Vulkan empty-shader trio** (`backend_vulkan_spirv.spl:169-209`): import the
  existing real line/circle_outline/rounded_rect shaders, or mark honestly
  no-op + bug if not contained. Prefer the real wiring.
- **Metal `clip` no-op** (`metal_session/backend :389`): implement scissor clip or mark honest.
- **Draw-IR flat-fill collapse** (`draw_ir_adv.spl:182/264`): the HTML/CSS
  executor fix makes RECT boxes render borders/gradients/radius/shadow; the
  item-dispatch spec (shared #6) is its gate. (`<img>` blocked — see bug
  `engine2d_draw_ir_image_path_no_resolver_2026-07-06.md`.)

## 5. File layout

- Shared helper: `test/helpers/gpu_draw_event_shared.spl` (parameterized scenario
  fns + device-availability probe + `read_pixels`→PPM oracle wrapper).
- Emission/payload/compute: `test/02_integration/lib/gpu/*_spec.spl`.
- Scheduler + message passing: `test/02_integration/lib/gpu/host_gpu_queue_*_spec.spl`.
- Drawing per-combination: `test/03_system/gui/draw_backend_matrix/*_spec.spl`.
- Events: `test/01_unit/lib/common/ui/event_*_spec.spl`.
- Feature diag emission: alongside the scheduler spec.
- Mirror manuals to `doc/06_spec/...` via `bin/simple spipe-docgen ... --no-index` (`0 stubs`).

## 6. Execution — agent teams

Lanes edit disjoint file sets; run per-spec verification (grep for `✗`, not just
`PASS` — interpreter greenwash). Import `std.spec.*`, `std.io_runtime`/`app.io`
facades (no raw `rt_*` in specs), `std.diag` for instrumentation. **Commit each
lane's files atomically on completion** (shared working copy is swept by parallel
sessions — uncommitted work is clobbered).

- **Lane F** — scheduler debug-log feature + its emission spec.
- **Lane V** — Vulkan trio + Metal clip drawing fixes.
- **Lane S** — shared helper + emission/payload/scheduler/message-passing portable specs.
- **Lane P** — per-combination drawing specs (system-specific checkpoints).
- **Lane E** — event hit-test/router/CPU↔GPU specs.

Verify gate: no false-green (absolute oracle present), `spipe-docgen` `0 stubs`,
docs freshness (guides/tldr updated where behavior changed).
