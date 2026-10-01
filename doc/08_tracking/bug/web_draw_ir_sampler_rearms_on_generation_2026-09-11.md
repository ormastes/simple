# Web Draw IR route sampler re-arms on every composition generation (2026-09-11)

Status: FIXED (group F1 of
`doc/03_plan/ui/gpu_offload/web_vulkan_cpu_gpu_boundary_fix_plan_2026-09-11.md`;
census rows R2, R3, R13 of
`doc/01_research/ui/gpu_offload/cpu_gpu_boundary_census_2026-09-11.md`).

All file:line references are post-fix unless marked "was".

## Defects

### D1 — the route key carried a per-mutation counter

`_web_draw_ir_key` (was `src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl:400-411`)
built the route-cache key from `"draw-ir-generation=" + composition.generation`,
falling back to `"draw-ir-sha256=" + sha256_text(draw_ir_to_sdn(composition))`
when the generation was unassigned.

`DrawIrComposition.generation` (`src/lib/common/ui/draw_ir.spl:118`) is a
serial revision handed out per composition VALUE — "rebuilding identical
content deliberately gets a new generation". So a scroll, an animation tick and
a tab switch each produced a brand-new key, a brand-new `_WebDrawIrRouteState`,
and a fresh 3-frame A/B sampling phase on a device that had already been proven
pixel-exact. The generation-0 fallback was worse: it serialized the whole scene
to SDN and SHA-256'd it, per frame.

Fix: `web_draw_ir_route_key` (`:414`) takes `document_identity`, extent,
backend and `device_token`. There is no parameter through which a per-frame
counter can reach it, and neither the serialized scene nor any hash of it is
retained. `_web_draw_ir_document_identity` (`:405`) supplies
`composition_id;scene_key;backend_target`.

Retained PIXEL reuse is unchanged and still exact:
`_web_draw_ir_cached_frame_reusable` (`:815`) still requires producer
generation + parked owner token + extent, so the looser key cannot put a stale
frame on screen.

### D2 — every steady frame compared 8.3M pixels

The steady offload branch (was `:806-810`) ran
`_web_draw_ir_pixels_equal(gpu.readback.pixels, state.validated_pixels)` — one
interpreted loop iteration per pixel, 8,294,400 at 3840x2160 — on every frame
that reached it.

Fix (`:895-918`): the branch now splits on the scene revision.

- **Same revision** — a re-validation of a frame already held. Compare the
  device-side `Engine2DReadback.checksum` (`backend_vulkan.spl:1613`, produced
  by `vulkan_sffi_readback_u32_into`) against `state.validated_checksum`
  retained at validation. One `i64`, zero scans. The exact compare remains the
  fallback when either checksum is 0, so correctness never rests on the
  checksum merely being present.
- **New revision** — no oracle for this content exists and none is rendered. A
  device already proven pixel-exact for this key, still returning a proven
  readback with zero skipped commands, is the authority; the retained frame is
  re-anchored to it.

The CPU oracle route's readback carries no checksum, so at validation
(`:1028-1042`) the checksum is taken from the device readback when available and
otherwise computed ONCE by `web_draw_ir_device_checksum` (`:680`), the CPU twin
of the identical fold `acc = (acc + px) % 2147483647` from `acc = 0` — verified
against `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl:1015` and
`src/compiler_rust/runtime/src/vulkan_graphics_runtime_buffer.rs:464`. Never
per frame.

The fold is not Vulkan-specific: the generic constructor
`engine2d_readback_with_identity`
(`src/lib/gc_async_mut/gpu/engine2d/backend.spl:17-23`), which is what the
Metal and CPU paths go through, computes the byte-identical
`(checksum + pixels[i]) % 2147483647`. And the comparison is device-vs-device
in any case — the CPU twin is consulted only when the device reports 0 — so the
same-revision check would stay sound even if a future backend chose a different
fold.

**Known weakening, stated rather than hidden:** that fold is order-independent
(a sum), so it is a weaker check than the exact compare it replaces on the
same-revision path. It is the check the DEVICE already computes for free. The
exact compare still governs the sampling phase, which is what establishes
`pixels_match` in the first place.

### D3 — a lost timing margin diverted a proven device to software

Steady frames took the `else` branch (was `:855`) and ran
`_web_draw_ir_oracle_route` — the full software raster — whenever
`evidence.should_offload` was false. `should_offload` additionally requires the
GPU to have beaten the upload path by a strict 100us margin
(`web_draw_ir_gpu_route_policy_spec.spl:63-71`), so a proven, pixel-exact
device that merely lost the margin test rasterized every later frame in
software.

Fix: `_web_draw_ir_device_authorized` (`:840`) — `pixels_match and
gpu_device_proven and commands_complete` — is what authorizes the GPU route at
`:871` and at the validation retention at `:1029`. The margin verdict is still
published in `state.evidence.should_offload`, as evidence only. The oracle
branch (`:965`) is now reached only when the device is genuinely unauthorized.

### D4 — engine parking

No defect found. The Draw IR lane already acquires from
`_web_fast_engine_slots` (`:531` -> `_web_fast_engine_acquire`, `:282`) and the
only `shutdown()` calls are slot eviction/teardown (`:296`, `:321`, `:327`,
`:337`). `owner_generation` is stable across a reuse, so the device token in
the new key does not flap. Unchanged.

**One bounded cost the new key introduces, stated rather than hidden:** frame 0
runs before any engine is parked, so its device token is `""` and it keys a
state that nothing ever revisits once the engine is parked and the token turns
non-empty. That orphan is bounded by `WEB_DRAW_IR_ROUTE_CACHE_MAX` (16) and by
the LRU eviction in `_web_draw_ir_state`; it costs one extra sampling phase per
cold start, not per frame.

## Evidence

Binaries (bracketed): seed
`src/compiler_rust/target/bootstrap/simple` 130402384 bytes mtime 1788606093;
device lane `bin/release/aarch64-apple-darwin-macho/simple` 26264696 bytes
mtime 1788766698.

Specs (run with
`src/compiler_rust/target/bootstrap/simple run <spec>`; verdict read from the
`N examples, M failures` line):

- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_draw_ir_route_key_generation_independence_spec.spl`
  — reproduces D1 and the steady-frame re-sample it caused (NOT D2's
  checksum branch, which is unreachable without an authorized device):
  `2 examples, 0 failures`.
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_draw_ir_route_key_rearm_axes_spec.spl`
  — generalization (device token / extent / document identity each re-arm, as
  key inequality AND as an observed re-sample; margin never authorizes;
  checksum fold oracle): `7 examples, 0 failures`.

Absolute oracles, not parity: a 16x16 fixture renders `0xFFFF0000` at (2,2) and
`0xFFFFFFFF` at (12,12), folding to checksum `2143289663`.

### Before / after — `_web_draw_ir_pixels_equal` calls per steady frame

Measured by `web_draw_ir_pixels_equal_call_count()` (`:637`), a counter added
inside `_web_draw_ir_pixels_equal` itself. Six frames of the 16x16 fixture,
bumping only `generation`:

| | sampling (frames 1-3) | each steady frame | total after 6 frames |
|---|---|---|---|
| before (see note) | 6 | 2 | 12 |
| after | 6 | **0** | 6 |

Note on the "before" row: it was measured through the SABOTAGE arm, which
restores generation-in-key and changes nothing else. The pre-change tree had no
counter at all — `web_draw_ir_pixels_equal_call_count()` is added by this
change — so a literal pre-change measurement was not available. The sabotage
arm is the closest faithful stand-in and its diff is one expression.

### Sabotage

Reverting D1 alone — re-appending the generation to the document identity in
`_web_draw_ir_key`, changing nothing else — turns the generation-independence
spec RED with exactly the defect's signature:

```
✗ gives two compositions differing only in generation the same key
  expected 49:html-layout;simple-web-html-layout;cpu;SABOTAGE=1;16;16;0:8:software0:0:0:0:
    to equal 49:html-layout;simple-web-html-layout;cpu;SABOTAGE=2;16;16;0:8:software0:0:0:0:
✗ performs zero full-surface pixel compares while generation bumps
  expected 12 to equal 6
2 examples, 2 failures
```

The generalization spec's behavioural case bites on the same sabotage:

```
✗ re-samples on a new extent and a new document, not on a new frame
  expected 12 to equal 10
7 examples, 1 failure
```

Restored: `2 examples, 0 failures` and `7 examples, 0 failures`.

### Neighbour specs

- `web_draw_ir_gpu_route_policy_spec.spl` — `5 examples, 0 failures`, unchanged.
- `web_draw_ir_route_key_memory_spec.spl` — pinned the SUPERSEDED contract (it
  required `draw-ir-sha256=` to be present in the source). Its single example
  was rewritten to pin the new contract — document identity and device token
  present, `draw-ir-sha256=`/`draw-ir-generation=`/the DJB2 and raw-SDN forms
  all absent — and now reports `1 example, 0 failures`.

### Device lane (900x760, backend `vulkan`, Apple M4)

Run with
`SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0
bin/release/aarch64-apple-darwin-macho/simple run <probe>`, 8 frames of a
684,000-pixel surface bumping only `generation`:

| frame | `pixels_equal` calls | route submissions | engines created | engines reused | reason |
|---|---|---|---|---|---|
| 0 | 2 | 2 | 2 | 0 | timing-unavailable |
| 1 | 4 | 4 | 2 | 2 | timing-unavailable |
| 2 | 4 | 6 | 3 | 3 | pixel-mismatch |
| 3-7 | **4** | +1/frame | **3** | +1/frame | pixel-mismatch |

Three things this shows and one it does not:

- **Steady frames run zero full-surface compares at 684,000 px.** The counter
  is frozen at 4 from frame 2 onward while the route keeps being consulted.
- **The engine is parked.** `engines_created` freezes at 3 while
  `engines_reused` rises one per frame — no per-frame `shutdown()`.
- **The correctness gate still governs.** This device disagreed with the
  software oracle during sampling (`reason=pixel-mismatch`), so
  `_web_draw_ir_device_authorized` is false and the steady frames correctly
  take the oracle branch. D3's fix does not paper over a wrong device; it only
  removes the *margin* as grounds for that diversion.
- **It does NOT exercise D2's device-checksum comparison**, precisely because
  the device is unauthorized here. See below.

The `pixel-mismatch` verdict is a pre-existing, separate defect of the Vulkan
web lane on this host. That it is not introduced by this change holds **by
construction, verifiable from the diff**: the sampling block that computes
`state.pixels_match` (`:1003-1009`) is untouched, and every line this change
adds sits on the `state.complete` steady path that only runs afterwards. It is
not diagnosed here.

Two notes for whoever owns the wider plan, neither an F1 item:

1. `reason=pixel-mismatch` blocks device-side verification of the AUTHORIZED
   branch for every F-group in the plan, not just F1 — on this host no Vulkan
   route ever becomes authorized, so no amount of F-group work can be shown
   running on the device here. That is the single unblock condition for the
   plan's Vulkan evidence. Probe output:
   `<scratchpad>/vk1.txt` (8 frames, 900x760).
2. `engines_created` steps 2 -> 3 at frame 2, exactly where the mismatch is
   latched — one discard + recreate during sampling. Steady frames are clean
   (frozen at 3). Not diagnosed, not F1.

### Why the single-render `web_render_page_ppm` timing is not the F1 metric

`simple_web_render_html_to_pixels_with_engine2d_backend` does reach this route
(`simple_web_renderer.spl:98` -> `:46` ->
`simple_web_layout_render_html_pixels_engine2d` -> `_web_draw_ir_choose_route`
at `:1107`), so the entry is on-path. But a single-render process renders
exactly ONE frame, which is frame 0 — a cold A/B sampling frame. Every defect
fixed here is about the SECOND and later frames of a process. F1 therefore
cannot move that number, by construction, and a flat wall-clock on it is the
expected result rather than evidence of no effect.

**It was attempted and did NOT complete.** A copy of
`examples/06_io/ui/web_render_page_ppm.spl` with the backend switched to
`vulkan`, run at the default 900x760 on the macho binary under
`SIMPLE_EXECUTION_MODE=interpreter`, was still running after ~25 minutes and
was killed before it wrote its PPM. So there is **no after-number to compare
against the 19.85s baseline** — that comparison is unmeasured here, not
measured-and-flat. Given the ~60s/frame the 8-frame probe showed at this extent
under the same binary and mode, the 19.85s baseline was probably taken under a
different execution mode or backend; that was not established and should not be
assumed.

The measurement that does show the change is the 8-frame device probe above:
route submissions fall from two per steady frame (gpu + fallback upload) to
one, whole-surface compares per steady frame fall from two to zero at 684,000
px, and `engines_created` stays frozen while `engines_reused` rises per frame.

## Not verified on this Mac

- **Nothing here required faking a device.** Both specs are absolute-oracle
  software-path tests and discriminate without a GPU, because the sampling
  phase's two exact compares per frame versus a steady frame's zero is
  observable with no device at all.
- **The device-checksum path itself** (D2's same-revision branch reading a
  non-zero `Engine2DReadback.checksum`) is exercised only when a real Vulkan
  device returns `source == "device_readback"`. Unblock condition: a run of
  `test/05_perf/web_render_chrome/web_draw_ir_gpu_route_device_measured_spec.spl`
  on a host where `_web_draw_ir_proven` holds, asserting the steady frames
  report `web_draw_ir_pixels_equal_call_count() == 6` (sampling only) while
  `web_draw_ir_gpu_route_canonical_submission_count()` keeps rising.
- **The order-independence weakening of D2** is not exercised by any spec: no
  fixture currently produces two distinct surfaces with equal pixel sums. If
  the same-revision path is ever relied on for more than re-validation of an
  already-proven route, that fixture must be built first.
