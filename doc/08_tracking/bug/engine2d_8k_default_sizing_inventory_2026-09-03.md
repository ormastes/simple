# Inventory: resolution-sensitive defaults / caps in the 2D + GPU lane (8K-first audit)

- **Date:** 2026-09-03
- **Directive:** two first-class default targets — 8K screen 7680x4320 (33.2 Mpx,
  132,710,400 B) and square 8K 8192x8192 (67.1 Mpx, 268,435,456 B). Lower and
  higher resolutions must keep working; no hard upper bound may be introduced.
- **Policy source of truth:** `config/graphics/resolution_targets.sdn`
- **Related:** `doc/02_requirements/nfr/engine2d_vulkan_2d_perf.md` (NFR-2DP-004),
  `doc/08_tracking/bug/engine2d_2d_perf_bug_register_2026-09-03.md`

## A. CORRECTNESS — device-limit breaches and silent fallbacks at 8K

### A1. 1-D linearized compute dispatch exceeds the Vulkan spec-minimum `maxComputeWorkGroupCount` (CORRECTNESS)

| site | group math | 800x600 | 3840x2160 | 7680x4320 | 8192x8192 |
|---|---|---|---|---|---|
| `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:777` (`clear`) | `(w*h + 255) / 256`, dispatched as `(N,1,1)` | 1,875 | 32,400 | **129,600** | **262,144** |

Vulkan's *required limits* table guarantees `maxComputeWorkGroupCount` of only
**65,535** per dimension. The clear path exceeds that from ~7680x4320 upward.
**Nothing in the tree queries
`maxComputeWorkGroupCount`** — `/usr/bin/grep -rn maxComputeWorkGroupCount
src/compiler_rust/runtime/src` returns nothing; the only device limit read
anywhere is `max_push_constants_size` (`vulkan/device.rs:366`). `rt_vulkan_dispatch`
(`vulkan_graphics_runtime_compute.rs:465,477`) casts `i64 -> u32` with a bare
`as u32` and validates nothing.

It runs today only because MoltenVK/Metal's per-dimension limit is far above the
spec floor. On a conformant desktop Vulkan device at the spec minimum this is a
validation error / undefined behaviour, i.e. a wrong-pixels or device-loss class
bug that no gate would catch on this machine.

Every *other* dispatch site in `backend_vulkan.spl` (rect, filled rect, line,
blit, image — `:792,793,823,824,859,903,904,935,936,942,943`) already uses 2-D
groups `((w+15)/16, (h+15)/16)`, which at 8192 is 512 per dimension. The clear
path is the outlier.

**Font path — checked and NOT a live breach; recorded so it is not re-raised.**
`backend_vulkan_font.spl:85` uses a coarser `(pixel_count + 63) / 64`, but its
`pixel_count` is a single **glyph quad's** area, not the framebuffer: `:708`
computes `q.width * q.height` per quad and `:553-556` takes the max quad area
across the batch. A quad would have to exceed 4,194,240 px (~2048x2048 for one
glyph) to reach 65,535 groups, so this does not trip at any realistic font size
and does not scale with surface resolution. Two residual unchecked
linearizations, noted but not blocking: the Y dimension at `:558` is
`batch.quads.len()`, so a text run above 65,535 glyphs would exceed the floor,
and neither call site validates against a queried limit.

### A2. `maxStorageBufferRange` is never queried; square 8K is 2x the spec minimum (CORRECTNESS)

Vulkan's required minimum `maxStorageBufferRange` is **134,217,728 B (128 MiB)**.

- 7680x4320 framebuffer = 132,710,400 B — fits, with ~1% headroom.
- **8192x8192 framebuffer = 268,435,456 B — 2.0x the spec floor.**

No code queries the limit (see A1 grep). A device at the floor would fail to bind
the framebuffer as a storage buffer, and the failure path in this lane is
`mark_cpu_fallback(...)` — i.e. a *silent* degradation to the CPU lane rather
than a diagnosable error. Not observed on the M4/MoltenVK bench (Metal's limit is
far higher), but unchecked.

### A3. Damage readback silently falls back to a FULL-frame readback at 8K (CORRECTNESS-adjacent, large cliff)

`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:1358-1361`:

```
if rh > 16384 - total_rows:
    self.frame_full_fallback = true
    self.frame_fallback_reason = "damage-transfer-row-cap"
    return self._refresh_host_full()
```

The literal `16384` mirrors `MAX_STRIDED_TRANSFER_ROWS`
(`src/compiler_rust/runtime/src/vulkan/buffer.rs:10`), enforced again in Rust at
`:105` and `:132` (`total_rows > MAX_STRIDED_TRANSFER_ROWS -> BufferTooSmall`).

The cap is on **summed rows across all damage regions**, so its severity scales
inversely with surface height:

| height | full-height damage rects admitted before the cap trips |
|---|---|
| 600 | 27 |
| 1080 | 15 |
| 2160 | 7 |
| 4320 | 3 |
| 8192 | **2** |

The production compositor asks for up to 256 damage rects
(`src/os/compositor/compositor_engine2d.spl:410,471`). At 8192 rows, any damage
set averaging >64 rows per rect trips the cap and downgrades an incremental
readback into a full 268 MB one. This is the single clearest "tuned for a small
framebuffer" constant in the lane: at 800x600 the cap is generous, at 8K it is
effectively always exceeded.

The companion cap `regions.len() > 256` (`vulkan/buffer.rs:121`) exactly equals
the compositor's request, so it does not trip today — but it has zero headroom.

### A4. Full-screen alpha rect silently drops to a 268 MB host blend at 8K

`backend_vulkan.spl:796-807`: `draw_rect_filled` with `color_a(color) < 255`
allocates `[color; w * h]` on the host and routes through `draw_image_blend`.
At 8192x8192 that is a 67,108,864-element (268 MB) host array **per call**. The
guard at `:802` (`pixel_count > 2147483647 -> mark_cpu_fallback`) never fires at
our targets, so the expensive path is taken silently. Same shape at `:808-816`
when a stencil mask is active.

### A5. Stale comment (harmless, but now wrong)

`src/compiler_rust/runtime/src/vulkan_graphics_runtime_buffer.rs:529` still says
"MAX_RAW_TRANSFER_BYTES caps the count at 2^26 pixels". Since the cap was raised
to 2 GiB the true bound is 2^29 pixels. The u128-cannot-overflow argument still
holds; the number does not.

## B. Caps and hard upper bounds

| file:line | constant | value | 8K-safe? | note |
|---|---|---|---|---|
| `src/compiler_rust/runtime/src/vulkan_graphics_runtime_buffer.rs:23` | `MAX_RAW_TRANSFER_BYTES` | `2 * 1024^3` (2 GiB) | **yes** | already 8K-first; its own tests (`:790-798`) assert 7680x4320, 8192x8192, double-buffered 8K, and 16384x16384. No change needed. |
| `src/compiler_rust/runtime/src/vulkan/buffer.rs:10` | `MAX_STRIDED_TRANSFER_ROWS` | `16_384` | **borderline** | admits a 16384-row surface exactly, rejects anything taller — a hard upper bound, which the directive forbids. See A3 for the summed-rows problem. |
| `src/compiler_rust/runtime/src/vulkan/buffer.rs:121` | region count | `> 256` rejected | **zero headroom** | equals the compositor's request exactly. |
| `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:1358` | damage row cap literal | `16384` | **no** | duplicated magic number; see A3. |
| `src/lib/gc_async_mut/gpu/engine2d/backend_baremetal.spl:42` | `BM_MAX_DRAW_DIM` | `20000` | yes for both targets | hard upper bound: rejects any draw dimension above 20000, so a 32768-wide surface is refused (`:329,:351`). Violates "no hard upper bound". |
| `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:335` | `GPU_LUT_MAX_ENTRIES` | `65536` | yes | palette LUT size, not resolution-scaled. Correctly resolution-independent. |
| `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl:1507-1509` | damage-rect fallback cap | `16` when `max_rects <= 0` | **no** | over-cap the damage set "collapses to its single bound" (`:1604-1608`) = a full-surface copy. 16 rects is a 800x600-era default; at 8K the collapse is a 268 MB memcpy. |

## C. Default resolutions

| file:line | default | owner | verdict |
|---|---|---|---|
| `src/app/ui_showcase/hosts/main_2d_vulkan.spl:23-24` | 320x240 | **this agent** | small-framebuffer-tuned; GPU-backed, so an 8K default is *feasible* but unverified here (see §E). |
| `src/app/ui_showcase/hosts/main_2d_gpu.spl:32-33` | 320x240 | **this agent** | same. |
| `src/app/ui_showcase/hosts/main_2d_engine.spl:22-23` | 320x240 | **this agent** | same. |
| `src/app/ui_showcase/hosts/main_2d.spl:36-37` | 320x240 | **this agent** | the in-file comment at `:32-33` records *why*: the surface is allocated one `push` per pixel and painted per command in-language. The small default is a **symptom**; the defect is the per-pixel interpreted allocation path. Raising this default without fixing that path makes the host unusable. |
| `src/app/ui_showcase/hosts/main_web.spl:27-28` | 800x600 | **this agent** | small-framebuffer-tuned. |
| `src/app/ui_showcase/hosts/main_gui.spl:24-25` | `WIDGET_SHOWCASE_WINDOW_W/H` | this agent (indirect) | window-manager geometry, not a framebuffer target; correctly not resolution-swept. |
| `test/05_perf/bench/vulkan_2d_c/feature_showcase.spl:24-25` | `const W: i32 = 800`, `const H: i32 = 600` | **other agent** | compile-time constants, not env-overridable — the bench cannot be swept at all without an edit. |
| `scripts/check/check-ui-showcase-exact-backend-matrix.shs:73` | `SIMPLE_SHOWCASE_W=320` | this agent | the **only** gate that pins the resolution explicitly; every other spec takes the host default. |

`src/lib/gc_async_mut/gpu/engine2d/engine.spl` — **explicitly clean**: its only
occurrences of `800`/`600` are docstring examples (`:12`, `:273`). It declares no
resolution-sensitive constant, cap, chunk size or threshold. Nothing to change.

## D. Integer-width audit on pixel and byte counts

Checked, all safe at both targets, reported for completeness:

- `src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl:883`
  `vulkan_sffi_readback_u32_into(dest, handle, pixel_count: i32, offset: i64)` —
  `i32` **pixel** count. 8192x8192 = 67,108,864 fits. The implied ceiling is
  ~46340x46340; above that this signature silently truncates. Not a bug at our
  targets, but it is a latent hard bound in a type.
- `src/compiler_rust/runtime/src/vulkan_graphics_runtime_buffer.rs:485`
  `pixel_count.checked_mul(4)` is on an **`i64`** — the bytes product
  (268,435,456) is computed in 64-bit and checked. Correct.
- `backend_vulkan.spl:1373` `expected_pixels.to_i32()` — bounded by the row cap
  (A3), so it cannot exceed `i32`. Safe by construction, fragile by inspection.
- `backend_vulkan.spl:776,799,816` all use `_i64(w) * _i64(h)` — deliberately
  widened before multiplying. Correct pattern; the rest of the lane should match it.

No i32 *byte*-count arithmetic was found on the framebuffer path. The 268,435,456 B
figure never reaches an `i32` variable.

## E. Why no default was flipped in this pass

A runnable lane **does** exist in this worktree and was found and used:
`src/compiler_rust/target/vulkan/release/simple` (39 MB, built today with the
`vulkan` feature) answers `--version` and runs `.spl` sources. It is the binary
`scripts/check/check-engine2d-backend-parity.shs:32` invokes as `$SEED`. Probed
and ruled out first: `bin/simple` does not exist; `bin/release/simple` is a
2 KB wrapper that resolves `bin/release/x86_64-unknown-linux-gnu/simple` and
exits with `deployed Simple runtime failed its bounded identity probe` on this
arm64 host; `bin/simple-interp` walks that same broken candidate list and so
fails identically.

With that binary the owned host defaults were still **not** flipped, for two
measured reasons rather than an assumed one:

1. **The Vulkan showcase host is already red at its own current default.**
   `SIMPLE_SHOWCASE_FRAMES=5 <seed> run src/app/ui_showcase/hosts/main_2d_vulkan.spl`
   prints `showcase status=fail renderer=vulkan reason=fresh-device-drawir-receipt-rejected`
   at the stock 320x240. Pre-existing, unrelated to this audit — but it means a
   resolution flip cannot be A/B'd against a green baseline, so the sweep the
   task's method requires would be uninterpretable.
2. **Cost.** That 5-frame 320x240 run took 44 s wall. The host compares
   `pixels.len() != w*h` on the full framebuffer and writes a PPM, so at
   7680x4320 (33.2 Mpx) or 8192x8192 (67.1 Mpx) it moves a 133-268 MB array
   through the interpreter per frame. Measured elsewhere in this lane at
   0.39 fps @ 8192x8192, the host's default 20 frames is ~51 s of render alone
   before readback and PPM encoding. Every `test/03_system/ui_showcase/**` spec
   inherits this default —
   `scripts/check/check-ui-showcase-exact-backend-matrix.shs:73` is the only
   caller that pins `SIMPLE_SHOWCASE_W` explicitly — so the flip would push a
   whole gated spec family from seconds to many minutes.

The conclusion is not "8K defaults are wrong here"; it is that these particular
hosts cannot carry an 8K default until the per-frame full-framebuffer array
round-trip through the interpreter is fixed. `main_2d.spl:32-33` already records
the same shape in its own comment (one `push` per pixel). **The small default is
a symptom of that path, and raising it without fixing the path just converts a
fast wrong answer into a slow one.** That belongs in the perf register as a
prerequisite, and is why the change requests in §F — CR-5 in particular — are
the substantive deliverable of this pass.

`config/graphics/resolution_targets.sdn` (added, owned, non-behavioural) records
the normative targets and the derived sizing figures, so each constant below has
a number to be checked against rather than an intuition.

## F. Change requests for files this agent does not own

**CR-1 — `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:776-779` (clear path).**
Replace the 1-D linearization with the 2-D group shape the rest of the file
already uses:
```
val gx = (_i64(self.w) + 15) / 16
val gy = (_i64(self.h) + 15) / 16
val dispatched = self._dispatch_framebuffer_checked(self.pipe_clear, pc, gx, gy, 1)
```
This requires the clear shader to derive its linear index from
`gl_GlobalInvocationID.xy` and the packed `w`/`h` in the push constant rather
than from `.x` alone. Rationale: 262,144 groups at 8192x8192 is 4x the Vulkan
spec-minimum `maxComputeWorkGroupCount` of 65,535; 512x512 is comfortably under
it and stays under for any surface up to 1,048,560 px per side. If the shader
change is too invasive for this pass, the interim fix is to clamp X to 65,535 and
have each invocation stride by `gl_NumWorkGroups.x * 256`.

**CR-2 (low priority) — `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font.spl:85,558`.**
Not resolution-scaled (see A1's font-path note), so this is hardening, not a fix.
`:558` dispatches Y = `batch.quads.len()`, unchecked against the 65,535 floor.
Clamp both dimensions, or route through the same validated dispatch helper CR-6
introduces.

**CR-3 — `src/compiler_rust/runtime/src/vulkan/buffer.rs:10`.**
`MAX_STRIDED_TRANSFER_ROWS: u64 = 16_384` -> `262_144`
(= 16 full 16384-row surfaces, or 32 full 8192-row ones). Rationale: the current
value admits only **two** full-height damage regions at 8192 rows and rejects any
surface taller than 16384 outright, which is a hard upper bound the directive
forbids. The value guards a `row_bytes * row_count` product that is already
`checked_mul`'d at `:110`, so raising it removes no overflow protection.
Correspondingly raise the `regions.len() > 256` cap at `:121` to `1024` — it
currently exactly equals the compositor's request
(`src/os/compositor/compositor_engine2d.spl:410,471`) with zero headroom.

**CR-4 — `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:1358`.**
The literal `16384` duplicates `MAX_STRIDED_TRANSFER_ROWS` across the FFI
boundary. Track CR-3's new value, and prefer exposing the runtime cap through the
SFFI surface over a second magic number. Until then, any CR-3 landing that misses
this line leaves the Simple-side fallback firing at the old threshold.

**CR-5 — `src/compiler_rust/runtime/src/vulkan/buffer.rs:331,357,371,406,437,453`.**
Every upload and download calls `StagingBuffer::new(...)` — a fresh
`vkCreateBuffer` + `vkAllocateMemory` + `vkMapMemory` **per transfer**. At
800x600 that is 1.9 MB and negligible; at 8192x8192 it is a 268 MB allocate + map
+ free **per frame**, which is a plausible large share of the measured
present 1,050 ms + readback 1,470 ms. Change request: a per-`Buffer` (or
per-device) staging pool keyed by size, allocated once at the high-water mark and
reused, with the mapping kept persistent. This is the archetypal
small-framebuffer-tuned heuristic in the lane. It is also the single change most
likely to move the 0.39 fps number.

**CR-6 — device-limit validation (new code, `src/compiler_rust/runtime/src/vulkan/device.rs`).**
Query and expose `maxStorageBufferRange`, `maxMemoryAllocationCount` and
`maxComputeWorkGroupCount`. Today only `max_push_constants_size` (`:366`) is
read. Fail **loudly** — not via `mark_cpu_fallback` — when a requested
framebuffer or dispatch exceeds a limit, so an 8K surface on a floor-spec device
produces a diagnosable error instead of a silent CPU-lane downgrade (see A2).

**CR-7 — `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl:1507-1509`.**
The `cap = 16` fallback (used when `max_rects <= 0`) should scale with surface
area rather than being a fixed count, e.g. `max(16, (w*h) / (256*256))` — 16 at
800x600, 1024 at 8192x8192. Over-cap the damage set collapses to a full-surface
copy (`:1604-1608`), which at 8K is 268 MB.

**CR-8 — `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:796-807`.**
A full-screen `draw_rect_filled` with alpha < 255 materialises `[color; w*h]` on
the host. Give the rect pipeline an alpha/blend variant so the common
full-surface translucent fill stays on the device instead of costing a 268 MB
host allocation per call at 8K.

**CR-9 — `src/lib/gc_async_mut/gpu/engine2d/backend_baremetal.spl:42`.**
`BM_MAX_DRAW_DIM: i32 = 20000` is a hard upper bound on draw dimensions
(`:329,:351`). Both 8K targets pass, but a 32768-wide surface is refused. Raise
to at least `65536`, or replace the fixed bound with an overflow check on
`w * h`.

**CR-10 — `test/05_perf/bench/vulkan_2d_c/feature_showcase.spl:24-25`.**
`const W: i32 = 800` / `const H: i32 = 600` are compile-time constants, so the
bench cannot be swept without an edit. Make them read
`SIMPLE_SHOWCASE_W`/`SIMPLE_SHOWCASE_H` with the 8K screen target as the default,
so the required resolution sweep is a matter of environment rather than a patch.

**CR-11 — `src/compiler_rust/runtime/src/vulkan_graphics_runtime_buffer.rs:529`.**
Comment says "2^26 pixels"; the true bound after the 2 GiB cap is 2^29. Text only.

## G. Gate status at the time of this audit

`sh scripts/check/check-engine2d-backend-parity.shs` is **not runnable on this
host right now**, independent of this audit: the gate's own internal 4-attempt
retry exhausted with `Bus error: 10` (SIGBUS) on every attempt at `:52`, and it
reported `ERROR — nothing was compared (backend vulkan produced no dump after
4 attempt(s))`, exit 2. An outer 4x retry of the whole gate reproduced this.
SIGBUS under MoltenVK is the known flake for this lane on a loaded machine.

This audit changed no code — its two artifacts are a new tracking document and
`config/graphics/resolution_targets.sdn`, which no code path loads — so pixel
identity cannot have been affected. The gate must be re-run to green before any
of the §F change requests is landed.
