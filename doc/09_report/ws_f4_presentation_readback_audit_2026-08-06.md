# WS-F4 — presentation path audit: what actually reads back, and what only looked like it

Binary for every measurement: `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`,
md5 `ed53cc5f255e269ca27c4cd83b17aef9` (Rust seed). The render lane is
interpreter-bound. No number here is a self-hosted AOT measurement.

## The composite claim, element by element

The plan's §12.2 F4 premise was that showcase/WM paths "clear and repaint the
full framebuffer, read pixels back, downsample or encode it, write a PPM file,
and route it through the WM". Checked against source, that is **partly right and
partly wrong, and the wrong part matters** — it points the fix at the wrong file.

| element | verdict | evidence |
|---|---|---|
| showcase hosts read pixels back | **REFUTED** | none of the four `ScreenHost.present_scene` impls performs a readback |
| a PPM file is written per frame | **CONFIRMED — one host only** | `host_wm.spl:84-104` |
| ...for the 2d host | **REFUTED** | `main_2d.spl:47-56` — once at exit, gated on `SIMPLE_SHOWCASE_CAPTURE` |
| ...for the gui host | **REFUTED** | `host_gui.spl:90-94` → `present_argb_u32`, no file |
| ...for the web host | **RECLASSIFIED** | `host_web.spl:119-124` writes an HTML doc per frame — that is the web host's render target, not a pixel encode |
| downsampling | **NOT FOUND** | no downsample in any present path traced |
| per-pixel readback, 230,400 FFI calls/frame | **CONFIRMED** | `window_scene_draw_ir.spl:522-536`, one `rt_ptr_read_i64` per pixel at 480x480 |

### The PPM-per-frame case is real but narrow

`ScreenWmHost.present_scene` encodes the whole frame to P6 PPM and writes it to
disk **every frame**, plus a sequence file and a receipt file. That is the
normal WM-client transport, not a test adapter — the legitimate/illegitimate
distinction the brief asks for lands on the *wm* host alone. Replacing it needs
a shared-surface or shared-memory transport, which is a design change, not a
cleanup, so it is **handed off, not attempted here**.

The other three hosts are already clean: PPM appears only as an explicitly
env-gated export.

## The finding the claim missed

The readback is real, but it is not in the showcase layer — it is in the
SimpleOS/hosted compositor present path, and it is **twice as expensive as
filed**:

```
shell_baremetal.present_pixel_buffer_to_framebuffer
  -> shared_wm_pixel_buffer_pixels()   230,400 x rt_ptr_read_i64   (build [u32])
  -> render_blit_frame()               230,400 x rt_mmio_write_u32 (consume it)
```

~460,800 FFI crossings per frame, plus a 230,400-element allocation, to move a
buffer from one RAM address to another. The intermediate `[u32]` has no
consumer: it is built element-by-element from a raw address and immediately
destroyed element-by-element into another raw address.

## Change

`render_blit_frame_from_addr(src_addr, src_pixel_count, width, height)` in
`src/os/gui/render.spl` does the whole move in **one `rt_memcpy`**, and
`shell_baremetal.spl` calls it when the backend has a raw address, falling back
to the array path when it does not.

Safe as a memcpy because both endpoints are plain RAM holding contiguous
little-endian ARGB; the destination is the shadow buffer, never MMIO. MMIO is
still reached only through `render_present()`'s volatile stores.

It does **not** inherit the live-alias hazard of
`ws_d3_damage_present_investigation.md` §9b, because no `[u32]` is produced at
all — there is no shared array for a caller to mutate. `src_pixel_count` is a
required parameter rather than inferred, because a raw address carries no
length and the array form got that bound for free from `pixels.len()`.

## Verification status: UNVERIFIED IN THIS TREE — and that is itself a finding

`src/os/gui/render.spl` cannot execute here on **either** engine:

```
bin/simple test render_blit_from_addr_spec.spl  -> 5 total, 0 passed, 5 failed
bin/simple test render_pixel_bridge_spec.spl    -> 2 total, 0 passed, 2 failed
bin/simple run  <equivalent probe>              -> same error
    error: semantic: unknown extern function: rt_mmio_write_u32
```

The second line is the important one: the **pre-existing** spec fails
identically at HEAD, for the same reason, unrelated to this change. So
`render_pixel_bridge_spec.spl` has never executed an assertion in this tree
despite declaring `@cover src/os/gui/render.spl 70%`. That coverage claim is
vacuous — the same shape as `painted=N` counting commands visited rather than
pixels produced.

Filed: `doc/08_tracking/bug/render_spl_specs_cannot_execute_mmio_externs_2026-08-06.md`,
with the cheap fix (host stubs for the two MMIO externs; the module is already
designed for headless assertion via `px_read`, `render.spl:193-194`).

`bin/simple lint` on all three changed files: **0 errors** (384-line log, all
warnings pre-existing repo-wide co-compilation categories, none naming these
files).

## Handoffs

- **PPM-per-frame on the wm host** (`host_wm.spl:84-104`) — needs a shared
  surface / shared-memory transport. Design change.
- **Full-frame clear+repaint where damage would do** — O0/O1 own revisions and
  damage; not touched here.
- **`host_gui` allocates a full ARGB frame per present** (`raster_scene_argb`)
  — an allocation issue, not a readback; belongs with the arena/adoption lane.
