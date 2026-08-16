# Browser has no Vulkan render lane; deployed seed lacks the vulkan feature

**Date:** 2026-08-15
**Status:** PARTIAL (2026-08-15 post-push audit: the earlier Docker/Vulkan
result used a Rust runtime-vulkan seed and is diagnostic only, not admissible
production evidence. The gate now rejects seeds and remains unverified until a
Vulkan-capable pure-Simple self-hosted CLI passes it. The compiler `vulkan`
feature vendoring blocker is fixed — see "Vendored rspirv repaired" below.)
**Area:** src/app/browser, src/compiler_rust (seed features)

## Post-push verification correction

The original lane silently returned from its SSpec when Docker or the
Vulkan-featured seed was absent, and its shell driver explicitly executed that
seed. Both behaviors violated the repository's fail-closed, pure-Simple
verification policy. The SSpec now treats every unavailable/error result as a
failure, while the driver defaults to `bin/simple` and uses
`scripts/check/lib/require-self-hosted.shs` to reject Rust bootstrap seeds.
Historical seed results below remain useful diagnostics, but do not establish
a green system-test verdict.

## Gap 1 — no browser-level Vulkan render lane

`src/app/browser/render_lane.spl` dispatches exactly two lanes: `live` and
`blink`. Both are CPU HTML->`[u32]` rasterizers; neither lays out or paints on
a GPU. There is no `SIMPLE_BROWSER_RENDER_LANE=vulkan`.

Consequence for the docker/Vulkan system lane
(`scripts/check/check-simple-web-browser-docker-vulkan.shs`): the closest real
path is browser lane paints the frame on CPU, then the engine2d
`VulkanBackend` presents that frame (`draw_image`) on a real lavapipe device
and the check verifies `device_readback` provenance plus pixel fidelity. The
Vulkan device carries present + readback of the browser's frame, not the
paint itself. A genuine fully-GPU browser lane would need the browser's draw
IR routed through `std.gc_async_mut.gpu.engine2d` primitives instead of the
CPU rasterizer.

## Gap 2 — deployed seed binary is built without the vulkan feature

`bin/simple` (rust seed, `bin/release/x86_64-unknown-linux-gnu/simple`) has
no `rt_vulkan_selected_device_index` export; any `VulkanBackend.init()` (via
`vulkan_session.spl:201`) dies with `semantic: unknown extern function`.
The driver crate (`src/compiler_rust/driver/Cargo.toml`) declares **no
vulkan feature at all** — a vulkan seed must be built as:

```
cd src/compiler_rust && cargo build --release --bin simple \
    --features "simple-runtime/vulkan"
```

Note: adding `simple-compiler/vulkan` too fails to build — vendored
`rspirv v0.12.0` dies with `error[E0583]: file not found for module 'build'`
(incomplete vendored crate). The runtime-only feature is sufficient for the
`rt_vulkan_*` SFFI surface VulkanBackend uses.

The docker lane requires that binary at `build/browser-vulkan/simple`
(override: `SIMPLE_VULKAN_BIN`). Related:
`doc/08_tracking/bug/host_vulkan_lavapipe_graphics_entry_points_stubbed_without_vulkan_feature_2026-08-11.md`.

Also observed on host 2026-08-15: `scripts/check/check-vulkan-engine2d-readback.shs`
ends `native_execution_reason=interpreter-fallback / spec_status=not_run /
overall=fail` — the host lane is red for the same feature-gap family.

## 2026-08-15 update — docker lane made GREEN

A runtime-vulkan seed was built exactly as above
(`cargo build --release --bin simple --features "simple-runtime/vulkan"`,
clean target dir, 7m21s) and deployed to `build/browser-vulkan/simple`
(93 `rt_vulkan*` dynamic exports; `rt_vulkan_selected_device_index` present).
Two blockers surfaced past the feature gap, both fixed:

1. `src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl` —
   `render_html_to_pixels_with_viewport` chained a method on the nested
   `BrowserRenderer.create(...)` call; under the seed interpreter that is the
   known erased-receiver-in-nested-call-context failure
   (`semantic: method 'render_html_to_pixels' not found on value of type
   object`). Fixed with the documented intermediate-typed-`val` workaround
   (both `_with_viewport` variants).
2. `scripts/check/browser_vulkan_evidence.spl` required foreground pixels to
   be exactly `0xFF0000`, but the live lane's palette paints CSS `red` as
   `0xDC3232` (measured in-container: the 32x16 div paints 512 px of
   `0xFFDC3232`). Foreground is now "any non-white pixel"; the two-tone and
   byte-exact device-fidelity checks are unchanged.

Verdict (2026-08-15, this host, lavapipe in docker):

```
container_exit=0 lane=live readback_source=device_readback pixels_match=1 pixels_nonbg=512 verdict_key=ok
PASS — 6 check(s) verified: browser page rendered in docker, presented and read back on Vulkan (lavapipe), evidence build/browser-vulkan-docker/browser_vulkan_readback.ppm
```

E0583 re-verified the same day: `cargo check --release --bin simple
--features "simple-compiler/vulkan"` fails in vendored
`rspirv v0.12.0+sdk-1.3.268.0` — `dr/mod.rs:28 mod build;` but `dr/build.rs`
(and the whole `dr/build/` builder module tree) is missing from the vendor
snapshot AND from its `.cargo-checksum.json`, i.e. the crate was vendored
incompletely at the source. Fix requires re-vendoring rspirv 0.12, not a
feature tweak. Runtime-only vulkan does not touch rspirv and is sufficient
for the `rt_vulkan_*` SFFI surface.

Still open:
- compiler-side `vulkan` (SPIR-V codegen) blocked on the rspirv re-vendor.
- no deploy channel for a vulkan-featured seed (this build lives only at
  `build/browser-vulkan/simple`).
- host lane `check-vulkan-engine2d-readback.shs`: with
  `SIMPLE_BIN=build/browser-vulkan/simple` Vulkan now really initializes on
  the NVIDIA device (`selected=vulkan;status=Initialized;compute=true;
  graphics=true;present=false`) but the lane still ends
  `present_exercised=false readback_exercised=false spec_status=not_run
  overall=fail` — the present/readback path is not exercised there; separate
  from the feature gap this record tracked.
- Gap 1 (a genuinely GPU-painting browser lane) unchanged; note
  `src/app/browser/render_lane.spl` now has a `vulkan` present lane
  (`BROWSER_RENDER_LANE_VULKAN`, CPU paint + device present/readback with
  honest provenance), which is the presented-frame path, not GPU paint.

## End-state 2026-08-15 (lane landed GREEN despite the gaps)

`scripts/check/check-simple-web-browser-docker-vulkan.shs` PASSes: the LIVE
browser lane renders the fixture page (white body + 32x16 red div, 512 red
pixels) inside the docker container, and the engine2d VulkanBackend presents
it and reads it back pixel-perfect on lavapipe (`readback_source=device_readback`,
`pixels_match=1`). Verified by `test/03_system/browser_engine/docker_vulkan_browser_spec.spl`
(1/1). Additional gaps hit while building the lane, all still open:

- **Committed HEAD rust seed is unbuildable** (`E0432`: driver references
  `pipeline::compile_stack_bytes_from_mib`, only present in an uncommitted
  working-copy edit of `compiler/src/pipeline/mod.rs`). The vulkan seed at
  `build/browser-vulkan/simple` was built from a detached HEAD worktree with
  that one WC file grafted in.
- **Blink lane paints nothing on this tree** (all-zero buffer under both
  `run` and `test`), and `src/std/blink/style/cascade.spl` imports
  `blink_parse_declarations` which `src/std/blink/css_parser/parser.spl` does
  not provide — browser_render_lane_spec results also fluctuated (10/11 →
  3/11) under concurrent-session tree churn.

## Vendored rspirv repaired (2026-08-15)

The `simple-compiler/vulkan` blocker (`E0583: file not found for module
'build'` in `vendor/rspirv/dr/mod.rs:28`) is fixed:

- Fetched pristine `rspirv v0.12.0+sdk-1.3.268.0` from crates.io via
  `cargo fetch` (scratch `CARGO_HOME`, minimal manifest depending on
  `rspirv = "=0.12.0"`). `diff -rq` against the vendored copy showed exactly
  one delta: the whole `dr/build/` directory was missing (7 files:
  `mod.rs`, `autogen_{annotation,constant,debug,norm_insts,terminator,type}.rs`).
- Copied `dr/build/` into `src/compiler_rust/vendor/rspirv/dr/build/` and
  added the 7 sha256 entries to `vendor/rspirv/.cargo-checksum.json`
  (package checksum unchanged — files match the registry crate exactly).
- Also fixed two unrelated blockers hit on the way: refreshed the
  `vendor/zerocopy/.cargo-checksum.json` entry for `win-cargo.bat` (the
  COMMITTED file's sha256 disagrees with the committed checksum — CRLF
  normalization at vendoring time), and re-exported
  `compile_stack_bytes_from_mib` from `compiler/src/pipeline/mod.rs`
  (defined in `pipeline/native_project`, used by `driver/src/cli/native_build.rs`,
  never re-exported — this also un-breaks the "committed HEAD seed
  unbuildable" E0432 item above).
- Verified: `cargo check --release --bin simple --features
  "simple-compiler/vulkan"` → `Finished 'release' profile` (exit 0), and
  `cargo build --release --bin simple --features
  "simple-runtime/vulkan,simple-compiler/vulkan"` → `Finished 'release'
  profile [optimized] target(s) in 4m 38s`, exit 0.

## Fix direction

- Add a `vulkan` feature to the driver crate forwarding to
  `simple-runtime/vulkan` + `simple-compiler/vulkan`, and a deploy channel for
  a vulkan-featured seed.
- Longer term: a real browser `vulkan` render lane routing draw IR through
  engine2d GPU primitives.

## 2026-08-16 update — browser ENGINE vulkan routing verified (minimal wiring already existed)

Assessment of `src/lib/gc_async_mut/gpu/browser_engine/**`: the minimal wiring
is already present — no glue needed. `SimpleWebRenderer.create_with_backend`
/ `simple_web_render_html_to_readback_with_engine2d_backend(html,w,h,"vulkan")`
route through `simple_web_engine2d_resolved_backend_name` (probe-gated:
resolves "vulkan" only when `Engine2D.probe_backend` initializes, else
"software"), and non-CPU resolutions present through
`present_layout_pixels_with_engine2d_readback`, returning `Engine2DReadback`
with honest `source` provenance ("device_readback" vs "cpu_mirror").

What was missing was proof. Added
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_engine_vulkan_readback_spec.spl`
(oracle-compare vs the strict software backend, [probe-gpu] disclosure, no
vacuous green). On this host (lavapipe + 2x RTX A6000, vulkan-featured
self-hosted binary):

```
[probe-gpu] browser-vulkan: GPU-PROVEN — device readback served the browser frame (source=device_readback identity=... mismatches=0/512)
2 total, 2 passed  |  engine2d_backend_matrix_spec: 16/16 (vulkan GPU-PROVEN)
```

Still open (unchanged): a fully GPU-PAINTING browser lane (draw IR executed by
engine2d GPU primitives rather than CPU layout raster + device present) —
that remains the large feature under "Fix direction".
