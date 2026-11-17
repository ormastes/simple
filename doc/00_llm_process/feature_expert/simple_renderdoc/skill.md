# Simple RenderDoc Feature Expert

## Role

Own SPipe/LLM process knowledge for **Simple RenderDoc**, the repo-native
**Simple 2D RenderDoc Backend Equivalence** capsule. It is Simple's counterpart
for deterministic render records, validation, field-level diff, exact
equivalence, guest/board receipts, and external capture inspection. It is not a
RenderDoc fork and is broader than the `capture-simple` wrapper.

## Implemented Core

```sh
bin/simple test test/01_unit/lib/common/renderdoc/backend_render_record_spec.spl --mode=interpreter
bin/simple test test/02_integration/rendering/backend_render_equivalence_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/renderdoc_replay_inspect_spec.spl --mode=interpreter
```

These cover the pure record model, fail-closed validation, canonical form,
first/all differences, exact equivalence policy, and pure-Simple parsing of
RenderDoc XML conversion. Focused verification passed 6/6, 5/5, and 5/5 on
2026-07-27.

## External Capture Bridge

```sh
scripts/tool/renderdoc-evidence.shs capture-simple
RDOC_SIMPLE_EVIDENCE_ENV=build/renderdoc/canonical-probe/simple/evidence.env \
  sh scripts/check/check-renderdoc-simple-gate.shs
```

External `.rdc` replay-open/action evidence corroborates the Simple record; it
does not replace the record, exact pixel oracle, or independent producer. The
producer emits a lowercase SHA-256 and the Simple gate recomputes it before and
after replay so substituted or concurrently changed capture bytes fail closed.

## Current Gaps

- Fresh native Windows/macOS, physical-board, and live RenderDoc evidence
  remains external to a Linux-only run.
- A host-matched deployed pure-Simple release binary is mandatory; a Rust seed
  is rejected rather than accepted as capture or SSpec evidence.
- QEMU and full bootstrap qualification must run in a fresh environment after
  their bounded retry caps are exhausted.

Until these are implemented, report the counterpart as **core implemented,
aggregate incomplete**.

## Aggregate

```sh
sh scripts/check/check-simple-2d-renderdoc-backend-equivalence.shs --self-test
sh scripts/check/check-simple-2d-renderdoc-backend-equivalence.shs --profile=focused
```

The wrapper reports all focused, QEMU, and external rows, rejects non-Stage-4
Simple binaries, preserves leaf logs/artifacts, measures elapsed time and RSS,
and exposes every explicit fail helper as a blocker. Its SSpec contract is
`test/03_system/check/simple_2d_renderdoc_backend_equivalence_aggregate_spec.spl`.
The 2026-07-27 focused lane remains blocked where a deployed pure-Simple runner
or live RenderDoc/native-host artifact is unavailable.

## Owners

- Requirements: `doc/02_requirements/feature/simple_2d_renderdoc_backend_equivalence.md`
- Architecture: `doc/04_architecture/simple_2d_renderdoc_backend_equivalence.md`
- Design: `doc/05_design/simple_2d_renderdoc_backend_equivalence.md`
- Core: `src/lib/common/renderdoc/backend_render_record.spl`
- RDC inspector: `src/app/test/renderdoc_replay_inspect.spl`
- QEMU/board schemas: `src/lib/common/renderdoc/simpleos_render_target_evidence.spl`,
  `src/lib/common/renderdoc/simpleos_simd_render_evidence.spl`
- Guide: `doc/07_guide/tooling/renderdoc_capture_infra.md`
- Shared tool: `scripts/tool/renderdoc-evidence.shs`
- Shared capture/schema helper: `scripts/lib/renderdoc-evidence-common.shs`
- Glossary: `doc/glossary.md`

## Update Rule

When record schema, facade capture, QEMU receipts, external bridges, or
acceptance rules change, update this entry and the canonical guide in the same
SPipe lane. Never replace explicit fail placeholders with false-green passes.

## Linux aarch64, no root — 2026-11-14

- RenderDoc v1.36 builds without root (clang/lld 23, Ninja; only
  `libx11-xcb-dev` and `libxcb-keysyms1-dev` needed `apt-get download` +
  `dpkg-deb -x`; lld 23 needs `-Wl,--undefined-version`). `renderdoccmd` then
  drives `scripts/check/check-renderdoc-web-capture-lane.shs`.
- **The lanes expect an INSTALLED tree.** `rdoc_capture_simple_vulkan` sets
  `VK_LAYER_PATH`, which replaces loader discovery, from
  `$RDOC_HOME/etc/vulkan/implicit_layer.d/renderdoc_capture.json`. A build tree
  has no `etc/`, the layer never loads, and the in-app API still answers
  `available=1 start=1` — the run ends `num_captures=0` with no cause named.
  The helper now reports `missing-renderdoc-layer-manifest:<path>`.
- **Start the capture after the device exists.** A start issued before the
  first `vkCreateDevice` returns 1 and captures nothing (re-verified with the
  layer loaded: original program `num_captures=0`). Dropping the warm-up
  engine afterwards is harmless — the shared session keeps the device.
  `renderdoc_web_page_capture.spl` now follows `renderdoc_vulkan_capture.spl`.
- **NVIDIA GB10 (driver 580.173.02): `vkCreateDevice` under the RenderDoc
  layer fails INTERMITTENTLY with `VK_ERROR_INITIALIZATION_FAILED` (-3) — it is
  not a hard rejection** (corrected 2026-11-18; the 2026-11-14 note said 5 of 5).
  Re-measured with a bare instance+device probe: no layer 6/6 ok; layer via
  `ENABLE_VULKAN_RENDERDOC_CAPTURE=1` 2/6 ok; under `renderdoccmd capture` 0/6
  in one batch and 6/6 in the next. Cause not established (two other processes
  held ~21 GB of GPU memory at the time — a correlation only). The Engine2D
  capture lane (`rdoc_capture_simple_vulkan`, `renderdoc_vulkan_capture.spl`,
  `VK_DRIVER_FILES=/usr/share/vulkan/icd.d/nvidia_icd.json`) failed all 5
  Engine2D retries on try 1, then **passed on tries 2 and 3**: `num_captures=1`,
  `.rdc` 7457/7616 bytes, and the converted XML names vendor 0x10de, device
  0x2e12, `NVIDIA GB10`, driver `580.173.02`. So GB10 captures ARE possible;
  rerun on -3. llvmpipe (`lvp_icd.json`) remains the deterministic fallback
  (`overview.simple.rdc` 486756 bytes at 900x760, 2026-11-14).
- GB10 identity (2026-11-18): integrated GPU, Vulkan API 1.4.312, deviceUUID
  `1883ff9c30a91b8abc50ef34ac2f5a89`, driverUUID
  `6d5e1e1841115cbdae1ec369f9e3c390`. The process loader on this host is
  `/home/yoon/.local/lib/libvulkan.so.1` (1.4.328, via `LD_LIBRARY_PATH`), not
  the system one; there is no `libvulkan.so` dev symlink and no
  `/usr/include/vulkan` — link `-l:libvulkan.so.1` and use Skia's in-tree headers.
- The N2 qualification runner and `provider.cpp` do not call the RenderDoc
  in-app start/end API, and the workers never present, so the N2 case workers
  cannot be captured as-is; only the generic Engine2D capture scene can.
- Pinned Skia (`35d5edfa…`) builds on this aarch64 host with
  `tools/upstream-skia-ganesh-vulkan/build-linux.shs` in ~2 min at `-j6`
  (`SIMPLE_UPSTREAM_SKIA_NINJA_JOBS`). The full dependency sync is ~7 GB
  (`unicodetools` 3.2 GB, `swiftshader` 1.4 GB, neither used by the provider);
  `out/.../obj` is ~1 GB and safe to delete once `libskia.a` exists.
- `RDOC_WEB_CHROME_BIN` was honoured only in `RDOC_WEB_TOOL_SEARCH=isolated`
  mode; fixed. The Chrome side still ends `vulkan-angle-unavailable` on a host
  with no display and no Xvfb.
- **The replay inspector reads command names from `<chunk …>` opening tags
  only** (`_chunk_tags`, one `split` pass). It used to count `name="vkCmd…"`
  anywhere, so `<metadata name="vkCmdDispatch">` passed as a dispatch.
  Real capture check (web7 `overview.simple.rdc` → 1.8 MB XML, 1637 chunks):
  pass, 205 dispatches, 5 pipelines, 5 shaders, 33 resources, 8.8 s wall.
- `renderdoc_simple_gate_spec` needs a runnable inspector binary to exercise
  a real replay: in a worktree with no `bin/simple` set
  `RDOC_REPLAY_SIMPLE_BIN`. Since 2026-11-15 the gate checks `renderdoccmd`
  BEFORE the inspector binary (as `inspect_renderdoc_capture` does), so a host
  with no RenderDoc reports `renderdoccmd-missing` in any checkout; before
  that, the "synthetic magic file" case failed in every worktree with
  `simple-replay-inspector-missing` (10/11 -> 11/11 without the env var).
  `renderdoc_replay_inspect_spec` is 8/8 at `fa2dd425635` (default mode and
  `--mode=interpreter`); the earlier 7/8 did not reproduce.

## Finding which dispatch wrote a pixel — Vulkan text clip, 2026-11-15

Bug `web_vulkan_lane_control_text_one_row_past_clip_2026-11-15.md`: llvmpipe
painted `<input value="Simple">` glyph rows below the control box that the CPU
lane clips. Captured the 300x120 repro with the fix and with the base
`backend_vulkan_font.spl`, same seed, lvp ICD.

- **Installed-tree shim for a RenderDoc build tree** (no `etc/`, so the
  layer never loads): make a directory with `bin -> $RDOC_BUILD/bin`,
  `lib -> $RDOC_BUILD/lib` and
  `etc/vulkan/implicit_layer.d/renderdoc_capture.json` copied from the
  build's layer manifest, and pass it as the RenderDoc home.
- Capture: source `scripts/lib/renderdoc-evidence-common.shs`, set
  `RDOC_SIMPLE_PROG=src/app/test/renderdoc_web_page_capture.spl`,
  `RDOC_HTML_PATH`, `PAGE_W`/`PAGE_H`, `RDOC_SIMPLE_BIN`,
  `VK_DRIVER_FILES=/usr/share/vulkan/icd.d/lvp_icd.json`, and call
  `rdoc_capture_simple_vulkan "$ROOT" "$SHIM" "$OUT"` under
  `systemd-run --user --scope -p MemoryMax=8G`. Both runs: `num_captures=1`,
  `rdoc_capture_status=pass`, ~91 KB `.rdc`.
- `renderdoccmd convert -f X.rdc -c zip.xml -o cap.zip.xml` gives the chunk
  XML plus a zip of buffer contents. Before vs after: identical chunk
  structure (34 `vkCmdDispatch`, same pipelines and group counts); only two
  114720-byte buffer payloads differ, 7 bytes each.
- **Identify the dispatch by role, not by id** (ids differ per capture): the
  font-atlas composite pipeline is the one whose dispatch is
  `(ceil(max_quad_px/64), glyph_count, 1)`; here the last dispatch, groups
  `(2,6,1)` for the six glyphs of `Simple`. Its params buffer is
  `vulkan_font_packed_params`: 8 header words (`max_pixels` at byte 28), then
  7 words per glyph `atlas_x, atlas_y, w, h, dst_x, dst_y, color`.

| glyph | before (h, rows)  | after (h, rows) |
|-------|-------------------|-----------------|
| S     | 10, y 23-32       | 9, y 23-31      |
| i     | 10, y 23-32       | 9, y 23-31      |
| m     | 7, y 26-32        | 6, y 26-31      |
| p     | 10, y 26-35       | 6, y 26-31      |
| l     | 10, y 23-32       | 9, y 23-31      |
| e     | 8, y 25-32        | 7, y 25-31      |

  Header `max_pixels` 80 -> 72. So the vector-face composite dispatched whole
  glyph quads through a clip whose bottom is y 31: the clip was ignored
  entirely ('p' was 4 rows over), not off by one edge.
- The other font batchers do not share the defect by construction: CUDA,
  OpenCL, ROCm and Metal `draw_font_batch` return 0 (CPU fallback) whenever a
  clip or mask is set (source read only; no such device on this host).
  Vulkan now bakes the clip into the quads (`composite_font_batch`) and
  reports a fully clipped batch as the admitted status `clipped-out`.
