# Research: Image / Object Design Tooling for Game Assets

## Scope
Inventory of existing sprite/texture/3D-object tooling and gap analysis vs a
production 2D/3D game asset pipeline (sprites, textures, materials).

## 1. What exists today

### Image decode/inspect (`src/lib/common/image/`)
- `png_decode.spl` — PNG bytes -> ARGB `[u32]`, color types 2/6 only, built
  for screenshot-diff comparison. **Decode only, no encoder.**
- `ppm_decode.spl` — P6 PPM -> ARGB. Decode only.
- `image_info.spl` — signature/metadata sniffing (`ImageInfo`, color profile
  probes) for web image routing. No pixel decode.
- `deflate_inflate.spl` — thin wrapper over `std.nogc_sync_mut.compression.gzip.inflate`
  for PNG's zlib stream. **Inflate only, no deflate/compress.**
- **No PNG/BMP encoder anywhere in-repo.** Grepped `png_encode|encode_png|
  PngEncoder|bmp_encode|write_png|stbi_write` — zero hits outside a vendored
  torch-sys C header (unrelated, third-party). `model3d render` only ever
  writes plain-text PPM (`ppm_text` in `src/app/model3d/main.spl`).

### Image loading via stb_image (`src/lib/nogc_sync_mut/io/image_sffi.spl`)
- SFFI wrapper: `rt_image_load/free/width/height/channels/get_pixel` around
  the native stb_image decoder. Read-only; no write path exposed.

### 2D sprite/atlas engine code
- `src/lib/nogc_sync_mut/engine/sprite/{sprite,texture,atlas,atlas_builder}.spl`
  and a duplicate set under `src/lib/gc_async_mut/engine/sprite/` — runtime
  data types (`Sprite`, `Texture`, `AtlasRegion`) plus a **shelf-based bin
  packer** (`AtlasBuilder.pack()` -> `AtlasLayout` with named rects). This is
  real, working pack logic — it just has no CLI/file-format front end (no
  "read N pngs, emit atlas.png + atlas.sdn").
- `src/lib/nogc_sync_mut/engine/render/{texture_atlas3d,font_atlas,
  sprite_animation,tilemap}.spl` — additional atlas/animation runtime types.
- `src/lib/nogc_sync_mut/game2d/asset/` — `loader.spl` reads `assets.sdn`
  (images/sounds/atlases block) into an asset `table.spl` with diagnostic
  codes (`GAME-ASSET-001..014`, includes atlas-region-OOB). This is a
  **content descriptor loader**, not an authoring tool — it consumes
  hand-written SDN, doesn't generate or validate it standalone.

### 3D object/material (`src/lib/gc_async_mut/gpu/engine3d/`)
- `material3d.spl` — `Material3D`: PBR descriptor (albedo/normal texture ids,
  metallic/roughness as fixed-point 0-1000, alpha_mode, double_sided). Data
  type only, no file format binding.
- `texture3d.spl` — WebGPU-mirrored texture dimension/format/usage enums +
  descriptor/sampler/view types. Data type only.

### 3D scene CLI (`src/app/model3d/main.spl`, ~520 lines) — the most mature piece
- `simple model3d inspect <scene.sdn>` — parses an SDN `scene:` block
  (camera, background, box nodes with center/size/color), validates shapes
  (rejects e.g. `"sphere"` by name), prints node tree + tri/vert totals +
  world bounds. Exit 1 on any malformed input, path-qualified error text.
- `simple model3d render <scene.sdn> --out <file.ppm> [--width --height
  --eye ...]` — headless raster via the engine3d software rasterizer to a
  **P3 (ASCII) PPM only**. Deterministic (byte-identical across repeat runs,
  asserted in the spec via sha256).
- Nodes today are **box-only**, one flat material per node (`color` hex,
  "unlit"), no textures, no materials file, no multi-mesh scenes.
- Test convention already established:
  `test/02_integration/app/model3d/model3d_cli_spec.spl` +
  `test/fixtures/model3d/{valid_scene,bad_shape,not_a_scene}.sdn` — SSpec
  `describe/it` with `step()`, shell-out to the built CLI, and **absolute
  pixel/hash oracles** (exact RGB triple at named pixel coordinates, sha256
  equality across two renders). This is the pattern to extend, not replace.

### Editor surfaces — assessed for reuse
- `src/app/editor/` — full source-code IDE shell (LSP, debug adapter, wiki,
  command palette, GUI/TUI shells, ~40 files, largest is
  `editor_ctrl_core.spl` at 68KB). It is a **text/code editor**, not visual —
  no pixel canvas, no image widget. Reuse would mean bolting a raster canvas
  onto a code-editing framework; not a fit for sprite/texture editing.
- `src/app/ui_edit/` — CLI for HTML+CSS *page* pairs (`new/list/add-element/
  add-css/set-css`), operates on markup trees via
  `std.common.ui.html_ui.catalog`/`doc_ops`. It edits **UI markup structure**,
  not raster image content. Its dict-of-tags "add/list" CLI *shape* is a
  reasonable template for a future SDN-based sprite/atlas descriptor editor,
  but it has zero image/pixel handling to reuse directly.
- Net: neither editor is a real head start for pixel/texture editing. The
  model3d CLI (SDN in, deterministic raster out, absolute-pixel-oracle tests)
  is the closest existing pattern and the one to extend.

### Not found anywhere in-repo
`png_encode`, `bmp` (read or write), sprite-sheet packer CLI, palette/
indexed-color tooling, texture preview app, material authoring file format,
live-preview render loop for assets.

## 2. Gap analysis: production need vs repo state

| Need | Have | Gap | Real or YAGNI? |
|---|---|---|---|
| Decode common formats (PNG/PPM) | Yes (`png_decode`, `ppm_decode`, stb via SFFI) | — | n/a |
| **Encode PNG for export** (ship sprites/atlases as real PNGs, not PPM) | No | Full gap — no deflate/compress, no encoder | **Real.** Every downstream tool (game engine, browser, other DCC) expects PNG, not PPM. |
| Sprite-sheet packing (rects) | Yes (`AtlasBuilder`, shelf packer) | No CLI/file I/O around it | **Real but small** — wire existing packer to a CLI + PNG read/write. |
| Atlas manifest format | Partial (`assets.sdn` atlas block consumed by loader) | No *generator* — hand-authored only | **Real, small** — emit the same SDN shape the loader already reads. |
| Palette / indexed-color tooling | None | — | **YAGNI now** — no consumer in-repo needs indexed color; modern PNG export is truecolor. Defer until a real 8-bit/retro target exists. |
| Texture preview (view a PNG/atlas visually) | None (no GUI) | — | **Partial YAGNI** — CLI-first per this repo's own priority; a PPM/PNG dump you can open externally is enough for now. A live GUI preview is a later slice. |
| 3D object/material authoring (SDN) | Yes, minimal (`model3d inspect/render`, box-only, flat color) | No textured materials, no mesh shapes beyond box, no material file format | **Real** — closest existing surface, natural to extend rather than replace. |
| Live preview render for 3D | Yes (`model3d render` to PPM) | PNG output, texture sampling | **Real, incremental** — extend, don't rebuild. |
| Full DCC-style GUI editor (drag/drop sprite editor, node-graph material editor) | None | Everything | **YAGNI for this slice** — CLI-first is explicit project direction (`bin/simple build`/CLI-first culture); large GUI investment not justified until CLI slice ships and is used. |

## 3. Bottom line
The repo has real, working *pieces* (decoder, shelf packer, PBR data types,
a working SDN-driven 3D CLI with a proven absolute-oracle test pattern) but
is missing the one connective piece almost everything else depends on:
**PNG encode**. Second priority is wiring the existing atlas packer to actual
file I/O. Third is extending `model3d` to carry a texture reference through
material -> render. See the companion plan doc for the concrete slice order.
