# Plan: Smallest Production Image/Object Design Toolset

Companion to `doc/01_research/app/game_tools/image_object_design.md`. CLI-first,
extends existing surfaces (`model3d`, `atlas_builder`, `common/image/`) instead
of adding new apps. No GUI in this slice.

## Ordered plan

### 1. PNG encoder — `src/lib/common/image/png_encode.spl` (highest priority)
Everything downstream (atlas export, texture export, any external tool)
blocks on this. Mirror the shape of `png_decode.spl`:
- `encode_argb_to_png(pixels: [u32], width: i32, height: i32) -> [u8]` —
  8-bit RGBA (color type 6), one IDAT, stored/uncompressed DEFLATE blocks
  (BTYPE=00) to start — correctness first, no need for a compressor yet.
- New `src/lib/common/image/deflate_deflate.spl` (or extend
  `deflate_inflate.spl`) with a `deflate_store(data: [u8]) -> [u8]` — stored
  (non-compressed) DEFLATE blocks. This is legal DEFLATE, decodable by every
  PNG reader, and is a handful of lines vs. implementing LZ77+Huffman. Real
  compression is a follow-up if file size ever matters.
- Round-trips through the existing `decode_png_to_argb` — same file gives us
  the test oracle for free.

### 2. Atlas CLI — extend `src/app/model3d/main.spl`'s sibling pattern with a new thin CLI, `src/app/spritesheet/main.spl`
Wire the *existing* `AtlasBuilder`/`AtlasLayout` (already computes packing —
`src/lib/nogc_sync_mut/engine/sprite/atlas_builder.spl`) to real files:
- `simple spritesheet pack <dir-of-pngs> --out atlas.png --manifest atlas.sdn`
  — decode each PNG (`png_decode`), feed dims to `AtlasBuilder.pack()`, blit
  pixels into one ARGB buffer per `AtlasLayout`, encode with step 1's
  encoder, and emit an SDN manifest in the **same shape**
  `src/lib/nogc_sync_mut/game2d/asset/loader.spl` already parses (atlas
  block with named regions) — so the asset loader can consume packer output
  with zero changes.
- Only add a new top-level app if `model3d`'s subcommand dispatch can't
  cleanly host a second, unrelated domain (packing 2D sheets vs. 3D scenes)
  — keep them separate CLIs but reuse the same argv-parsing/usage-error
  idioms already in `model3d/main.spl` (`print_usage`, exit codes 0/1/2).

### 3. Textured materials in `model3d`
Extend, don't replace:
- `test/fixtures/model3d/*.sdn` node schema: add optional `texture: "path.png"`
  alongside existing `color`. Keep `color` as fallback when no texture (no
  breaking change to `valid_scene.sdn`).
- `src/app/model3d/main.spl`: `_node_of` gains texture path parsing; loads
  via `image_sffi.load_image` (or `png_decode` directly since we now also
  have an encoder for tests); `_submit_box` samples texture pixels instead
  of flat `EngineColor` when present.
- `render_scene`/`ppm_text` unchanged structurally; add `--out foo.png` as an
  alternative to `--out foo.ppm` in `cmd_render`, selecting encode path by
  extension. This is the natural place PNG-encode (step 1) gets its first
  real caller beyond its own unit test.

### Deferred (named, not silently dropped)
- Palette/indexed-color tools — no in-repo consumer; add when a retro/8-bit
  target exists.
- GUI preview/editor (sprite canvas, node-graph material editor) — add once
  the CLI slice above is in daily use and a concrete GUI need is named.
- Real DEFLATE compression (Huffman/LZ77) — add if exported PNG file size
  becomes a measured problem; stored blocks are correct today.

## BDD — first slice (PNG encoder), concrete SSpec scenario names

New file: `test/01_unit/lib/common/image/png_encode_spec.spl`
(mirrors the `describe/it` + `step()` + absolute-oracle style already used in
`test/02_integration/app/model3d/model3d_cli_spec.spl`).

```
describe "png_encode encode_argb_to_png":
  it "round-trips a solid-color 4x4 image through decode_png_to_argb byte-for-byte"
    # step: build a known [u32] ARGB buffer (e.g. all 0xFFCC3020)
    # step: encode_argb_to_png(pixels, 4, 4)
    # step: decode_png_to_argb(bytes) -> PngImage
    # oracle: decoded.pixels == source pixels (exact array equality, every element)
    # oracle: decoded.width == 4 and decoded.height == 4

  it "round-trips a mixed-alpha checkerboard pattern pixel-for-pixel"
    # oracle: every decoded pixel equals the corresponding source pixel (not just corners)

  it "produces bytes starting with the 8-byte PNG signature"
    # oracle: bytes[0:8] == [137,80,78,71,13,10,26,10] (exact byte match)

  it "produces a file decodable by the existing decode_png_to_argb without new codepaths"
    # oracle: Result is Ok(_), not Err — proves no format mismatch with the reader half

describe "spritesheet pack CLI" (slice 2, once encoder lands):
  it "packs 3 fixture PNGs into one atlas.png whose pixel content matches each source at its packed rect"
    # oracle: for each source image, read back the packed rect region from atlas.png
    #         and assert pixel-for-pixel equality against the original source pixels

  it "emits an atlas.sdn manifest that std.nogc_sync_mut.game2d.asset.loader can load without error"
    # oracle: load_assets(manifest_path) returns Ok, and each named region's
    #         width/height matches the packer's AtlasLayout output exactly

  it "rejects a directory containing a non-PNG file with a path-qualified error, exit code 1"
    # oracle: exit_code == 1 and stdout contains the offending file path (same
    #         Then_fails_cleanly-style pattern as model3d_cli_spec.spl)

describe "model3d render --out .png" (slice 3):
  it "writes a PNG whose decoded center pixel matches the textured node's source texel exactly"
    # oracle: decode_png_to_argb(rendered.png).pixels[center_index] ==
    #         known texel value from the fixture texture, exact equality
```

Every oracle above is absolute (exact byte/array/pixel equality or exact
exit code + substring), per the false-green guard — no "renders without
crashing"-only assertions.

## File paths touched (plan-time list, no code written yet)
- `src/lib/common/image/png_encode.spl` (new)
- `src/lib/common/image/deflate_deflate.spl` (new) or extend
  `deflate_inflate.spl`
- `src/app/spritesheet/main.spl` (new CLI)
- `src/app/model3d/main.spl` (extend: texture node field, `--out .png`)
- `test/fixtures/model3d/*.sdn` (extend schema, additive)
- `test/01_unit/lib/common/image/png_encode_spec.spl` (new)
- `test/02_integration/app/spritesheet/spritesheet_cli_spec.spl` (new)
- `test/02_integration/app/model3d/model3d_cli_spec.spl` (extend)
