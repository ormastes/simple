# TL;DR — Image/Object Design Plan

Three slices, in order, CLI-first, extend don't rebuild:

1. **PNG encoder** — `src/lib/common/image/png_encode.spl` (+ a stored-block
   `deflate_deflate.spl`). Unblocks everything else; test oracle is free via
   round-trip through the existing `png_decode.spl`.
2. **Spritesheet packer CLI** — `src/app/spritesheet/main.spl`, wires the
   already-working `AtlasBuilder` packer to real PNG I/O, emits an SDN
   manifest in the shape `game2d/asset/loader.spl` already parses.
3. **Textured `model3d` materials** — add optional `texture:` field to scene
   nodes, `--out foo.png` on `simple model3d render`.

Deferred and named: palette/indexed-color tools (no consumer yet), GUI asset
editors (no concrete need yet), real DEFLATE compression (stored blocks are
correct, just uncompressed).

```
png_encode.spl --> spritesheet pack CLI --> model3d textured render
   (slice 1)          (slice 2)                 (slice 3)
```

Every BDD oracle in the plan is absolute: exact pixel/byte/array equality or
exact exit code + path-qualified error text — no "ran without crashing" tests.

Full doc: `doc/03_plan/app/game_tools/image_object_design_plan.md`
