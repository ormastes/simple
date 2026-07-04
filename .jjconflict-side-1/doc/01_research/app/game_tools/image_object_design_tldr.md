# TL;DR — Image/Object Design Tooling Research

**Have:** PNG/PPM decode (`src/lib/common/image/`), stb_image load via SFFI
(`src/lib/nogc_sync_mut/io/image_sffi.spl`), a working shelf-based sprite
atlas packer (`src/lib/nogc_sync_mut/engine/sprite/atlas_builder.spl`), PBR
material/texture data types (`src/lib/gc_async_mut/gpu/engine3d/
material3d.spl`, `texture3d.spl`), and a real SDN-driven 3D CLI
(`src/app/model3d/main.spl`: `inspect`/`render` to PPM, box-only, flat color,
already has absolute-pixel-oracle SSpec tests).

**Missing:** PNG **encoder** (biggest gap — no deflate/write path anywhere,
only inflate/read), a packer-to-file CLI (packer exists, no I/O around it),
textured materials in `model3d`, palette tooling (YAGNI), GUI asset editors
(YAGNI — CLI-first).

**Editors checked:** `src/app/editor/` = code IDE (LSP/debug/wiki, no pixel
canvas). `src/app/ui_edit/` = HTML/CSS markup editor CLI (no image handling).
Neither is a real head start for pixel/texture work; `model3d`'s SDN+raster+
absolute-oracle-test pattern is the one to extend.

```
[PNG decode] --(MISSING: PNG encode)--> [export]
      |
[atlas_builder pack()] --(MISSING: file I/O)--> [atlas CLI]
      |
[model3d inspect/render] --(extend: textures/materials)--> [textured 3D preview]
```

Full doc: `doc/01_research/app/game_tools/image_object_design.md`
