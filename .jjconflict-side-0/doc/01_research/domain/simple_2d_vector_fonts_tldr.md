# Simple 2D Vector Fonts Domain Research — TLDR

```sdn
font_domain:
  reuse: [fontdue, FreeType, existing Engine2D blend]
  hot_path: [layout_once, glyph_cache, bulk_alpha_copy]
  excluded: [complex_shaping, new_parser, atlas]
```

Use the existing raster owner and bounded glyph cache; prove output and cache behavior through the public facade.
