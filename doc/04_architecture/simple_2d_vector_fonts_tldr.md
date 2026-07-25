# Simple 2D Vector Fonts — TLDR

```sdn
font_path:
  Engine2D: [load_font, draw_text]
  FontRenderer: [layout, cache, tight_alpha_payload]
  spl_fonts: fontdue
  fallback: bitmap
```

- Bitmap stays default; selected font uses one tight payload and one blend.
- FIFO remains 512 entries and gains a 32 MiB bound plus counters.
- Rasterized glyph snapshots are owned until copied/freed; cache stats remain honest.
- Each engine owns a lazy renderer/cache; the native face/layout remain a serialized process-global singleton.
- Trusted local paths use exact UTF-8 bytes; invalid sizes stop before native layout.
- Replacement is transactional; native generation lazily invalidates stale caches.
- No new dependency, parser, shaper, atlas, or per-glyph readback; emulated blend may read one full frame.
