# Simple 2D Vector Fonts Requirements — TLDR

```sdn
feature_B:
  public: [load_font, draw_text, unload_font, cache_stats]
  proof: [two_sizes, simple_unicode, kerning, fallback, invalid_input]
  default: bitmap
```

Selected Feature B reuses `FontRenderer`/`spl_fonts`; complex shaping and new formats remain excluded.
