# Simple 2D Vector Fonts Design — TLDR

```sdn
font_design:
  load: transactional_utf8
  render: layout_once_to_tight_alpha_payload
  cache: bounded_generation_aware_FIFO
  native_scope: serialized_process_singleton
```

Bitmap remains the nil fast path; owned glyph snapshots are bulk-copied and freed after each cache miss.
