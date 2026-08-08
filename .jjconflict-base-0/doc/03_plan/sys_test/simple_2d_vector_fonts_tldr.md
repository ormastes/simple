# Simple 2D Vector Fonts Test Plan — TLDR

```sdn
font_evidence:
  correctness: [system_7, direct_interpreter, cache_unit, bitmap_integration]
  performance: [public_engine2d_31_pairs, detached_bitmap_baseline]
  manual: pending_pure_simple_docgen
```

- Exact checksum, bbox, anchor, AA, clipping, cache, and invalid-input oracles are authored.
- Rust glyph-snapshot owner tests pass 7/7.
- Final Simple tests, manuals, guards, optimizer, and perf remain pending.
- Current blocker: canonical `bin/simple` is a Rust seed; stage3 crashes/no-ops.
