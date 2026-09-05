# Simple 2D Vector Fonts Performance — TLDR

```sdn
font_perf:
  public_path: Engine2D.load_font -> draw_text -> framebuffer
  paired_samples: 31
  bitmap_baseline: detached_HEAD_126bfa06081d
  status: pending_pure_simple_evidence
```

- Whole-payload memoization and its synthetic hit count were removed.
- Missing bitmap baseline/checksum now fails; the threshold is exactly 5%.
- Rust-seed/stage3 attempts are rejected, not performance evidence.
- One restored pure-Simple run must fill the retained report.
