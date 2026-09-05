# Simple 2D Vector Fonts NFRs — TLDR

```sdn
font_nfr_B:
  warm_hits: '>=90%'
  warm_p50_improvement: '>=25%'
  bitmap_regression: '<=5%'
  cache: [512_entries, 32_MiB]
```

Retained evidence must include p50/p95, checksum, cache counters, backend, fixture, and RSS when available.
