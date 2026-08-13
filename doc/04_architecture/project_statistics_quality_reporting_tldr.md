# Project Statistics and Quality Reporting — TLDR

`simple stats` performs one owned-code inventory and projects the same typed
`StatsInventoryV2` into JSON, Markdown, TLDR, and native Simple Office slides.

- Project rows are disjoint; platform and product-area rows are explicitly overlapping focus views.
- Tests include SSpec tiers, Markdown fenced tests, and `>>>` comment tests.
- Vendored/generated code and `*_tldr.md` files are excluded from owned-code totals.
- Coverage, duplication, coupling, and cohesion retain provenance and freshness.
- Missing or stale quality evidence is reported honestly, never converted to zero or PASS.
- `--quality=full` refreshes existing analyzers; default reporting does not hide expensive work.
- The slide source carries the SimpleOS default-theme marker and converts through the native Office PPTX exporter.
