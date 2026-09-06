<!-- codex-design -->
# Project Statistics and Quality Reporting Design

## Frozen interfaces

- `StatsCountRowV2(name, files, sloc)`
- `StatsProjectRowV2(name, total_files, total_sloc, source_files, source_sloc, test_files, test_sloc)`
- `StatsTestSurfaceV2(name, files, runnable_sloc)`
- `StatsQualityEvidenceV2(metric, status, source, measured_at, summary)`
- `StatsInventoryV2(projects, focus_areas, languages, test_surfaces, markdown_files, quality)`

## CLI

- `--quality=off` is default.
- `--quality=summary` reads persisted evidence.
- `--quality=full` refreshes through existing analyzers, then imports evidence.
- `--report=<path>`, `--tldr=<path>`, `--slides=<path>` and `--pptx=<path>` select durable outputs.

## SimpleOS default deck

The deck uses the resolved SimpleOS workspace theme identity, falling back to the same `IOSLight` identity used by Office when no workspace theme is available. Its slide Markdown has compact title, portfolio, projects, tests, quality, risks and methodology slides. PPTX conversion uses the Office slides owner, never a parallel exporter.

## Errors

Inventory errors fail the command. Optional evidence failures render unavailable with the source error. PPTX conversion failure leaves Markdown/TLDR reports intact and returns nonzero when `--pptx` was explicitly requested.
