<!-- codex-research -->
# Local Research: Project Statistics and Quality Reporting

## Existing ownership

`simple stats` is dispatched by `src/app/cli/_CliMain/main_and_help.spl` and
implemented by `src/app/stats/dynamic.spl`; `src/app/stats/main.spl` is a
startup-light stub and is not the authoritative reporting path.  The existing
Markdown renderer is `src/app/stats/markdown_report.spl` and defaults to
`doc/09_report/project_statistics.md`.

## Current capabilities and gaps

- Existing inventory excludes vendored and third-party source, counts Simple,
  Rust and C/header SLOC, recognises canonical and legacy unit/integration/
  system test roots, excludes `*_tldr.md`, and counts Markdown fenced examples
  plus `>>>` source examples.
- Its project rows are incomplete and use inconsistent source scopes; the
  console total omits some source areas and C SLOC while the report uses a
  different set of buckets.
- Test tiers expose files but not tier LOC. Markdown-test discovery is limited
  to `doc/`. The user needs total source files/LOC, all tests including SSpec,
  Markdown and comment tests, and per-project file/LOC matrices.
- `src/compiler/90.tools/duplicate_check` and `src/compiler/90.tools/coupling`
  already own clone, dependency, cycle, fan-in/out and LCOM4 analysis. They
  must remain the authority rather than being duplicated in stats.
- Current coupling analysis can have unavailable AST/call-index-backed LCOM,
  API and ATSS data. A report must render this as `unavailable`, not zero or a
  passing quality score. Coverage must similarly preserve the freshness and
  provenance of an existing coverage artifact.

## Proposed information model

One canonical inventory model should drive JSON, console and Markdown:

1. Disjoint ownership projects: compiler, app, lib, OS, runtime, hardware,
   verification, tooling, examples and remaining source.
2. Language rows: Simple, Rust, C/C++/headers/assembly, scripts and Markdown.
3. Overlapping focus tags: firmware and RISC-V, reported separately so totals
   are never double counted.
4. Test surfaces: total test LOC/files, SSpec, Markdown fenced tests, comment
   SDoctests, and unit/integration/system/other SSpec tiers with files and LOC.
5. Evidence records for coverage, duplication, coupling and cohesion containing
   status (`measured`, `stale`, `unavailable`), source, timestamp and metrics.

## Presentation and verification

The durable report should have a compact executive summary and stable,
presentation-sized tables. A generated `project_statistics_tldr.md` is the
slide-outline companion and remains excluded from Markdown counts. The normal
report is directly consumable by the in-tree Office/Impress/PPTX surfaces after
template styling is selected. Tests must replace the current manual-placeholder
stats integration specification with real inventory/report assertions.
