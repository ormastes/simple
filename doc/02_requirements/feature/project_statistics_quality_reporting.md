<!-- codex-design -->
# Project Statistics and Quality Reporting Requirements

- REQ-STAT-001: `simple stats` shall report owned source file count and SLOC by language, excluding configured external/generated paths.
- REQ-STAT-002: It shall report non-TLDR Markdown file count and exclude every `*_tldr.md` from all Markdown totals.
- REQ-STAT-003: It shall report disjoint project ownership rows with total, source and test file/SLOC columns for compiler, app, library, OS, runtime, hardware, verification, tooling, examples and remainder.
- REQ-STAT-004: It shall report overlapping firmware and RISC-V focus rows separately and label them non-additive.
- REQ-STAT-005: Test totals shall include SSpec/SPipe source, Markdown fenced runnable examples and source-comment `>>>` tests, with files and runnable LOC.
- REQ-STAT-006: SSpec shall be split into unit, integration, system and other tiers with files and SLOC, deduplicating canonical and legacy mirror paths.
- REQ-STAT-007: Coverage, duplication, coupling and cohesion shall be evidence records with measured/stale/unavailable status, source and timestamp; unavailable data shall never appear as zero or PASS.
- REQ-STAT-008: `--quality=off|summary|full` shall keep quality analysis opt-in and reuse the existing duplicate-check and coupling owners.
- REQ-STAT-009: One normalized model shall drive console, JSON, Markdown, TLDR and deck outputs.
- REQ-STAT-010: The report shall generate `doc/09_report/project_statistics.md`, its same-directory TLDR and a SimpleOS-default-themed slide Markdown/PPTX artifact.
- REQ-STAT-011: Existing placeholder stats tests shall be replaced or superseded by executable assertions covering scope, exclusions, tiers, quality status and report output.
