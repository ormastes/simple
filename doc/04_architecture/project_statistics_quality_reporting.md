<!-- codex-design -->
# Project Statistics and Quality Reporting Architecture

## Decision

Extend the authoritative `app.stats` capsule. A single `StatsInventoryV2` model owns disjoint project/language/test rows and quality evidence. Console, JSON, Markdown, TLDR and deck renderers are projections of that model.

## Boundaries

- `inventory_v2.spl`: pure path classification, exclusion and row aggregation.
- `quality_evidence.spl`: adapters for persisted coverage, duplicate-check and coupling evidence; status is measured/stale/unavailable.
- `dynamic.spl`: maintenance-command orchestration and CLI flags only.
- `markdown_report.spl`: full report, TLDR and SimpleOS-themed slide Markdown projections.
- Existing duplicate-check/coupling tools remain semantic owners. Stats never reimplements clone, graph or LCOM algorithms.

Project ownership rows are disjoint. Firmware, RISC-V, DB/web server,
UI/rendering, Office, CRM, Agent Caret, Agents Manager, and SPipe are overlapping
focus tags and are excluded from portfolio summation. Canonical test tier paths
win over legacy mirrors using normalized relative identities.

## Performance

The default path performs one inventory traversal and reads existing evidence only. `--quality=summary` imports persisted evidence; `--quality=full` may invoke the existing analyzers once. No full-tree scan is placed in a request handler: stats is an explicit maintenance command.

## Truthfulness

Evidence records contain status, source, timestamp and details. Missing or unparseable artifacts are unavailable. Old artifacts are stale. Zero is reserved for a measured zero.
