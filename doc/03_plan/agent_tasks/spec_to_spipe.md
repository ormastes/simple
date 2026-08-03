<!-- codex-design -->
# Agent Tasks: Lossless Specification Import to SPipe

Status: Follow-on roadmap; no implementation completion claimed
Date: 2026-08-03

## Phase 0 — Freeze contracts

1. Architecture/IR owner: source, mapping, syntax/semantic IR, manifest schema,
   extension rules, and golden serialization.
2. Census owner: every executable spec's canonical source, manual, owner, tier,
   quality, standard reference, register usage, and migration state.
3. Verification owner: exact coverage, round trip, non-vacuity, deliberate-red,
   determinism, source links, recovery, stale hash, and license gates.

Gate: all three owners approve one manifest schema; unknown fields round-trip,
unknown schema versions fail, and adapter fields cannot leak into shared core.

## Phase 1 — Shared foundation

After the gate, independently implement source snapshots/maps/preprocessing;
lossless document primitives; XML/HTML and JSON/YAML primitives; normative,
grammar, and register semantics; canonical SPipe/manual/source-ledger emission;
and semantic/version differences. Shared model changes return to the IR owner.

## Phase 2 — Adapter pilots

Adapter lanes own only their adapter and fixture directories. Each contributes
one valid fixture, one malformed fixture, one version pair, one unsupported
construct, and round-trip/SPipe/manual goldens. Priorities are web standards and
suites, openCypher/Gherkin, RFCXML/ABNF/CDDL, APIs/schemas, hardware/registers,
and AsciiDoc/reST/ecmarkup language specifications.

## Phase 3 — Migration

Consolidate legacy importers behind `spec-to-spipe`; replace vacuous/source-grep
tests; migrate browser manifests and handwritten bitfields; retain overlays for
Simple-only cases; then add changed-spec cache, corpus gates, reproducible
release manifests, performance budgets, and duplicate-root retirement.

## First milestone

Use the same manifest and gates for four inputs:

1. Existing Simple Markdown/spec source.
2. One openCypher TCK feature.
3. A small redistributable RFCXML source containing ABNF and malformed input.
4. A public CMSIS-SVD device plus the existing NVMe CC register overlay.

Only after all four pass exact coverage, source ledger, modern SPipe,
non-vacuity, and semantic-diff gates may broader adapter parallelism begin.

## Merge rules

Shared contracts land before dependents rebase. Only the docgen owner changes
`spipe_docgen`; only the verification owner changes final release policy.
Generated files are immutable outputs. No migration deletes an old path before
differential parity. Large snapshots are content-addressed and license-reviewed.

Merge owner: architecture/IR owner. Final reviewer: verification owner.

