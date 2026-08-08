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

### Parallel Phase 0 lanes

| Lane | Exclusive ownership | Required delivery | Merge gate |
|---|---|---|---|
| A0 — IR/architecture | `model/**`, architecture and IR design | Source/syntax/semantic IR, adapter/emitter traits, stable serialization, compatibility with `src/lib/common/structural/parse/**` | Golden round trip; no private adapter core fields |
| A1 — Census | `census/**`, migration inventory | Canonical source/manual/owner/tier/class/migration state for every discovered executable spec | Every row has stable identity and disposition |
| A2 — Verification | `verify/**`, `check-spec-to-spipe-*` | Exact coverage, round trip, recovery, source links, non-vacuity, deliberate-red, determinism, license policy | Seeded dropped-byte, silent-recovery, tautology, stale-hash, and unlicensed cases fail |

Phase 0 ends only when A0, A1, and A2 sign the same versioned manifest. The
merge owner is A0; the final reviewer is A2.

## Phase 1 — Shared foundation

After the gate, independently implement source snapshots/maps/preprocessing;
lossless document primitives; XML/HTML and JSON/YAML primitives; normative,
grammar, and register semantics; canonical SPipe/manual/source-ledger emission;
and semantic/version differences. Shared model changes return to the IR owner.

### Parallel Phase 1 lanes

| Lane | Ownership | Dependency |
|---|---|---|
| A3 — snapshots/maps | source model, preprocessing, mapped views | Frozen A0 contracts |
| A4 — document parser | blocks, fences, tables, references, Markdown adapter | A0 + A3 |
| A5 — structured parser | lossless XML/HTML and order-preserving JSON/YAML | A0 + A3 |
| A6 — semantics | normative context, grammar IR, RegisterIR | A0; consumes A4/A5 nodes |
| A7 — emitters | SPipe/manual/source appendix; sole `spipe_docgen` integrator | A0 + representative A6 IR |
| A8 — semantic diff | stable identity, six diff layers, bitfield compatibility | A0 + manifest schema |

A3–A8 may run concurrently after Phase 0. A0 reviews shared-model proposals;
A7 alone changes `spipe_docgen`; A2 alone changes release quality policy.

## Phase 2 — Adapter pilots

Adapter lanes own only their adapter and fixture directories. Each contributes
one valid fixture, one malformed fixture, one version pair, one unsupported
construct, and round-trip/SPipe/manual goldens. Priorities are web standards and
suites, openCypher/Gherkin, RFCXML/ABNF/CDDL, APIs/schemas, hardware/registers,
and AsciiDoc/reST/ecmarkup language specifications.

Suggested independent lanes are web standards (WHATWG/Bikeshed/ReSpec/Web
IDL), executable web/language suites (WPT/Test262/WebAssembly),
openCypher/Gherkin, RFCXML/ABNF/CDDL, API/schema formats, hardware/register
formats, and AsciiDoc/reST/ecmarkup. Adapter agents own only adapter and fixture
directories and propose shared-model extensions to A0.

The WPT lane owns test inventory only; A1/A2 own the separate clause-to-test
binding ledger and coverage verdict. The RFC lane pins the live RFCXML
vocabulary plus retrieval hash and supports RFC 7405 ABNF. The API lane treats
OpenAPI prose as normative rather than promoting informational JSON Schemas to
the sole oracle. The register lane records format version, source-pack license,
and vendor-extension disposition before accepting fixtures.

Each adapter merge must include a valid fixture, malformed fixture, version
pair, unsupported construct, round-trip golden, generated SPipe golden, and
generated manual golden.

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

## Ordered implementation/PR sequence

1. Shared architecture, schemas, manifest, and structural-parser reuse.
2. Raw snapshots, source maps, exact coverage, and round trip.
3. Hash-pinned preprocessing and malformed-input policy.
4. Shared document/table/grammar/XML/JSON primitives.
5. Canonical SPipe/manual/source-ledger emitter integration.
6. Non-vacuity, deliberate-red, determinism, and license gates.
7. Semantic and bitfield difference core.
8. Existing Simple Markdown migration pilot.
9. openCypher TCK/Gherkin pilot.
10. RFCXML plus ABNF pilot.
11. CMSIS-SVD plus native Simple bitfield pilot.
12. Kernel/NVMe/RISC-V handwritten bitfield differential migration.
13. WHATWG/CSSWG plus WPT manifest pilot.
14. Test262 and WebAssembly pilots.
15. OpenAPI/JSON Schema/AsyncAPI pilots.
16. RISC-V AsciiDoc and architectural-test binding.
17. Vulkan AsciiDoc/XML/CTS integration.
18. Census-driven repository migration and duplicate retirement.

No later item may bypass an earlier shared gate. Pilot work may prepare fixtures
in parallel, but it does not merge before its parser, IR, emitter, and verifier
dependencies are green.
