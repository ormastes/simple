# Modern SSpec Typed-Evidence Design

**Date:** 2026-08-08
**Research:** `doc/01_research/infra/sspec/modern_sspec_typed_evidence_research_2026-08-08.md` (full record/API sketches live there)
**Plan:** `doc/03_plan/infra/sspec/modern_sspec_parallel_agents_plan.md`
**Supersedes direction of:** `doc/05_design/sspec_capture_extension.md` (monolithic `Capture`)

## Decision

Replace the monolithic `Capture` (acquisition + parsing + comparison + serialization + `render_md()` in one runtime object) with a staged, typed pipeline. Rationale: capture runtime and `spipe_docgen` run in separate processes sharing only files; a runtime `render_md()` can never be invoked by docgen. Providers emit generic structured `ManualBlock` records; docgen stays the sole Markdown renderer.

```text
EvidenceRequest → EvidenceProvider → RawArtifact
→ FormatAdapter → CanonicalEvidence
→ OracleSpec/Comparator → ComparisonResult → EvidenceManifest
→ ProjectionRegistry → ManualBlock[] → spipe_docgen → user/QA manuals
```

Ordinary SSpec (`describe`/`it`/`step`/`expect`) stays the only scenario language.

## Core contracts

- **Four registries** (independently testable, stable IDs): EvidenceProviderRegistry, FormatAdapterRegistry, ComparatorRegistry, ProjectionRegistry.
- **Typed selectors** (`EvidenceSelector` enum: CanonicalNode, ProtocolField, JsonPointer, TerminalRegion, PixelRegion, ByteRange, BitRange, BinaryField, ScenePath, SimulationSignal, …). Exact declared cardinality; missing/ambiguous fails unless explicitly optional.
- **Typed oracle checks** (`OracleMode`: Exact, Semantic, Subset, OrderedSequence, Multiset, FullPattern, NumericTolerance, ImageExact, ImageThreshold, Invariant, Timeline, Distribution, Ignore), each with selector, typed expected, tolerance/pattern, cardinality, order/multiplicity policy, reason, requirement ID.
- **Fail-closed:** parse error fails; unresolved/ambiguous selector fails; patterns full-value anchored; ignore needs a reason; pattern-only resolving zero checks fails; closed mode rejects undeclared fields; a capture without a positive production oracle cannot pass; expected values never derived from the actual under test.
- **Compatibility facade** maps current `ScenarioEvidence` calls onto the new pipeline; existing exact `wm_compare` gates keep exact semantics.

## Surface profiles (summary — details in research §4–§7)

- **Interactive (SurfacePolicy.Auto):** TUI → semantic snapshot + terminal-cell grid (`TerminalCell` with grapheme, width, continuation, style, semantic_id; pinned width profile; `.tui.sdn` canonical + `.txt` projection; profiles tui_text_exact/style/scoped/masked/semantic_and_grid). GUI capture only for gui-only, visual-requirement, or explicit config. Action trace records before/resolved-target/dispatched/after/settle; bounded observable settling, never fixed sleeps.
- **Text protocol:** one `ProtocolTrace`/`ProtocolFrame` envelope; Text/Binary/Structured payloads; grammar-backed parsing (ABNF/JSON Pointer/etc.); checks exact/full_pattern/ignore(reason)/multiset/bind/same_as; raw bytes always retained; malformed input is a failure.
- **Binary layout:** `BinaryLayoutIR` with four sources — compiler ABI struct layout, RegisterIR (SVD imports), AccessorLayoutAdapter (existing `bitfield.spl` PTE/token/PCI accessors), external schema (Kaitai/CDDL). Manual byte/bit tables generated from the SAME layout the comparator uses; endian + bit numbering always declared; oracles include round trip, one-hot, adjacent-preservation, reserved policy, truncation.
- **Domain profiles** are oracle bundles, not capture kinds (2D Draw IR, 3D scene/asset validation, simulation seed/timeline/invariants/KPIs, audio, perf/statistics, ML, hardware, security).

## spec-to-spipe

Additive only: versioned extension namespace `simple.sspec.evidence.v1`; new semantic nodes (InteractionCase, ActionStep, EvidenceProfileRef, EvidenceOracle, EvidenceSelector, ProtocolGrammarRef, BinaryLayoutRef, ComparisonCheck, ManualProjectionHint) bound to existing stable IDs and spans. Phase-0 core stays frozen. One import emits generated spec + profile/manifest + ledger + manuals + semantic-diff baseline; generated SSpec immutable.

## Proposed layout

```text
src/lib/common/spec/evidence/            model, selector, oracle, result, manifest, manual_block, compatibility
src/lib/common/spec/evidence/format/     text_document, text_protocol, binary_layout, terminal_grid, scene, simulation
src/lib/nogc_sync_mut/spec/evidence/     runtime, registry, artifact_store, golden_review, providers/, comparators/
src/app/spipe_docgen/spipe_docgen/       evidence_loader, evidence_projection, evidence_renderer
src/app/spec_to_spipe/                   semantic/evidence, emitter/sspec_evidence, emitter/manual_projection
test/03_system/tools/spipe/examples/     interactive_surface / text_protocol / binary_layout manual specs
```

One canonical implementation; tiers re-export, never copy comparator logic.

## Verified-claim ledger

Repo claims underpinning this design were checked by independent read-only agents on 2026-08-08; results recorded in the research doc's audit section (§2) — treat any REFUTED/PARTIAL item there as a design input to re-check before the owning lane starts.
