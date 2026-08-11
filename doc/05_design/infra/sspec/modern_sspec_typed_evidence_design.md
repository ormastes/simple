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

**As-built deviation (recorded 2026-08-09):** the planned
`src/lib/nogc_sync_mut/spec/evidence/` runtime tree (registry, artifact_store,
providers/, comparators/) was never created. The live providers landed inside
`src/lib/common/spec/evidence/format/` instead (`exec_capture.spl`,
`file_capture.spl`), importing the nogc facades (`std.nogc_sync_mut.sffi.system.
process_run`, `std.io_runtime`) directly from the common tier; the spec-to-spipe
emitter landed as `src/app/spec_to_sspec/spipe_evidence_emit.spl`. Downstream
contracts are unaffected, but any future lane citing the proposed runtime tree
must create it deliberately, not assume it exists.

## Live-capture provider design (added 2026-08-09)

Audit finding: the pipeline above is fully implemented, but most format
adapters have only ever consumed CONSTRUCTED fixture input. The proven design
for closing that gap, validated by three landed live paths (`exec_capture.spl`,
`file_capture.spl`, `test/03_system/tools/spipe/examples/
live_terminal_capture_spec.spl`):

1. **Real source through an existing facade, never `rt_*` directly** —
   `process_run` for processes, `std.io_runtime` for files, `SgttiTestDriver.
   from_tui_state` for in-process interactive TUI/GUI state, the rendering
   backend-isolation facade for scene readback.
2. **Populate the SAME struct the fixture path builds** (`TerminalSnapshot`
   via `terminal_snapshot_from_rows`, `ActionTrace`, `DrawScene`, ...). Nothing
   downstream — evidence projection, comparator, docgen — changes. This is the
   design's core invariant: live vs fixture is purely an input-provenance
   distinction, invisible to the contract.
3. **Every live slice lands with a spec whose assertion path contains no
   fixture literal, plus a sabotage/revert proof** — otherwise the "live" claim
   is itself unverified.

**Correction to earlier assumptions:** `SgttiTestDriver`
(`src/lib/nogc_sync_mut/ui_test/sgtti.spl`) is NOT a process launcher and
cannot capture from a separate OS process — it snapshots an already-built
in-process `Compositor`/`WinTextSnapshot`. Use it for the in-process
interactive lane (2a/2b); use `process_run` for out-of-process capture.

Per-domain lane table, ordering, and acceptance criteria:
`doc/03_plan/infra/sspec/modern_sspec_completion_plan_2026-08-09.md` §T2.

## Verified-claim ledger

Repo claims underpinning this design were checked by independent read-only agents on 2026-08-08; results recorded in the research doc's audit section (§2) — treat any REFUTED/PARTIAL item there as a design input to re-check before the owning lane starts.
