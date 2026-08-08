<!-- codex-design -->
# Design: Spec-to-SPipe Evidence Extension (Lane E6)

Status: Draft, additive-only extension proposal — does not reopen Phase 0 core
Date: 2026-08-08

## Relationship to the frozen contracts

This lane extends `doc/05_design/app/spec_to_spipe_ir.md` (Phase 0 contract
freeze, "Status: Phase 0 contract freeze") without modifying it, per
`doc/03_plan/agent_tasks/spec_to_spipe.md` ownership: "Fields and meaning in
schema version 1 are frozen. Additive adapter data uses extensions. A core
field or semantic change requires a new schema version..."
(`spec_to_spipe_ir.md:82-86`).

### What the frozen core actually says about extensibility

Quoting `doc/05_design/app/spec_to_spipe_ir.md:38-44` verbatim:

> Adapter-specific information is represented only by `SpecExtensionField`.
> Namespaces are non-empty dotted names; fields are unique and sorted by
> namespace then key. The core does not interpret extension values, so unknown
> namespaces survive canonical serialization. An unknown core schema version is
> different and is rejected.

And `doc/05_design/app/spec_to_spipe.md:43-45`:

> Adapters consume shared lossless nodes and emit shared semantic nodes. They do
> not edit shared models directly; standard-specific data resides in a versioned
> extension record. Emitters consume IR, never raw adapter internals.

**This confirms the plan's premise.** `SpecExtensionField` already IS a
namespaced, additive-only mechanism attached to `SpecImportManifest` (and, by
the same rule, to semantic nodes and ledger entries) that the core does not
interpret. The plan's assumption — "evidence must be additive-only via a
versioned extension namespace" — is consistent with the real frozen contract;
it is not invented agreement.

### A naming collision the plan did not surface

`doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md:38` and the
plan both name the new spec-to-spipe extension namespace
`simple.sspec.evidence.v1`. But that exact string is **already in use** as a
top-level schema tag for an unrelated record:
`src/lib/common/spec/evidence/model.spl:19`:

```
pub val EVIDENCE_MANIFEST_SCHEMA: text = "simple.sspec.evidence.v1"
```

`EVIDENCE_MANIFEST_SCHEMA` tags `EvidenceManifest` (model.spl:453-490), the
per-run evidence-capture manifest (`spec_path`, `spec_sha256`, `provider_id`,
`artifact_sha256`, ...). That record has no relationship to
`SpecImportManifest` or its `SpecExtensionField` list — it is produced by the
*runtime* evidence-capture pipeline (`EvidenceRequest -> ... -> EvidenceManifest`)
described in the same design doc, not by spec-to-spipe import. Reusing the
identical dotted string for two different schema roles (a runtime capture
manifest tag vs. an import-time extension namespace) means a consumer that
greps or dispatches on `"simple.sspec.evidence.v1"` cannot tell which record
it has without also checking the enclosing structure. **This design keeps the
same namespace string** (it is what the plan and both upstream design docs
already commit to), but flags the collision explicitly and requires every
extension field emitted here to declare `kind` so a reader can disambiguate
without relying on the namespace string alone. If this proves confusing in
practice, the fix is a new dedicated namespace (e.g.
`simple.sspec.evidence.import.v1`) — that is a naming-only change and does not
touch the frozen core.

### Where this attaches

Extension nodes attach as `SpecExtensionField` entries in two frozen
attachment points, per `spec_to_spipe_ir.md:38-44`:

1. On the relevant `SpecLedgerEntry` (`spec_to_spipe_ir.md:46-52`) for each
   generated semantic node below, keyed `namespace: "simple.sspec.evidence.v1"`.
2. On `SpecImportManifest` itself, one summary field recording the extension
   schema id and count, so a consumer can detect "this import carries evidence
   extension data" without scanning every ledger entry.

No field of `SpecImportManifest`, `SpecSourceIdentity`, `SpecDisposition`,
`SpecLedgerEntry`'s core shape, `SpecImportDiagnostic`, `SpecErrorNode`, or
`SpecVerificationReport` is altered, reordered, or reinterpreted. Every
extension node still carries the ledger entry's existing stable semantic
identity, source span, adapter rule ID, and disposition (`spec_to_spipe_ir.md:52-53`)
— the extension payload adds evidence-specific fields alongside those, it does
not replace them.

## New semantic nodes (extension payload kinds)

Each node kind below is carried as one `SpipeEvidenceNode` (see code file)
inside the extension. Every node has: `semantic_id` (stable id, same identity
rules as `spec_to_spipe_ir.md:32-36`), `span_start`/`span_end` (byte offsets
into the same `SourceSnapshot` the ledger entry already references),
`requirement_id` (binds to a normative clause, may be empty only for pure
structural nodes), `adapter_rule_id` (which importer rule produced it),
`kind` (discriminator, see below), and `disposition` (reuses
`SpecDisposition` values — imported/malformed/skipped/etc., never a private
enum).

| kind | purpose |
|---|---|
| `InteractionCase` | one conformance/interaction scenario extracted from the source (e.g. one OpenAPI example exchange, one WPT test case) |
| `ActionStep` | one imperative step inside an `InteractionCase`, ordered by `order` in payload |
| `EvidenceProfileRef` | reference to a capture profile id (e.g. `tui_text_exact`) defined in `src/lib/common/spec/evidence/model.spl`; payload is the profile id text |
| `EvidenceOracle` | reference to an `OracleSpec.profile_id` plus the serialized `OracleCheck` list this import expects a generated spec to assert |
| `EvidenceSelector` | one typed `EvidenceSelector` (kind/path/start/length/cardinality/optional) bound to a requirement clause |
| `ProtocolGrammarRef` | reference to a grammar/production id (ABNF/CDDL/JSON-Schema) used to parse protocol evidence for this case |
| `BinaryLayoutRef` | reference to a `BinaryLayoutIR`/register id (e.g. CMSIS-SVD register name) this case's binary evidence is checked against |
| `ComparisonCheck` | one serialized `OracleCheck` (selector + mode + expected + reason), always bound to an `EvidenceOracle` node via `requirement_id`-shared parent id |
| `ManualProjectionHint` | which `ManualBlockKind` + `EvidenceAudience` the emitter should project this case/step to |

These are payload *kinds* multiplexed through one extension record shape
(`SpipeEvidenceNode`), not nine new top-level record types — this keeps the
core's "the core does not interpret extension values" property intact: the
core sees one opaque namespaced field list regardless of how many kinds live
inside it.

## Importer mapping table

| Format | Generated evidence profile |
|---|---|
| OpenAPI | `ProtocolGrammarRef` (JSON Schema per operation) + `InteractionCase` per example exchange + `text_protocol` selectors (`json_pointer`) |
| AsyncAPI | same as OpenAPI, `InteractionCase` per channel message example |
| RFCXML + ABNF | `ProtocolGrammarRef` (ABNF production) + `ComparisonCheck` (`full_pattern`/`exact`) per normative field |
| CDDL | `ProtocolGrammarRef` (CDDL rule) + `BinaryLayoutRef` when the CDDL group backs a binary encoding |
| Kaitai | `BinaryLayoutRef` (`.ksy` type) + `ComparisonCheck` (`binary_field` selectors, round-trip) |
| CMSIS-SVD | `BinaryLayoutRef` (register/field) + `ComparisonCheck` (`bit_range` selectors, reset/enum checks) |
| WPT / ARIA | `InteractionCase` + `ActionStep` sequence + `EvidenceProfileRef` (`tui_text_exact`/`semantic_and_grid` or DOM-equivalent) |
| Khronos (Vulkan/GL registries) | `BinaryLayoutRef` for structs + `ProtocolGrammarRef` for XML registry entries |
| OpenSCENARIO / FMI | `InteractionCase` (scenario) + `ActionStep` (timeline events) + `EvidenceOracle` (`timeline`/`distribution` modes) |

## What one import deterministically emits

Per `doc/03_plan/agent_tasks/spec_to_spipe.md` "Each adapter merge must
include a valid fixture, malformed fixture, ... round-trip golden, generated
SPipe golden, and generated manual golden," one import run emits, all
deterministic and content-addressed by the same source SHA-256 already
required by `SpecImportManifest`:

1. Generated `*_spec.spl` (ordinary SSpec — `describe`/`it`/`step`) referencing
   the evidence extension nodes by `semantic_id`.
2. The evidence profile/manifest — an `EvidenceManifest`
   (`src/lib/common/spec/evidence/model.spl:453`) per `InteractionCase`, plus
   the `OracleSpec` it will be checked against.
3. A source map + disposition ledger: the existing `SpecLedgerEntry` list,
   now additionally carrying the `simple.sspec.evidence.v1` extension fields —
   no separate ledger file.
4. A QA manual and a user manual (`ManualBlock` list, `EvidenceAudience.qa`
   and `EvidenceAudience.user` respectively) via `ManualProjectionHint`.
5. A semantic-diff baseline: the extension node list itself is diffable by
   the existing six-layer diff (`spec_to_spipe.md:117-119`) because each node
   carries the same stable-identity fields ordinary semantic nodes do.

## Generated-vs-overlay rule

Generated SSpec (item 1 above) is immutable, exactly as
`spec_to_spipe.md:143` states: "Generated files are never hand-edited."
Hand-written overlays (custom assertions, additional oracles a human adds)
live in a separate file, source-mapped back to the generated file's
`semantic_id`s via a plain text reference (`# overlay-of: <semantic_id>`), and
are never merged into the generated file. Regeneration must not silently drop
or renumber `semantic_id`s an overlay depends on — if an id would change, the
importer fails closed rather than emit a shifted id.

## Acceptance gates

- **Stable ids and spans preserved**: re-running the importer on unchanged
  source bytes yields byte-identical `semantic_id`, `span_start`, `span_end`
  for every extension node (same identity precedence as `spec_to_spipe_ir.md:32-36`).
- **Extensions survive deterministic round trip**: `extension_lines(...)`
  output is stable-ordered (fixed field order, see code) and canonical
  serialize→parse→serialize is byte-identical, matching the core's
  `canonical_spec_import_manifest` determinism requirement (`spec_to_spipe_ir.md:61-67`).
- **100% source disposition**: every byte range covered by an `ActionStep` or
  `InteractionCase` node is also covered by a `SpecLedgerEntry` with a
  non-`Malformed`, non-empty disposition — extension coverage is a subset of,
  never a substitute for, the core's exact byte accounting
  (`spec_to_spipe_ir.md:46-51`, `spec_to_spipe.md:127`).
- **No tautological generated assertion**: every `ComparisonCheck` node's
  `expected` value must trace to a `requirement_id`-bound source span, never
  to a value read back from the generated code under test (mirrors
  `modern_sspec_typed_evidence_design.md`'s "expected values never derived
  from the actual under test").
- **Unresolved oracle fails fast**: an `EvidenceOracle` node with a
  `ComparisonCheck` whose `EvidenceSelector` cannot resolve to its declared
  `cardinality` is a hard import failure, not a skipped/ignored disposition —
  matching `model.spl`'s selector cardinality contract (`model.spl:43-46`) and
  the core's "no unreasoned skip" invariant (`spec_to_spipe.md:129`).

## Non-goals

This document does not implement an adapter, does not claim any source has
been converted, and does not modify `SpecImportManifest`, `SpecExtensionField`,
or any other Phase-0 frozen record. It also does not resolve the
`simple.sspec.evidence.v1` naming collision noted above beyond flagging it —
that decision belongs to the A0 architecture owner.
