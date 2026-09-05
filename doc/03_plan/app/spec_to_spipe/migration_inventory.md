# Spec-to-SPipe Repository Census and Migration Inventory

Status: Phase 0 A1 contract implemented; repository traversal intentionally deferred
Date: 2026-08-03

## Purpose

The census establishes a deterministic, reviewable owner map before legacy
specifications are migrated. It classifies existing evidence without claiming
that text heuristics prove conformance. The initial API accepts already-loaded
text; it does not perform a full-tree scan in a request path.

## Inventory contract

Every executable `*_spec.spl` entry records:

- `executable_spec_path`: canonical test location.
- `canonical_source`: requirement, external standard, or explicit local source.
- `generated_documentation_path`: mirrored `doc/06_spec/.../*_spec.md` owner.
- `owner`: accountable package or team.
- `test_tier`: unit, integration, system, performance, or other named tier.
- `quality_classification`: behavioral, structural, compile_fail, compile_pass,
  evidence_only, vacuous, source_grep, or placeholder.
- `migration_state`: discovered, mapped, planned, differential-gate, migrated,
  blocked, or an explicitly reviewed extension value.

Serialization must first call `sort_spec_census_entries`. Ordering uses
executable path followed by every remaining field, so shuffled discovery input
produces byte-identical output and duplicate paths remain deterministic.

## Classification policy

`classify_spec_text` is a conservative first pass. Precedence is placeholder,
vacuous, source-grep, compile-fail, compile-pass, evidence-only, structural,
then behavioral. An assertion-free example remains vacuous. Old
`assert_compiles()` helpers remain placeholders until a real compiler result is
observed. Semantic verification may downgrade a classification; promotion to
implemented conformance requires the Phase 0 verifier and trace ledger.

## Parallel-agent lanes

| Agent | Exclusive ownership | Dependency | Merge gate |
|---|---|---|---|
| A0 | Shared IR and manifest contracts | Structural parser contracts | Golden serialization and schema-version policy |
| A1 | `census/**` and this inventory | Frozen names only | Eight-category fixtures and deterministic ordering |
| A2 | `verify/**` and release policy | A0 manifest schema | Seeded failures for drops, recovery, tautology, stale hash, and license |
| A3 | Snapshot, mapping, preprocessing | A0 + A2 policy | Exact byte disposition and round trip |
| A4 | Document blocks and Markdown adapter | A0 + A3 | Well-formed/malformed round-trip goldens |
| A5 | XML/HTML and JSON/YAML foundations | A0 + A3 | Lossless token/order goldens |
| A6 | Normative, grammar, and register semantics | A0 + parser foundations | Stable semantic identities and review dispositions |
| A7 | SPipe/manual/source-ledger emitters | A0 + A2; sole docgen integrator | Modern manual and non-vacuous SPipe goldens |
| A8 | Semantic/version diff | A0 semantic identity | Six-layer difference and migration-test goldens |

A0 is the only shared-model editor, A7 is the only `spipe_docgen` integrator,
and A2 is the only quality-policy owner. Adapter lanes consume frozen contracts
and keep fixtures under adapter-specific directories. No migration lane deletes
an old implementation until differential parity passes.

## Follow-on census implementation

1. Add a batch-only repository walker outside request handlers.
2. Derive mirrored documentation paths and test tiers from canonical paths.
3. Load explicit owner mappings and external-standard provenance.
4. Emit deterministic SDN and Markdown inventories from the same entries.
5. Add cache keys from repository revision plus classifier version.
6. Bind every entry to the trace ledger and verifier disposition.
7. Use the generated inventory to prioritize vacuous, source-grep, placeholder,
   duplicate-root, browser, RISC-V, and register/bitfield migrations.

## Completion gate

Phase 0 census completion requires every discovered executable spec to have all
seven inventory fields, stable output under shuffled input, no placeholder
passing tests in the classifier suite, and A0/A2 agreement on serialized schema
and quality policy. Whole-repository completion is a later batch milestone.
