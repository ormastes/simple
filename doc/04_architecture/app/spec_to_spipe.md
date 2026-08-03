<!-- codex-design -->
# Architecture: Lossless Specification Import to SPipe

Status: Target architecture; implementation follows contract-freeze milestones
Date: 2026-08-03

## System flow

```text
Acquire/load -> immutable SourceSnapshot -> preprocess overlay
             -> lossless syntax tree -> Semantic Spec IR
             -> SPipe | manual | bitfield | semantic-diff emitters
             -> verification and trace ledger
```

The overlay never mutates the snapshot. Every normalized token and semantic
node maps back to raw byte spans. A parser recovery creates a nested
`ErrorNode`; it cannot erase malformed input. Strict mode rejects recovery and
compatibility mode accepts only recovery rules named by the pinned manifest.

## Package boundaries

```text
src/app/spec_to_spipe/
  main.spl
  model/       source, maps, syntax, semantics, requirements, cases,
               registers, exclusions, diagnostics, manifests, differences
  preprocess/  ordered overlays and mapping
  parse/common byte cursor, tolerant lexer, delimiters, document blocks,
               fences, tables, XML/HTML, JSON/YAML, grammar, normative context
  adapters/    format- and suite-specific interpretation
  emit/        SPipe, manual, source appendix, bitfield, manifest, version diff
  verify/      coverage, round trip, links, non-vacuity, determinism, licenses
  census/      repository ownership and migration inventory
```

Adapters consume shared lossless nodes and emit shared semantic nodes. They do
not edit shared models directly; standard-specific data resides in a versioned
extension record. Emitters consume IR, never raw adapter internals.

## Command contract

```text
simple spec-to-spipe import path/to/import.sdn
simple spec-to-spipe verify build/spec-import/<id>/manifest.sdn
simple spec-to-spipe generate --spipe --manual --source-ledger <id>
simple spec-to-spipe diff <old-manifest> <new-manifest>
simple spec-to-spipe bitfield <manifest> --target simple
simple spec-to-spipe census --root .
```

`simple spec-to-sspec` is a compatibility dispatcher with a terminology notice.

## Shared models

`SourceSnapshot` holds immutable bytes and provenance. `SyntaxNode` holds kind,
raw spans, children, comments, and errors. `SemanticSpec` owns requirements,
algorithms, schemas/APIs, generalized grammar productions, conformance cases,
register blocks, exclusions, and diagnostics. Every semantic node carries a
stable identity, source spans, adapter rule ID, confidence, and disposition.

`ImportManifest` pins family, version/edition/date, URI, revision/tag, source
SHA-256, license policy, adapter/schema version, and preprocess rule-set hash.
Unknown manifest schema or source versions fail closed; unknown optional fields
remain round-trippable.

## Format strategy

- Documents: Markdown/CommonMark primitives, Bikeshed, ReSpec, WHATWG source,
  AsciiDoc, reStructuredText, and ecmarkup.
- Structured markup: RFCXML, CMSIS-SVD, IP-XACT, Vulkan registry, ODF schemas,
  and IANA registries over lossless namespace-aware XML/HTML.
- JSON/YAML: OpenAPI, JSON Schema, AsyncAPI, Devicetree bindings, and emitted
  TypeSpec/OCI/SPDX forms over order-preserving syntax and reference resolution.
- Grammar/IDL: ABNF, EBNF/BNF, PEG-like grammar, Web IDL, CDDL, Smithy,
  openCypher, and ECMAScript grammar through one production IR.
- Executable suites: Gherkin/openCypher TCK, WPT manifests, Test262 metadata,
  WebAssembly spec tests, Vulkan CTS, and RISC-V architectural tests.
- Registers: CMSIS-SVD first, existing Simple tables second, then SystemRDL,
  IP-XACT, Devicetree bindings, and source-mapped prose/PDF overlays.

PDF and license-restricted standards use user-supplied snapshots and emit only
permitted excerpts plus hashes, provenance, and clause identities.

## Normative and conformance semantics

An adapter profile declares normative/informative structure, modal and
prohibition words, algorithm/definition/example/note/exception markers, and
undefined or implementation-defined behavior. The classifier records modality,
structured predicate, exceptions, testability, confidence, and provenance.
Heuristics never become passing tests without an approved oracle.

Conformance cases may invoke translated Simple behavior, an upstream runner,
an interoperability harness, a differential oracle, or a retained result
artifact. The case IR records which; it does not blindly translate upstream
test programs.

## Registers and bitfields

RegisterIR normalizes inclusive bit ranges and separates raw layout from access
policy. Generation validates overlap, gaps, total width, signed representation,
numeric bit numbering versus byte order, reset state, enum values, arrays, and
strides. Unsupported member aliases become stable constants or wrappers.

Every generated field is exercised through real accessors: zero/all-ones,
min/max, one-hot, adjacency preservation, reserved policy, encode/decode,
reset/enums/invalid enums/access policy, serialization endianness, and supported
engine parity. Documentation provides grouped views and source/version status.

## Semantic differences

Diff layers are raw source, document structure, normative clauses,
grammar/schema/API, conformance bindings, and generated artifacts. Stable
matching prefers explicit IDs, registry IDs, structural paths, adapter keys,
then fingerprint plus neighborhood similarity. Register differences include
offset, width, bit range, signedness, access/reset/endian/enums/aliases/reserved
transitions/array layout, with source/binary/behavior/doc compatibility.

## Verification invariants

- 100% byte disposition and exact round trip.
- Deterministic parse, serialization, generation, and diff.
- No unreasoned skip, silent recovery, or unmapped display rewrite.
- Source ledger and runtime skip/ignore agree.
- Every normative clause has a test/schema/grammar/manual oracle or explicit
  skipped, blocked, unsupported, or review disposition.
- Generated tests contain no tautology; compile and runtime cases exercise the
  production implementation and fail under a deliberate-red mutation.
- License-invalid snapshots, stale hashes, and unknown versions fail closed.

## Ownership and dependency rule

Phase 0 freezes shared IR, manifest serialization, census schema, and verifier
policy before broad adapter work. One architecture owner controls shared model
contracts; one docgen owner integrates `spipe_docgen`; one verification owner
controls release policy. Adapter fixtures and extensions cannot bypass them.
Generated files are never hand-edited, and legacy implementations are removed
only after differential parity.

## Pure-Simple failure policy

Canonical components are pure Simple. When self-hosted Simple cannot process a
fixture, minimize it, record affected modes, add a regression, keep the import
blocked, fix the owning compiler/library/runtime layer, then remove the
workaround. Bootstrap oracles do not establish production validation.

