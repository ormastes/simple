<!-- codex-research -->
# Feature Requirements: Lossless Specification Import to SPipe

Status: User-selected target contract
Date: 2026-08-03

## Goal

Provide one pure-Simple `spec-to-spipe` pipeline that losslessly accounts for
source standards, derives explicit semantic and conformance dispositions, and
emits modern non-vacuous SSpec, professional manuals, register artifacts, and
semantic version differences. Emitting an SSpec file alone is not conversion.

## Requirements

### REQ-S2S-001 — Canonical command and compatibility

Expose `import`, `verify`, `generate`, `diff`, `bitfield`, and `census` under
`simple spec-to-spipe`. `simple spec-to-sspec` shall delegate to the same
implementation and print a terminology notice; it shall not fork behavior.

### REQ-S2S-002 — Lossless acquisition and parsing

Record immutable bytes, encoding, newline convention, SHA-256, pinned source
version/revision, URI, license policy, adapter version, and preprocess-rule
version. Preprocessing shall be an ordered, hash-pinned overlay with source
maps. Parsers shall retain raw nodes and comments and support nested
`ErrorNode`s, stable-delimiter recovery, partial semantics, adapter rule IDs,
strict mode, and manifest-approved compatibility recovery. Malformed constructs
shall remain source nodes with error children and never silently disappear.

### REQ-S2S-003 — Source disposition and exact coverage

Every source byte and clause shall be assigned an explicit disposition such as
normative, informative, editorial, license-restricted, generated navigation,
unsupported, blocked, excluded with reason, or another justified category.
Runtime ignore may be emitted, but the source ledger and manual shall retain the
source disposition. Exact byte coverage shall be 100%.

### REQ-S2S-004 — Shared semantic IR

Use adapter-neutral syntax and semantic IR for requirements, algorithms,
schemas/APIs, grammar productions, conformance cases, registers/fields,
exclusions, diagnostics, source mappings, manifests, and differences.
Adapter-specific additions shall use versioned extension namespaces.

### REQ-S2S-005 — Normative classification and conformance binding

Adapters shall supply normative profiles. Classification shall retain modality,
subject/action/object, conditions, exceptions, consequence, testability,
confidence, and source span. Heuristic language shall remain `needs_oracle` or
`needs_review`. Binding priority is official cases, machine schema/grammar,
existing Simple behavior, deterministic examples, differential oracle, manual
oracle, then explicit skipped/blocked status.

### REQ-S2S-006 — Format-family adapters

The architecture shall support staged adapters for document formats, XML/HTML,
JSON/YAML schemas and APIs, grammar/IDL, executable conformance suites, and
register/bitfield formats. PDF and proprietary standards are later local-input
adapters with content hashes and license-safe references, not the parser base.

### REQ-S2S-007 — Modern SPipe and manual output

Generated SSpec shall use outcome-oriented scenarios, procedural `step` calls,
stable requirement traceability, real compiler/runtime behavior, and explicit
fail-fast placeholders for unresolved bindings. Manuals shall be manual-first,
include source ledger/provenance and original content or a license-safe
content-addressed reference, and regenerate byte-identically.

### REQ-S2S-008 — Register and bitfield generation

Normalize ranges to inclusive `[msb:lsb]` RegisterIR. Validate width, overlap,
gaps, reset, signedness, access policy, aliases, endianness, arrays, and enums.
Generate native Simple declarations, documentation, and behavioral/differential
tests. Retire handwritten masks only after old/new parity passes.

### REQ-S2S-009 — Semantic version differences

Pin every imported version. Diff raw bytes, document structure, normative
requirements, grammar/schema/API, conformance bindings, and generated artifacts.
Use upstream ID, registry ID, structural path, adapter semantic key, then
content/neighborhood similarity for stable identity. Classify source, binary,
behavioral, and documentation compatibility and generate migration vectors.

### REQ-S2S-010 — Verification and safety

Verify exact coverage, round trip, source links, non-vacuity, deliberate-red
calibration, determinism, stale hashes, unknown-version fail-closed behavior,
license policy, source/runtime disposition agreement, and interpreter/native
parity where supported. No silently recovered or discarded source is allowed.

### REQ-S2S-011 — Pure Simple ownership

Canonical parsing, IR, emission, diff, and verification shall be pure Simple.
Foreign tools may be bootstrap oracles, suite launchers, one-time converters,
or justified bindings only. A self-hosted failure remains blocked and receives
a minimized regression; the Rust seed may not substitute for validation.

### REQ-S2S-012 — First milestone

One shared manifest and gate set shall prove: an existing Simple Markdown spec,
an openCypher TCK feature, a small RFCXML document with ABNF and malformed
recovery, and a public CMSIS-SVD device plus the existing NVMe CC register.

## Completion rule

An import is complete only when source is losslessly accounted for, every
applicable requirement has an explicit conformance disposition, and generated
tests provide non-vacuous evidence against the production Simple implementation.

