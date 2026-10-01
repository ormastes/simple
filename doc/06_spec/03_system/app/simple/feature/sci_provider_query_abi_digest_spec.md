# SCI Provider-Query ABI Digest Admission

## Purpose and audience

This operator manual verifies the focused bootstrap ABI-digest lane: a provider
query result preserves and returns the complete 32-byte SHA-256 identity, and
the host admits it only when it exactly matches the canonical SCI identity. It
is for compiler/runtime maintainers reviewing REQ-005, REQ-006, and REQ-014.

This slice deliberately does not claim mutable-path or same-handle loader
TOCTOU safety. That remains a separate later loader criterion.

## Preconditions

- A qualified, admitted pure-Simple self-hosted CLI with working `test`, SPipe
  docgen, and `sspec-maintain` commands.
- `SIMPLE_LIB=src` and the repository root as the working directory.
- No Rust bootstrap seed may be used as evidence.

Current execution status: **TEST_BLOCKED**. This worktree has no `bin/simple`,
and no available general test/docgen CLI has an admission receipt proving its
exact path, hash, stage, provenance, and supported commands. The previously
admitted Stage 2 compiler supports focused native compilation only and cannot
substitute for SPipe, docgen, or `sspec-maintain`.

## Operator workflow

1. `encode_provider_digest_result` — encode the canonical 84-byte result.
2. `verify_provider_digest_identity` — decode and compare all digest bytes.
3. `inspect_provider_digest_wire` — verify prefix, digest, and reserved offsets.
4. `query_provider_digest_producers` — inspect CLI and compiler-driver results.
5. `reject_provider_digest_identity` — reject malformed and unequal SCI input.
6. `reject_legacy_partial_provider_result` — detect legacy partial writes.
7. `reject_noncanonical_provider_result_size` — reject short/trailing records.

## Scenario narratives

### Exact identity succeeds

The result preserves its original 48-byte scalar prefix, carries the complete
ABI digest at bytes 48–79 in display order, and reserves zero bytes 80–83. A
round trip returns the exact lowercase digest and the host validator returns no
diagnostic only for the equal SCI identity.

### Real producers carry full identities

The in-process CLI provider and coarse compiler-driver provider return complete
canonical digest values through their production query functions. This guards
against fixing only the codec while leaving a producer truncated.

### Invalid identities fail closed

A malformed SCI digest reports `interface-abi-digest-invalid`; a different
canonical digest reports `provider-query-abi-digest-mismatch`. A poison-filled
84-byte buffer with only the historical 60-byte prefix overwritten reports
`result-reserved-not-zero`. Dirty reserved bytes and 60-, 83-, or 85-byte
records are rejected rather than normalized.

## Requirement traceability

| Requirement | Executable scenarios | Evidence |
|---|---|---|
| REQ-005 | exact round trip; producer queries; malformed/mismatch rejection | full SHA-256 returned and compared exactly |
| REQ-006 | exact round trip; offset inspection; partial-write rejection; strict sizes | 48-byte prefix + bytes 48–79 + zero reserved bytes |
| REQ-014 | exact admission; producer queries; identity and wire rejection | only canonical compatible identity reaches admission |

Each traced requirement has at least three non-placeholder executable
scenarios using built-in `to_equal` assertions.

## Scorecard

| Check | Status | Basis |
|---|---|---|
| Visible step-based flows | PASS | every scenario contains a literal `step("...")` |
| Positive, edge, and error assertions | PASS | exact/producer, byte-offset, and rejection rows |
| Built-in matchers only | PASS | `to_equal` only |
| Runtime execution | TEST_BLOCKED | no admitted general pure-Simple CLI |
| Docgen and `sspec-maintain` | TEST_BLOCKED | same admission blocker |

## Findings and remediation

No placeholder passes or skipped outcomes are present. Once a qualified CLI is
available, run this spec once, generate this manual once, run
`sspec-maintain scan` once, and replace only the `TEST_BLOCKED` evidence with
the exact CLI path/hash/stage/provenance and command results. A runtime failure
is a real failure; do not weaken assertions or fall back to the Rust seed.

## Evidence and provenance

- Executable source:
  `test/03_system/app/simple/feature/sci_provider_query_abi_digest_spec.spl`
- Production boundaries: `src/os/smf/provider_query_wire.spl`,
  `src/os/smf/provider_loader.spl`, CLI registry, and compiler-driver provider.
- Focused earlier native evidence is stage-scoped and does not establish this
  system-runner/manual gate.

## Compatibility and limitations

The accepted v1 result size is exactly 84 bytes: the original 48-byte scalar
prefix, a 32-byte ABI SHA-256, and four zero reserved bytes. Legacy 60-byte,
truncated, or trailing forms are incompatible by design. This manual covers
identity wire/admission only, not artifact-path stability, handle remapping,
unload races, Stage 4 readiness, convergence, DDC, or cross-host behavior.
