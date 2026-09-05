# Feature: self-review-policy-schema-v2

## Raw Request
Cross-repo P1: current Spipe/Simple self-review JSONL policy DB contracts incompatible (header fields/record_type, TTL/authority, identity nesting, timestamp format, higher-model vs self_attested). Audit exact current mains and design/implement canonical compatible schema or explicit adapter preserving fail-closed semantics, projections/tests/docs/plugin. Work in fresh isolated branches for each repo, push PR(s), no merge. Coordinate integration order and high-risk restrictions.

## Task Type
bug

## Refined Goal
Make Simple consume Spipe's canonical versioned self-review JSONL policy database through an explicit fail-closed adapter without accepting ambiguous identity, stale authority, malformed timestamps, self-attestation, or high-risk policy scope.

## Acceptance Criteria
- AC-1: Record exact Spipe and Simple main SHAs and reproduce the current producer/consumer mismatch before editing the consumer.
- AC-2: Claim the tracked bug before source edits, inspect the pure-Simple owner first, and document that no Rust/runtime change is needed.
- AC-3: Parse the canonical `spipe-self-review-policy-db/2` header and records with exact closed fields, RFC3339 UTC timestamps, bounded TTL, operator authority, nested subject identity, and higher-model receipt requirements.
- AC-4: If compatibility is required, use only the explicit named adapter for enumerated legacy Simple records, then revalidate canonical output; reject unknown legacy shapes and never infer authority or receipt facts.
- AC-5: Fail closed on expired/future/overlong validity, authority mismatch, identity mismatch, self-attested evidence, malformed receipt digests, and secret/live-policy/signing/review-workflow high-risk changes.
- AC-6: Add the exact mismatch reproducer and adjacent adversarial tests using the pure-Simple policy owner; no Rust/runtime code changes.
- AC-7: Update research, architecture/design/plan, operator guide, feature expert, layer expert, and workflow projections affected by the consumer contract; generated manuals remain operator-readable where applicable.
- AC-8: Run focused Simple tests/lint/duplication and relevant policy gates once, with no seed fallback; record any unavailable full-suite evidence as a blocker rather than a pass.
- AC-9: Integrate only after the Spipe canonical-schema PR; pin the Simple PR description to the Spipe schema and preserve fail-closed behavior while the dependency is unmerged.

## Scope Exclusions
No provider mutation, approval, signing/publish authority, ruleset changes, secrets, Rust/runtime edits, merge, or automatic in-place migration.

## Cooperative Review
No sidecars: the active session policy forbids unrequested delegation. The root task owner is merge owner and final highest-capability reviewer. Shared interfaces are `spipe-self-review-policy-db/2` and the explicit legacy adapter; all unsupported shapes use fail-fast rejection.

## Phase
dev-done

## Log
- dev: Created state file with 9 acceptance criteria (type: bug).
