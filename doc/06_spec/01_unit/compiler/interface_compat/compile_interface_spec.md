# Compile_interface_digest Acceptance Properties

- Executable: `test/01_unit/compiler/interface_compat/compile_interface_spec.spl`
- Requirements: `KPM-REQ-002`, `KPM-REQ-003`, `KPM-REQ-009`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- body-only change: same interface digest, different implementation digest.
- comment/formatting-only change: same interface AND implementation digest.
- private declaration added: same interface digest.
- public function signature change: different interface digest.
- public function return type change: different interface digest.
- declaration iteration order does not change the digest.
- hash inside a string literal is not treated as a comment start (no false collision).
- ABI and placeholder semantic digests are domain-separated from compile digest.
- field append changes provider ABI without changing caller compile interface.
- field rename changes compile and ABI digests.
- field type participates in the ordinal ABI encoding.
- field reorder changes the ABI digest.
- declaration iteration order does not change the ABI digest.
- private record fields participate in exported value layout.
- ignores function body changes after real parsing and HIR lowering.
- changes when a typed exported field is appended renamed retyped or reordered.
- fails closed when an exported signature retains an unresolved HIR type.

## Manual Steps
- Verify: body-only change: same interface digest, different implementation digest.
- Verify: comment/formatting-only change: same interface AND implementation digest.
- Verify: private declaration added: same interface digest.
- Verify: public function signature change: different interface digest.
- Verify: public function return type change: different interface digest.
- Verify: declaration iteration order does not change the digest.
- Verify: hash inside a string literal is not treated as a comment start (no false collision).
- Verify: placeholder abi/semantic digests are domain-separated from compile digest.

## Selected Policy
- This scenario has no additional user-selected policy beyond its listed requirements.

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-02.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.
