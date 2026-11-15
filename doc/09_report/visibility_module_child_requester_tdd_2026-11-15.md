# Selected-child requester consumer evidence

Base: `47c4abcc8e2d72beb4758ecbceeef67e1da638e0`.
Worktree: `/tmp/simple-visibility-route-tdd-20261115`.

Nine requester cases were authored before the consumer implementation. Existing
receipt fixtures also had their literal import braces corrected (`\{...\}`);
they remain UNRUN and their earlier source-review acceptance is not execution.

Implemented: real HIR type/expression access hooks, route-specific child and
ancestor checks, source declaration intent checks, typed retained Direct /
NamedImport facade eligibility with folder-local promotion, stale-binding
rejection and reset ownership. Full details and limitations are in
`doc/05_design/compiler/declaration_visibility_requester_consumer_2026-11-15.md`.

RED/GREEN is TEST_BLOCKED. Available pinned P2 supports native-build only;
unsupported check/test/run/SPipe/docgen commands were not invoked. No seed
fallback or full build was used. No runtime or performance PASS is claimed.

Source hygiene and independent exact-head review are recorded at the handoff.
