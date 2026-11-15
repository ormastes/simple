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

Self-review repaired an explicit import for the expression spelling helper and
changed direct-vs-facade classification to the typed Declaration-role lookup.
Compatibility authority maps contain projected facade terminal rows; their
lookup success alone cannot classify a source binding as a direct declaration.
The authored folder-local facade-promotion case covers this distinction.

Working and staged direct-env guards and staged whitespace checks passed for
the implementation checkpoint. These checks do not qualify runtime semantics.

Independent review identified unproven imported-template closure and unavailable
legacy NamedImport-hop promotion. The safety repair requires an exact selected
hop receipt and blocks unproven alias/default/bound elaboration at the outer
binding. Added two negative regressions and preserved three legal positive
requirements with success oracles. Those positive cases are known unsupported,
so this checkpoint is neither a green suite nor feature completion. The next
required proof producers are specified in the consumer design document.

Follow-up implementation adds actual same-source bare-alias proof at the existing
registration branch, after selected target category and qualified SymbolId agree.
The earlier valid-public-alias success oracle is retained and now intended
supported. Two new regressions cover explicit-private target rejection and stale
projection/reset handling. Sixteen consumer cases remain UNRUN; the valid
generic-default and sibling-facade success requirements remain unsupported.

Next finite checkpoint implements bare same-source nominal-default selection
proofs at the owner dependency/type-resolution operation. The existing valid
Box<T = Target> success oracle is unchanged and now intended supported. Three
new regressions cover pri, qualified-binding mutation/reset and formal shadowing.
Nineteen consumer cases remain UNRUN. Bounds and other default shapes remain
unavailable; authenticated sibling facade selection remains an unmet positive.

Self-review hardened missing template payloads: class/enum/trait/function
authority without its declaration payload is unavailable, never interpreted as
no generic dependencies. Added the twentieth consumer regression; all UNRUN.
