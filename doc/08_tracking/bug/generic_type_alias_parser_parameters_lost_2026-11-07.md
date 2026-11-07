# Generic alias declarations lose their parameters and target

Status: source repair and regression specifications authored; runtime verification pending.

The canonical module parser recognized `type Items<T> = Dict<text, T>` as an
alias name followed by unsupported trailing tokens. It did not consume the
generic parameter list, so it never reached the assignment or parsed the
target. Its recovery loop discarded the remaining declaration. The flat-AST
bridge separately constructed every `ParserTypeAlias` with `type_params: []`.

Consequently, generic alias source could not reach the existing semantic alias
owner as a parameterized template. Earlier HIR tests injected a
`ParserTypeAlias` directly and therefore covered substitution without detecting
the parser/bridge loss. This also blocks source-declared aliases needed by
exact type identity in node attributes.

## Repair and existing owners

- The alias declaration reuses `parse_type_params_with_trait_bounds`, including
  its supported inline bounds and default-type transport. It stores the
  resulting names and rows with `decl_set_type_params` and
  `decl_set_type_param_constraints`, then parses the assigned target.
- The bridge reuses `convert_decl_function_type_params` to restore complete
  `ParserTypeParam` values. Missing alias assignment now produces the existing
  parser expectation diagnostic instead of a success with an inferred target.
- Semantic alias registration, argument substitution, defaults, owner scoping,
  cycle handling, and serialization remain at their existing owners. No second
  alias parser or semantic resolver is introduced. Alias `where` clauses are
  not added by this change.

The canonical inline-bound helper currently consumes bare identifiers and
their conjunctions, not parameterized trait bounds: in
`type Items<T: Carrier<i64>> = [T]`, it leaves `<i64>` unconsumed. This is a
separate source-identified grammar gap requiring a canonical helper repair and
focused verification; this alias fix does not claim to support that form.
Structured default types and alias targets use the existing type parser.

The existing flat declaration codec already writes and restores both
`decl_type_params` and `decl_type_param_constraints`. Their wire shape is
unchanged, so no generated codec edit or version bump is needed. Canonical
frontend-cache identity includes the compiler source fingerprint, which
invalidates cached output from the old alias grammar. The tests exercise the
actual pool-capture/restore API after unrelated pool reuse.

## Authored prevention coverage

- `test/01_unit/compiler/frontend/generic_type_alias_parser_spec.spl`: actual
  generic source, multiple parameters, full target structure, bounds/defaults,
  no leakage to a plain alias, pool roundtrip, and malformed declarations.
- `test/01_unit/compiler/hir/type_alias_representation_spec.spl`: parsed alias
  chains equal their direct composite type; parsed imported generic defaults
  retain their owner despite a consumer homonym; explicit arguments survive
  imported nested-array fields and returns. These cases no longer inject the
  parser template under test.
- `test/fixtures/compiler/generic_type_alias_parser/main.spl`: standalone
  default/integer/Boolean and nested-container value assertions.

The isolated source base is release
`283b42bed49b5b5c3a7efc8ca854f055ddf7c56e`. Edits occupy only the alias parser
and alias bridge regions; concurrent node-tree attribute regions must be
preserved when integrating the shared files.

No admitted self-hosted compiler test, native compile, or executable was run;
no Rust seed was used. The authored specifications and source review are not
an executed PASS. Resume with the focused frontend/HIR specs and native fixture
through an admitted self-hosted runtime, followed by required compiler/core and
MCP/LSP checks.
