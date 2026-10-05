# Explicit free-call type arguments discarded before HIR

Status: source repair candidate; native tests and regenerated-schema parity UNRUN.

Phase3 reported 35 unresolved generic calls even though its authenticated source
contained explicit arguments at the 34 `cas_batch_error_v1` calls and
`walk_hir_expr<MatchSiteScan>`. This record isolates a directly visible source
defect; it does not claim that the candidate compiler has completed Phase3.

`try_skip_ident_generic_args` confirmed and consumed a generic argument token
sequence without returning it. Both bare-identifier postfix paths discarded the
sequence. The flat bridge emitted an ordinary callee and HIR call lowering then
unconditionally supplied `[]` as its type arguments. HIR codec/mono changes
cannot restore information already discarded here. Contextual inference is an
independent fallback and its implicit-call regressions remain unchanged.

The candidate keeps the existing speculative comparison disambiguation, then
rewinds a confirmed free call and uses the canonical type parser. Type ids are
length-framed in the otherwise unused IDENT float-text slot, which is already
preserved by the flat pool snapshot and clone representation. They are never
placed in expression-child slots. Decoding is bounded by the encoded length and
rejects malformed/trailing frames. A defaulted structured Expr field carries the
converted types to HIR Call; existing Call variant arity is unchanged. Semantic
hashing and the AST visitor include those types. The schema generator already
walks non-kind carrier fields; checked-in generated bodies are synchronized by
inspection, but regeneration/header parity must be verified when the real
compiler_schema binary is available. Existing headers are not new proof.

The canonical type parser also consumes one half of a combined `>>` only when
expecting a generic close, leaving the second close pending. Expression shifts
retain their existing token path. Generic receiver/method specialization remains
outside this free-call repair; no claim is made about those existing paths.

Regressions: `explicit_call_type_transport_spec.spl` parses real source, checks
ordered arguments and nested dictionary shape, resets/restores flat expression
pools, calls real HIR lowering, compares semantic hashes and checks implicit
calls/comparison backtracking. Native fixture
`test/fixtures/compiler/explicit_return_only_generic/main.spl` intentionally
omits contextual annotations: T appears only in the callee return type. Require
both backend compile success, run exit 0 and exact
`explicit return-only generic: 3 checks, 0 failures`. Existing implicit generic
and wrong-fixed-nominal fixtures must remain in qualification.

Memory/performance limits: no additional process, global side table or source
reread; explicit calls incur a second bounded scan of their written type list
and per-callee metadata. Expr gains a collection field, so AST memory and cold/
warm parse time require measured regression checks on a real compiler before
promotion. No native builds were launched from this lane; active sources,
snapshots, caches and owner budgets were preserved.
