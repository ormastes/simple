# Actual retained compiler source traversal observations V1

This handwritten manual mirrors the executable unit spec. Runtime execution,
SPipe generation and admission are NOT_RUN.

The compiler's existing retained parse loop consumes two real source modules.
The observed route must retain the actual parsed function names also committed
to `CompilerDriver.ctx.modules`, one source-input read per source and an exact
immutable source subject. Each read uses the existing
`SemanticQueryReadManifestV1` representation and remains `Unknown`.

The existing `parse_all_impl` entrypoint selects observation when the compiler
context config contains `scv_source_observations_v1: "1"`. The default retained
phase produces the same parsed module without allocating an observation owner.
Every new parse traversal retires an earlier observed generation. The direct observed method uses the
same loop, rather than parsing a second time to produce a receipt.

Expected negative behavior:

- Editing a returned subject or function-name array cannot mutate the retained
  receipt's subject or observations.
- Changed content, omitted/additional source rows, a foreign driver, changed
  selected frontend context and a newer traversal generation invalidate a
  receipt projection.
- Duplicate source paths or module names are refused before parsing.
- An actual malformed program cannot issue a successful observation receipt.
- An entry-selected closure is refused because it does not traverse the full
  retained input list described by this profile.
- Closing the receipt revokes projection and a second close cannot revive it.

This is source-input and parsed-function observation evidence. It neither
resolves the transitive import/reexport universe nor proves trait, aspect,
macro/CTFE or body dependency completeness. No semantic cache authority is
issued and no accepted-root publication is enabled.
