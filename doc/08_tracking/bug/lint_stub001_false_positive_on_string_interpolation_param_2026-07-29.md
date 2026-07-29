# Bug: lint STUB001 false-positives on a param used only via string interpolation

- **Date:** 2026-07-29
- **Status:** open
- **Severity:** low (false-positive lint error, no wrong runtime behavior)
- **Found by:** lane sbom-emission, mission-critical robustness campaign

## The defect

`bin/simple lint` rule STUB001 ("trivial ... return with N unused param(s)")
flags a function whose entire body is a single string-interpolation literal
that references its only parameter **only inside the `{...}` template**, e.g.:

```
fn file_package_id(index: i64) -> text:
    "SPDXRef-Package-File-{index}"
```

Lint reports:

```
error[STUB001]: trivial string ("SPDXRef-Package-File-{index}") return with 1 unused param(s)
```

`index` **is** used — it is substituted into the string at the `{index}`
site. The parameter is not unused.

## Root cause

`src/compiler/35.semantics/lint/stub_impl.spl`:
- `classify_trivial` (tag == 3, string literal) reads the literal's raw
  template text verbatim, unexpanded.
- `expr_references_param` / `stmt_references_param` walk `left`/`right`/
  `args`/`stmts` of the expression AST looking for a bare-identifier node
  (tag == 6) matching a parameter name, but a string-literal AST node's
  interpolation holes are not exposed through any of those accessors — so the
  param reference inside `{index}` is invisible to this specific checker,
  even though the same interpolation is correctly compiled/evaluated
  everywhere else in the toolchain.

## Impact / workaround

Cosmetic only. Any short "build an id/label from one interpolated param"
helper trips this. Workaround used in this lane
(`src/lib/nogc_sync_mut/sbom/sbom_generator.spl`, `file_package_id` /
`vendor_package_id`): split into two statements (`val id = "...{param}..."`
then `id`) — `get_single_trivial_expr` requires `stmts.len() == 1`, so a
two-statement body isn't inspected at all. Behavior is unchanged; this only
dodges the checker's single-statement-body precondition.

## Suggested real fix

Teach `expr_references_param` (or a sibling walk invoked from
`classify_trivial`'s string-literal branch) to also scan the string literal's
interpolation-hole identifiers, not just AST child expressions.
