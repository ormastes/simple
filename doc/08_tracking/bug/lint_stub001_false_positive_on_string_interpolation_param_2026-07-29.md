# Bug: lint STUB001 false-positives on a param used only via string interpolation

- **Date:** 2026-07-29
- Status: CLOSED — ALREADY-FIXED by content (2026-08-17); see the verification
  section at the end of this file. The earlier "OPEN (P3) / re-verified by
  triage shard 02" line was a stale-doc classification, not a source finding.
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

## Verification 2026-08-17 (w02/s4 lane) — ALREADY FIXED, closing on content

Classified by CONTENT of current source (session brief CORRECTION 1).

`src/compiler/35.semantics/lint/stub_impl.spl` now implements the interpolation
scan this bug asked for:

- `:641` `fn interpolation_hole_references_param(hole: text, params: [text]) -> bool`
  — "Check whether any identifier token inside an interpolation hole's raw ..."
- `:674` a scanner over "a string literal's raw template text for `{...}`
  interpolation" holes, `:691` "Start of an interpolation hole — scan to the
  matching close", calling the predicate at `:708`.
- `:765-769` the STUB001 decision site, whose comment names **this bug doc by
  filename**: "String literal: params referenced only inside `{...}`
  interpolation ... (see doc/08_tracking/bug/lint_stub001_false_positive_on_string_interpolation_param_2026-07-29.md)".
  `:769` additionally handles the raw-string case (`i_val == 1`, `r"..."` never
  interpolates), which the original report did not ask for.

The tracking-row evidence "doc Status open, no interpolation-scan added" is
**stale** — the interpolation scan is present, reachable from the STUB001 path,
and explicitly attributed to this bug.

**Verdict: ALREADY FIXED (stale doc). No patch applied.**
Not proven: this lane did not run `bin/simple lint` against
`src/lib/nogc_sync_mut/sbom/sbom_generator.spl` to observe the absence of the
warning — a single-file lint costs ~12s startup plus a superlinear per-decl term
(see `lint_single_file_superlinear_timeout_on_line_count_2026-08-06.md`, still
live) and the host is running a live bootstrap at 164 concurrent `simple`
processes. The close rests on source content.
