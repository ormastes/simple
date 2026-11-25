# Bug: lint STUB001 false-positives on a param used only via string interpolation

- **Date:** 2026-07-29
- **Status:** resolved (fix landed same day in `ef086dc25dd`; verified end-to-end 2026-11-25 — see Resolution below)
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

## Resolution (2026-11-25)

**Root cause (confirmed):** as diagnosed above. The lint CLI path
(`run_lint_file` → `parse_module_silent_checked` →
`_parse_module_with_diagnostics`) never calls
`expand_string_interpolations` (that pass only runs on the compile/frontend
path, `core_frontend_parse_legacy_reference`), so at lint time an interpolated
literal is still a bare `EXPR_STRING_LIT` (tag 3) whose `s_val` holds the raw
template text verbatim (`"SPDXRef-Package-File-{index}"`), with no child AST
nodes for the `{...}` holes. The param-usage walk
(`expr_references_param`/`stmt_references_param`) only recursed into
left/right/args/stmts, so a param referenced solely inside a hole was
invisible and STUB001 fired.

**Fix (already landed):** commit `ef086dc25dd` ("fix(lint+desugar): STUB001
sees interpolation holes", 2026-07-29 — same day this doc was filed) added
exactly the suggested fix to `src/compiler/35.semantics/lint/stub_impl.spl`:
- `expr_references_param` gained a tag-3 arm that calls
  `string_lit_references_param` on the raw template (skipped for raw strings,
  `i_val == 1`, which never interpolate).
- `string_lit_references_param` scans for `{...}` holes with `{{`/`}}`
  escape handling and brace-depth tracking for nested braces.
- `interpolation_hole_references_param` tokenizes the hole text on
  non-identifier characters and compares each identifier run against the
  param names (handles compound holes like `{a + b}`).

The fix survived the later WP-8 refactor and accessor-routing sweeps intact
(verified by diffing `ef086dc25dd..HEAD` for the file on 2026-11-25). The
status field above was simply never updated; the doc lingered as "open".

**Evidence (2026-11-25, worktree on `release/1.0.0` @ `e803fa9762c`):**
- `./bin/simple lint` on the doc's exact repro
  (`fn file_package_id(index: i64) -> text:` / `"SPDXRef-Package-File-{index}"`):
  **clean, no STUB001**.
- Genuine-unused control (`fn label_for(index: i64) -> text:` / `"literal"`):
  **STUB001 still fires** (no over-correction).
- Escaped braces (`"literal {{index}} brace"`): STUB001 still fires —
  `{{...}}` is literal text, not a hole.
- Raw string (`r"literal {index} brace"`): STUB001 still fires — raw strings
  never interpolate.
- Regression spec `test/01_unit/compiler/lint/stub_impl_spec.spl` (Test Group
  1b, REQ-COMPILER-LINT-STUB-011..016): **60/60 passed**.

**Evidence limits:** lint runs were executed with the 2026-11-23 bootstrap
seed (`build-commit 1343b77bbaa7`) driving the worktree's own
`src/app/cli/lint_entry.spl` + `src/compiler/**` lint source in interpreter
mode (the seed refuses a Rust lint fallback, so the lint logic exercised is
the checked-in Simple source, not a baked-in copy). The older 2026-10-05
deployed seed cannot parse the current `src/lib` grammar at all and was
unusable. No pure-Simple self-hosted `bin/release` binary was available on
this host; none of this changes the verdict, since the lint rule logic under
test is the source tree itself.

**Workarounds now unblocked (left in place, NOT reverted in this change):**
`src/lib/nogc_sync_mut/sbom/sbom_generator.spl` `file_package_id` /
`vendor_package_id` still use the two-statement dodge (`val id = "...{param}..."`
then `id`) described above. The dodge is no longer necessary — a
single-expression `"SPDXRef-Package-File-{index}"` body lints clean — but the
workaround is behavior-neutral, so removing it is optional cleanup for a
future sbom lane, not part of this bug's scope.
