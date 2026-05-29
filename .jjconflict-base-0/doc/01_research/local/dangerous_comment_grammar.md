<!-- codex-research -->
# Dangerous Comment Grammar Local Research

Date: 2026-04-23

## Scope

Research stronger grammar and lint behavior for constructs that silently pass,
hide incomplete work, suppress checking, or catch broad cases. The user's core
direction is:

- `pass` and `pass_*` should require `(...)` with a useful explanation, or warn.
- `todo(...)` is not a "reason"; it should state what remains and ideally a hint
  for the next implementer.
- `case _:` should require `(...)` or a warning, because most matches can handle
  explicit variants instead of swallowing everything through `_`.
- Other dangerous whole-code constructs should also require comments.

## Current Implementation

The parser already accepts string arguments for pass-like constructs in both
statement and expression positions:

- `src/compiler/10.frontend/core/parser_stmts.spl`
  parses `pass`, `pass_todo`, `pass_do_nothing`, and `pass_dn` as statements.
- `src/compiler/10.frontend/core/parser_primary.spl`
  parses the same constructs as primary expressions.
- `src/compiler/10.frontend/core/ast_expr.spl`
  stores the optional string in `expr_s_val`.

Statement-form `pass_todo`, `pass_do_nothing`, and `pass_dn` currently call
`parser_warn("REQC001: ...")` when no string is present. Expression-form
pass-like nodes do not emit the parser warning, although the semantic lint can
detect their empty `expr_s_val`.

Bare `pass` has optional `pass("reason")` parsing but is not part of
`required_comment`. It is treated by the deprecated lint as `DEPR003` regardless
of whether a reason string exists.

`todo()` is not a language keyword or builtin today. A compile smoke with
`todo()` fails as an undefined identifier.

## Required Comment Lint Status

`src/compiler/35.semantics/lint/required_comment.spl` defines:

- `REQC001`: `pass_*` used without a comment string.
- `REQC002`: dangerous keyword call without a comment string.
- `check_required_comment(decl_indices)`.

Tests exist in `test/unit/compiler/semantics/lint/required_comment_lint_spec.spl`
for the AST lint, and tests in
`test/unit/compiler/frontend/required_comment_parse_spec.spl` simulate parser
warning behavior.

Missing wiring: `rg "check_required_comment(" src/compiler src/app src/lib`
finds only exports/tests, not production invocation from `bin/simple lint` or
compile diagnostics. `src/compiler/90.tools/lint/main.spl` registers `REQC001`
and `REQC002` in metadata, but does not run the AST lint.

## Existing Dangerous Keyword Registry

`src/compiler/10.frontend/core/dangerous_keywords.spl` currently contains:

- `dangerous_token_but_needs`
- `loss`
- `unsafe_cast`
- `raw_pointer`
- `unchecked`

This is a good seed list, but it mixes placeholder/test names with real safety
operations and lacks broader categories such as suppressions, wildcard arms,
raw FFI, inline assembly, unchecked conversions, and ignored error paths.

## Wildcard Match Local Findings

The codebase has many `case _:` occurrences in tests, docs, and production
code. Some are legitimate catch-all paths; others are placeholders or default
branches that hide future variants. There is already a `wildcard_match` lint in
`src/compiler/90.tools/lint/main.spl`, defaulting to `Allow`, and existing
easy-fix code can generate `case _: todo("handle remaining cases")`.

This suggests the least disruptive path is to extend the wildcard lint rather
than inventing a separate grammar first. A stricter grammar can come later after
the lint has measured and cleaned existing usage.

## Candidate Dangerous Constructs Beyond Pass

High-value candidates for forced explanations:

- `todo(...)`: must say what remains, not just "todo".
- `case _:` / `_ =>`: must explain why explicit cases are not used, or use a
  sanctioned terminal such as `compile_error("...")`.
- `unsafe_cast(...)`, `raw_pointer(...)`, `unchecked(...)`: must explain the
  invariant that makes the operation safe enough.
- `asm` / target-qualified asm fallback arms: require architecture, ABI, and
  safety rationale for catch-all or raw blocks.
- FFI boundary escape hatches: unchecked pointer conversion, untyped IPC/VFS
  payload conversion, raw handles, and layout assumptions.
- Lint suppressions and bypass annotations: `allow`, `bypass`, `skip_todo`, or
  similar attributes should carry an issue/code and rationale.
- Empty/no-op handlers: `pass_do_nothing`, `pass_dn`, empty `case Err(_)`,
  empty cleanup/defer paths.
- Error swallowing: `case Err(_): pass_dn(...)`, `case _: nil`, and branches
  that discard error details.

Lower-value candidates that should not be forced globally:

- `_` in ordinary destructuring when intentionally ignoring a value.
- `_` parameter names in callback signatures.
- `_` in test fixtures that immediately assert a concrete result elsewhere.

## Local Recommendation

Implement this as a staged lint policy, not an immediate syntax break:

1. Wire `check_required_comment()` into `bin/simple lint` and compile warning
   reporting.
2. Extend `REQC001` to cover bare `pass` with no string, and make
   `pass("reason")` accepted without `DEPR003`.
3. Add `todo("what remains", "hint")` or `todo("what remains; hint: ...")` as
   first-class placeholder syntax, with missing/weak text warning.
4. Upgrade `wildcard_match` to warn for `case _:` unless the arm has a rationale
   or is a recognized explicit failure path.
5. Expand dangerous keyword categories through data-driven registry metadata:
   name, category, required fields, default level, and accepted examples.

