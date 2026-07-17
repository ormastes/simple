# Brace-containing string literal corrupts lowering scope across functions

Date: 2026-06-12
Status: source fixed; exact regression execution pending
Severity: P2
Related: `short_grammar_placeholder_interpolation_2026-05-27.md`,
memory note "Brace Interpolation in Literals"

## Symptom

A function whose body returns a string literal containing braces (e.g. `" { "`)
poisons HIR lowering for the whole file: lowering reports an *unrelated*
variable from a *different* function, and the entry point disappears.

## Minimal repro (verified 2026-06-12 on freshly redeployed stage4)

```simple
fn open_brace(x: text) -> text:
    " { "

fn main():
    val ob = open_brace("unused")
    val rule = ".a" + ob + "color: red" + " } "
    print("RULE: [" + rule + "]")

main()
```

`bin/simple run` output:

```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error:
  Unknown variable: rule while lowering open_brace
error[E1002]: function `main` not found
```

Note `rule` is local to `main` but is reported while lowering `open_brace` —
scope bleed between functions triggered by the brace literal. In larger files
the failure can surface instead as concatenation appearing to substitute a
variable's *name* rather than its value.

## Real-world hit

`_norm_rule_open_brace`/`_norm_rule_close_brace` in
`src/lib/gc_async_mut/gpu/browser_engine/html_string_parser.spl` returned
`" { "` / `" } "` for CSS-nesting normalization; the spec
`browser_renderer_spec.spl` CSS-nesting tests failed until the literals were
replaced. Workaround now in tree (`_norm_emit_rule`): build the rule from a
placeholder template (`"... OPENBRACE ... CLOSEBRACE"`) and `.replace()` the
tokens with `"{"` / `"}"` at runtime.

## Expected

A string literal containing `{`/`}` with no `{identifier}` interpolation form
inside must lower as plain text and never affect other functions' scopes.

## Suggested direction

Audit interpolation detection in the lexer/lowering: a lone `{` followed by
whitespace (no identifier) should not open an interpolation region; lowering
errors inside one function must not refer to locals of another.

## Current-source audit (2026-07-17)

The current normal flat bridge already falls back to a plain literal when an
interpolation fragment is invalid or braces remain unmatched. The dormant
bootstrap HIR helper also produces no interpolation parts for the exact
unmatched `" { "` opener, but it has no live call root and therefore is not
evidence that the historical cross-function scope-corruption reproduction is
fixed. No speculative bootstrap-helper change is retained in this lane.

The parity harness now retains both forms. The normal `brace_literal_scope`
case is the native-entry adaptation. With `NATIVE_OPEN_BUG_REPROS=1`,
`brace_literal_scope_exact` preserves Unit `main` and the trailing top-level
`main()` call so `_expr_N` restoration and the `functions.contains("main")`
branch cannot be adapted away. Both expect normalized output
`RULE:[.a{color:red}]`. The exact case remains deliberately opt-in and red
until Linux execution proves the active source fix preserves scope isolation
and the entry point.

The focused core CI lane additionally executes
`test/01_unit/compiler/frontend/interp_fragment_sticky_error_spec.spl`, which
pins speculative-fragment error cleanup and current-source HIR scope isolation.
The bootstrap portability audit prevents that test, its workflow triggers, or
its interpreter-mode invocation from being silently dropped. This is supporting
coverage only: the full CLI parity reproduction below remains the closure gate.

## Root fix (2026-07-17)

The corruption was in the Rust seed f-string lexer, not empty-map freshness.
While scanning a possible `{...}` interpolation in a single-line string,
`scan_fstring_impl` treated the outer closing `"` as the start of a nested
string. For the exact source it therefore scanned from `" { "` across the
next function until the later `}` in `" } "`, attaching `main`'s `rule`
expression to `open_brace` and consuming the real entry point.

The shared scanner now stops and backtracks when a top-level unescaped `"`
closes a non-triple f-string. Triple f-strings and escaped nested quotes retain
their existing behavior. The exact source is pinned both as a lexer-boundary
regression and as a parser-to-HIR scope/entry-point regression. The pure-Simple
lexer already stopped unmatched interpolation lookahead and required no change.
Independent `{}` literals were also traced through pure-Simple MIR and both
runtime owners; each evaluation allocates a fresh dictionary, so the reverted
`Map.new()` caller rewrite remains correctly absent.

## Runtime verification (2026-07-17)

Before the source fix, the exact `bin/simple run` repro matched byte-for-byte:
`HIR lowering error: Unknown variable: rule while lowering open_brace` followed
by `error[E1002]: function 'main' not found`. Post-fix seed/CLI execution has
not been run in this lane; the opt-in parity case remains known-red until that
authorized execution succeeds.

Discarded candidate `f06e5829` replaced the frontend bridge's brace-initialized
maps with explicit `Map.new()` construction; `0f535b099788` correctly reverted
that caller workaround. It did not repair the seed scanner that consumed the
cross-function source. The scanner fix above is the active fix; the exact
opt-in Linux parity case remains its closure gate.
