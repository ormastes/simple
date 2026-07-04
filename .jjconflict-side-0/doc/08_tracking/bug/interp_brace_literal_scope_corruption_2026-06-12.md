# Brace-containing string literal corrupts lowering scope across functions

Date: 2026-06-12
Status: open (workaround in place)
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
