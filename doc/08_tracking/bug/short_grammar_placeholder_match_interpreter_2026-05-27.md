# Short Grammar Placeholder Match Interpreter Failure

Date: 2026-05-27

## Summary

Placeholder short grammar in a `match` selector currently checks but fails when
run by the interpreter.

## Repro

```simple
val result = [1, 2, 3].map(match _1:
    case 1: 10
    case 2: 20
    case _: 30
)
```

Observed during focused verification:

```bash
src/compiler_rust/target/debug/simple check test/unit/compiler_core/parser/short_grammar_interpreter_spec.spl
src/compiler_rust/target/debug/simple test test/unit/compiler_core/parser/short_grammar_interpreter_spec.spl --mode=interpreter --clean
```

The file check passed, but the interpreter spec failed after adding the
placeholder-match case.

## Impact

Do not rewrite callbacks such as `\value: match value:` to `match _1:` until
interpreter execution supports this form.
