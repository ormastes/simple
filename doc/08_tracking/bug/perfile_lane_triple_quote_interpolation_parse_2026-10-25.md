# Per-module lane: multi-line interpolated triple-quoted string fails to parse

- Date: 2026-10-25
- Workaround tag: `WA-PERFILE-TRIPLE-QUOTE`
- Where: `src/compiler/60.mir_opt/_OptimizationPasses/engine.spl` `OptimizationStats.to_text`

## Symptom

Frozen stage2 (`wt-rel3-new/.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-gnu/simple.exe`)
running the per-module (non-flat, `SIMPLE_BOOTSTRAP` unset) native-build of
`src/app/cli/bootstrap_main.spl` fails in parse:

```
engine.spl: 126:22:unexpected token in expression: : ':'
```

The function body is a docstring `"""..."""` followed by a multi-line `"""`
string with `{...}` interpolation as the tail expression. The flat
(`SIMPLE_BOOTSTRAP=1`) lane accepts the same file. It was the only parse
failure across the full 1453-module closure.

## Workaround

Rewrote the literal as concatenated single-line interpolated strings.

## Fix needed

The lexer/parser used by the per-module lane must accept a multi-line
interpolated triple-quoted string after a docstring; then revert the WA.
