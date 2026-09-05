# Codegen fails on very large function body: _dispatch_function (236-arm match, 2497 lines)

- **Date:** 2026-07-27
- **Lane:** stage4 native-build (cranelift), full-CLI closure
- **Status:** open — blocks stage4 full-CLI build (last remaining compile blocker)

## Symptom
`native-build` of `src/app/office/sheets/formula.spl` fails:
```
codegen: Module error: 1 function body/bodies failed to compile: [_dispatch_function];
set SIMPLE_ALLOW_STUB_FALLBACK to emit empty stubs instead (unsafe)
```
`_dispatch_function` (formula.spl:4270-6767) is a single 2497-line function whose
body is one `match canonical_name:` with **236 quoted string arms** (Excel
function dispatch). It also first hit a 300s per-file compile TIMEOUT before the
codegen error surfaced (raised to 900s to get past the timeout).

## Assessment
Per project rule "Compiler auto-optimizes patterns — don't make users rewrite for
perf; fix it in the compiler": a 236-arm match SHOULD compile. This is a codegen
scalability limit on large function bodies / large string-match lowering, not a
user error. Regression window: grew with `15b03323ee feat(office): add full-size
Calc TUI UI access`.

## Two fixes
1. **Proper (compiler):** make codegen handle large match/function bodies (chunked
   lowering, or lower a big string-match to a table/hash dispatch instead of a
   linear IR chain). Codex/compiler territory.
2. **Workaround (source, to unblock deploy):** split `_dispatch_function` into
   category sub-dispatchers (math / stats / text / lookup / logical …), each a
   separate `fn` with a manageable arm count, called in sequence. Preserves exact
   behavior; gets each body under the codegen limit. Being applied to unblock the
   stage4 deploy while the compiler fix is pending.
