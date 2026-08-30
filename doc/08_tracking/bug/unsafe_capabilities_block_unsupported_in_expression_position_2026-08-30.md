# `unsafe(capabilities: [...])` is a STATEMENT-only form; in expression position it silently becomes a call and breaks LLVM codegen

**Date:** 2026-08-30
**Status:** OPEN (parser feature gap). Call sites worked around; the gap is NOT fixed.
**Found on:** Windows MSVC Stage 2, but the defect is **platform-independent**

## Symptom

Stage 2 native-build aborted with 3 files failing, all identically:

```
llvm codegen: semantic: llvm global load referenced undeclared symbol `ffi`
```

- `src/compiler/20.hir/hir_lowering/_Expressions/expression_support.spl`
- `src/compiler/50.mir/_MirLowering/function_lowering.spl`
- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`

## Root cause

`unsafe(capabilities: [...])` is parsed **only in `parse_statement()`**
(`src/compiler/10.frontend/core/parser_stmts.spl:753-800`). The expression
parser (`parser_expr.spl`) has no `unsafe` handling at all — it does not carry
block-form keywords generally (no `if`/`match` expression forms live there
either).

So in expression position:

```simple
val configured = unsafe(capabilities: [ffi]):
    rt_env_get("SIMPLE_TRACE_DICT_ELEM")
```

`unsafe` parses as an ordinary identifier, `(capabilities: [ffi])` as a call
with a named argument, and `[ffi]` as an array literal whose element is the
**identifier** `ffi`. Nothing declares `ffi`, so codegen emits a global load of
it. This is the known class guarded by
`scripts/check/check-predicate-parser-native-build.shs`: an undeclared name is
only a WARNING on the interpreter path and a hard ERROR in LLVM codegen, so the
construct looks fine until a native build runs.

The interpreter-path leniency is why this reached Stage 2 rather than being
caught at authoring time.

## Evidence that this is exactly the trigger

The failing set and the expression-form set are the SAME three files:

```
$ grep -rln "= unsafe(capabilities:" src/compiler/   # -> exactly the 3 failures
```

Statement-form use is overwhelmingly dominant and unaffected: 286
`capabilities: [ffi]`, 33 `[ffi, raw_ptr]`, plus others, across 25 files.

## What was done (workaround, not a fix)

The 7 expression-position uses in those 3 files were rewritten to the supported
statement form — declare first, assign inside the `unsafe` region:

```simple
var configured: text = ""
unsafe(capabilities: [ffi]):
    configured = rt_env_get("SIMPLE_TRACE_DICT_ELEM")
```

Semantics are unchanged: same capability region, same calls, same values. In
`function_lowering.spl` four adjacent single-call regions became one region
containing four assignments, which is equivalent and marginally tighter.

Per CLAUDE.md this is recorded rather than silently normalized: *"When a short,
safe grammar or compact expression form fails ... fix it or record a concrete
bug/feature request instead of silently normalizing the workaround."*

## The actual fix (NOT done here)

Support `unsafe(capabilities: [...])` (and bare `unsafe:`) in expression
position, producing the same `ExprKind.UnsafeBlock` the statement path already
builds — HIR lowering (`expression_core.spl:847`) and the flat-AST bridge
(`convert_nodes.spl:1201`) already handle that node correctly and need no
change. This was not attempted here because the expression parser carries no
block-form keyword support at all, so it is a cross-cutting parser feature
rather than a local addition, and this lane's job was to reach Phase 3.

**Better still, and cheaper:** make an unknown identifier in a `capabilities:`
list a parse/semantic ERROR. The HIR lowerer already rejects unknown capability
NAMES (`expression_core.spl:848-850`, "Unknown names are a diagnostic here,
never silently dropped") — but only once the construct is recognised as an
unsafe block at all. The failure mode here is that it never becomes one.

## References

- `src/compiler/10.frontend/core/parser_stmts.spl:753-800` (statement-only impl)
- `src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl:847`
- `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:1201`
- `scripts/check/check-predicate-parser-native-build.shs` (same defect class)
- `doc/08_tracking/bug/stage2_native_build_has_paren_idx_undeclared_global_2026-08-09.md`
