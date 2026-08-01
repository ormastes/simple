# `_simple_web_layout_compose_retained` references an undeclared `animation_time_ms`

- **Status:** FIXED (2026-08-01)
- **Severity:** Medium — hard stage4 build abort; nested-iframe animation never propagated
- **Found by:** stage4 bootstrap, alongside
  `if_val_expression_binding_lost_hir_2026-08-01.md` (different root cause, same run)

## Symptom

```
error: codegen: semantic: llvm global load referenced undeclared symbol `animation_time_ms`
    -> src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl
```

## Root cause

This one is **not** a compiler bug. It is a genuine undefined identifier in the
source, masked until LLVM emission.

`_simple_web_layout_compose_retained` (declared at line 1405) took 21 parameters,
**none** of them `animation_time_ms`. Its body nevertheless referenced that name
exactly once, at line 1578, forwarding it into the nested-iframe child render:

```
val child = _simple_web_layout_compose_document(
    child_html, content.width, content.height,
    vector_fonts, animation_time_ms, 0,
    ...
)
```

There was no parameter, no `val`, no `for`/`match` binding for that name anywhere
between lines 1405 and 1656. Because bootstrap builds run with `lenient_types`,
the unresolved name was rewritten into `HirExprKind::Global` with no diagnostic
(`hir/lower/expr/mod.rs:308-313`) and only failed at LLVM global emission.

Behaviour by engine on the unmodified source:

| path | result |
|---|---|
| `--backend=llvm` with `SIMPLE_BOOTSTRAP=1` | hard error naming the symbol, no location |
| same, **without** `SIMPLE_BOOTSTRAP=1` | correct `Undefined("undefined identifier: animation_time_ms")` |
| JIT (`simple <file>`) | compiles and silently yields `0` |

So the retained compose path could never propagate an animation clock into nested
iframe documents — it was reading a global that does not exist.

## Fix

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`:

- `_simple_web_layout_compose_retained` gains an `animation_time_ms: i64`
  parameter, placed with the other animation parameters (21 -> 22).
- `SimpleWebRetainedLayoutPreparation` gains an `animation_time_ms: i64` field, so
  the prepared/retained path can carry the clock; populated in
  `simple_web_layout_prepare_retained`, which already had the value in scope.
- All three call sites updated (all positional, all now 22 args):
  - `_simple_web_layout_compose_document` — forwards its own `animation_time_ms`.
  - `simple_web_layout_compose_prepared` — forwards `prepared.animation_time_ms`.
    (This caller had no animation clock of its own; the new struct field is what
    makes it available, rather than passing a fabricated constant.)
  - `simple_web_layout_rerender_retained` — forwards its own `animation_time_ms`.

`< 0` continues to mean "no animation time", matching the existing
`if animation_time_ms >= 0:` guards in this file.

## Evidence

Compiled with the patched seed, with a reachability harness so the function is
actually emitted (the file is a library, so a bare `compile` stops at
"native binary requires a main function" before codegen):

- original source: `error: codegen: semantic: llvm global load referenced undeclared symbol \`animation_time_ms\``
- patched source: that error is **gone**; the build advances through HIR and LLVM
  codegen to the link stage.

Independently localised by giving each of the 19 functions mentioning the name a
unique parameter name and observing which one the error followed, then confirming
the error vanished when only line 1578's identifier was changed — establishing
this as the sole instance of the defect in the file.

## Follow-up

`lenient_types` silently converting unresolved names to globals is what let a
plain undefined identifier reach LLVM emission. Tracked in the follow-up section
of `if_val_expression_binding_lost_hir_2026-08-01.md`.
