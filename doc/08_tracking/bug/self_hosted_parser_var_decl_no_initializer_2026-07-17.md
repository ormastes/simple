# self-hosted parser: `var name: Type` without initializer rejected

**Severity:** high (blocks whole entry closures from parsing)
**Found:** 2026-07-17 during stage3 entry-closure hang diagnosis
**Status:** open
**Component:** pure-Simple parser `parse_var_decl_stmt()` — `src/compiler/10.frontend/core/parser_stmts.spl:645-682`

## Symptom

A type-annotated `var` declaration with no initializer, assigned later inside
`if`/`elif`/`match` arms, fails to parse on the self-hosted parser:

```simple
var offscreen: Engine2D
if cond:
    offscreen = make_a()
else:
    offscreen = make_b()
```

`[parser_error] expected =, got Newline`. The seed grammar accepts this form.

First hit at `src/std/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:586`, which
blocks the whole hosted-WM entry closure in phase 2 (see
`stage3_host_entry_closure_retains_unresolved_modules_2026-07-11.md`, 2026-07-17
findings). The same pattern exists in `src/lib/nogc_async_mut/http_server/worker.spl:184,191`,
`static_file.spl:397,505`, `range.spl:64-65`, `spm_service.spl:24-26`,
`test_daemon/daemon.spl:438` — those files simply haven't been in a tested
native-build closure yet.

## Reproduction

Minimal standalone repro (10 lines, no OS/GUI closure needed):
`scratchpad/s4_stage3/minrepro/varnoinit.spl` from the diagnosis session — any
file with `var x: T` + later assignment.

## Root cause

`parse_var_decl_stmt()` unconditionally requires `=` after the optional type
tag; there is no declare-without-initializer branch.

## Fix requirements (why this is not a one-line parser change)

Parser tolerance alone is not enough: a correct fix needs a "no initializer"
representation threaded through HIR lowering, MIR lowering (default-value or
definite-assignment handling), and the interpreter's decl-eval path, so the
declared-but-unassigned local neither crashes nor silently reads garbage.
Must fail loud on read-before-assign or zero-init per seed semantics — match
what the seed does, verified by oracle probes.
