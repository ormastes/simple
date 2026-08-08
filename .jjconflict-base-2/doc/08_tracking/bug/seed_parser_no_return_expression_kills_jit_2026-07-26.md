# Rust seed has no `return` in expression position — `x ?? return e` hard-fails, and every function using it is dropped from the JIT

> **2026-07-26 hot-path rewrite landed + scope finding.** The one hot-path
> user (`_engine2d_draw_ir_render_batch_embedded`, draw_ir_adv.spl) is
> rewritten to statement form (plus its W1003 mutable-`Engine2D?` binding,
> the next opt-out in the same function); probe
> `probes/dg_draw_ir_embedded_jit.spl` verifies the "Unknown variable:
> return" line is gone. HOWEVER: the seed JIT is whole-program
> all-or-nothing (`exec_core.rs:629` + `codegen/jit.rs:84`) — 0 functions
> finalize for the showcase even after the fix, because two module-fatal
> blockers remain: (1) CODEGEN-AMBIGUOUS-METHOD on trait-object
> `core.draw_image_blend` (backend_emu_adv.spl:66,70, the filed
> RenderBackend trait-dispatch defect); (2) unresolved runtime externs in
> the deployed binary (`rt_directx_execute_readback_checked`,
> `rt_sleep_ms`). The web×headless cell therefore stays interpreted until
> seed rebuild/redeploy with current runtime symbols, per-function JIT
> granularity, or self-hosted redeploy.

- **ID:** seed_parser_no_return_expression_kills_jit_2026-07-26
- **Date:** 2026-07-26
- **Area:** `src/compiler_rust/parser/` (no `return` expression form) →
  `src/compiler_rust/compiler/src/hir/lower/` (`Unknown variable: return`)
- **Severity:** high — two distinct failures from one hole: a **correctness**
  failure (hard error) in an entry module, and a **performance** failure (silent
  JIT opt-out) for stdlib code. The idiom appears **178 times** across `src/`.
- **Status:** OPEN. Seed-only — the self-hosted compiler is already correct.

## Symptom 1 — hard failure in an entry module

`probes/coalesce_return_min.spl`:

```
fn maybe(v: i64) -> i64?:
    if v > 0: v else: nil

fn f(v: i64) -> i64:
    val x = maybe(v) ?? return -1
    x + 100

fn main():
    print "a={f(5)} b={f(-5)}"
```

```
$ bin/simple run probes/coalesce_return_min.spl
[INFO] JIT compilation failed, falling back to interpreter:
       HIR lowering error: Unknown variable: return while lowering f
error: semantic: variable `return` not found
rc=1
```

The program does not run at all. Both `val` and `var` forms fail identically.

## Symptom 2 — silent JIT opt-out for stdlib (this is the expensive one)

The same construct inside an already-loaded stdlib module degrades instead of
failing. Every run of the web showcase logs:

```
[INFO] JIT compilation failed, falling back to interpreter:
       HIR lowering error: Unknown variable: return
       while lowering _engine2d_draw_ir_render_batch_embedded
```

That function is `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:644`, the
**2D draw-command batch renderer** — the hot path for every DrawIR render. It
runs interpreted on every frame because of one line, `draw_ir_adv.spl:739`:

```
var offscreen = pending_offscreen ?? return _engine2d_draw_ir_render_outcome(eng, 0, batch.commands.len().to_i32(), "embedded-offscreen-not-created")
```

This is the cause of the `web × headless` showcase cell's failure.
**Confirmed 2026-07-26:** a full cell run (`web_standards_showcase_gui.spl`,
320x240, `SIMPLE_TIMEOUT_SECONDS=0`) emitted exactly this opt-out receipt at
startup, parsed the document correctly (`nodes=151 styles=151`), and then
failed to complete a single frame before an external 40-minute timeout killed
it (EXIT=124, no evidence line). A control run with
`SIMPLE_WEB_RENDER_BUDGET_MS=1800000` (30-minute paint budget) behaved
identically — same receipt, same healthy parse, killed at a 45-minute wall cap
with no evidence line — so the paint budget is not the limiting factor.
The earlier `reason=blank-or-uniform` verdict
(`web_render_budget_interpreter_gap_2026-07-25.md`) is the 10 s-budget face of
the same problem: the interpreted batch renderer cannot finish inside any
practical budget. Remaining unmeasured: the same cell on a self-hosted binary
(which parses `return`-expressions and can JIT the path).

## Root cause

The seed's parser has no `return` expression production at all — there is no
`Token::Return` / `Keyword::Return` handling anywhere under
`src/compiler_rust/parser/src`. In expression position `return` therefore lexes
as a plain identifier, and HIR lowering later fails to resolve it:

```
src/compiler_rust/compiler/src/hir/lower/error.rs:17
    #[error("Unknown variable: {0}")]
```

Hence the giveaway wording — it reports a *variable* named `return`.

## The self-hosted compiler is already correct

This is **not** a language-design gap. `return` is a first-class expression in
the pure-Simple compiler:

```
src/compiler/20.hir/hir_definitions.spl:484        Return(value: HirExpr?)
src/compiler/20.hir/hir_lowering/expressions.spl:691
    case ExprKind.Return(value):
        HirExprKind.Return(rv)
```

So `x ?? return e` is valid Simple that the real compiler lowers correctly, and
178 sites across `src/` depend on it. Only the bootstrap seed cannot handle it.

## Fix options

1. **Redeploy the self-hosted binary.** Closes this outright, no seed change.
   This is the direction `.claude/rules/bootstrap.md` already mandates ("default
   tooling = pure-Simple self-hosted binary; seed is bootstrap-only"). Blocked
   on the separate redeploy work.
2. **Teach the seed parser `return` as an expression** and lower it to the
   existing HIR `Return`. Contained, but it is seed surgery — and per
   `feedback_fix_spl_not_rust` the seed should not accrete features that the
   real compiler already has.

**Do NOT "fix" this by rewriting the 178 call sites into `if`-form.** The idiom
is valid, the real compiler handles it, and normalizing it would be exactly the
silent workaround `CLAUDE.md` prohibits.

## Reproduce

```bash
bin/simple run probes/coalesce_return_min.spl                  # rc=1, hard error
bin/simple run examples/06_io/ui/web_standards_showcase_gui.spl 2>&1 \
  | grep 'Unknown variable: return'                            # JIT opt-out
grep -rn '?? return' --include=*.spl src | wc -l               # 178
```

## Related

- `doc/08_tracking/bug/web_render_budget_interpreter_gap_2026-07-25.md` — the
  paint-budget verdict this may explain
- `doc/08_tracking/bug/stdlib_uses_letelse_ahead_of_deployed_compiler_2026-07-25.md`
  — same shape, opposite direction: there the stdlib used a form no *deployed*
  binary parsed. Both are the deployed-seed-vs-source skew.
