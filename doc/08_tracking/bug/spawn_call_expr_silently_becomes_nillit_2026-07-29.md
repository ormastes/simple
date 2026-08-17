# Bug: `spawn(...)` call expressions silently lower to `HirExprKind.NilLit` on the bootstrap seed frontend — the callee and every argument are discarded with zero diagnostic

**Date:** 2026-07-29
**Status:** FIXED 2026-08-17 — `EXPR_SPAWN` (and its two silent siblings
`EXPR_AWAIT`, `EXPR_YIELD`) now have real dispatch arms in
`convert_flat_expr`. See "Resolution (2026-08-17)" at the bottom.
**Found:** side-finding while lane G8 (`transfer-share`, mission-critical
robustness campaign) wrote a spec exercising a real `spawn(...)` call site
**Area:** compiler / frontend (`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`) — bootstrap-seed-only parsing bridge
**Severity:** High — silent, undiagnosed loss of program semantics; the call's side effects (and any arguments' evaluation) simply never happen, with no error, warning, or lowering-error entry anywhere

## Finding

On the current Rust-built bootstrap seed binary (`bin/simple` → confirmed via
`bin/simple --version`'s own "this Rust-built Simple binary is a bootstrap
seed only" warning; the pure-Simple self-hosted binary was not available to
build/verify against in this session), a bare call to a function named
`spawn` — e.g. `spawn(w)` as a statement — does not lower to
`HirExprKind.Call` at all. It lowers to `HirExprKind.NilLit`, discarding the
callee reference and every argument, with `HirLowering.errors.len()` staying
`0` (no diagnostic recorded anywhere reachable from `parse_full_frontend`).

Repro (isolated via `test/01_unit/compiler/semantics/transfer_share_semantic_spec.spl`'s development, not currently a landed repro spec — see below):

```
use std.actor.spawn.{spawn}

class Worker:
    id: i64

fn boot(w: Worker):
    spawn(w)
```

Debug instrumentation (temporarily added and removed during investigation)
showed, for `boot`'s single-statement body:

```
body.stmts.len=1  body.has=false     # one statement present, as expected
stmt.kind = Expr(expr)               # correctly an expression statement
expr.kind = HirExprKind.NilLit       # NOT Call — the whole call vanished
```

For comparison, an otherwise-identical fixture calling a plain (non-keyword)
function `identity(w)` in the same position correctly lowers to
`HirExprKind.Call(NamedVar(_, "identity"), [NamedVar(_, "w")], [])`.

The same collapse happens whether or not `spawn` is imported from the real
stdlib (`use std.actor.spawn.{spawn}`, which resolves to
`src/lib/nogc_async_mut/actor/spawn.spl:112`,
`fn spawn(handlers: HandlerTable) -> ActorRef`) — the loss happens upstream
of symbol resolution entirely.

A **declaration** named `spawn` is a separate, already-visible failure mode
on the same seed: `fn spawn(...)` is a hard parse error
(`[parser_error] ... expected Ident, got spawn 'spawn'`), because `spawn`
lexes as the reserved `KwSpawn` token
(`src/compiler/10.frontend/lexer_types.spl:60`), never `TOK_IDENT`. That much
at least surfaces a diagnostic. The **call-expression** collapse described
here does not — it is strictly worse, because it looks like successful,
silent no-op compilation.

## Root cause (traced, not fixed)

`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`'s own header
says it is "the bootstrap-safe frontend path when the newer parser surface
is unavailable" — i.e. exactly the path this seed binary runs.  That file
already has this *exact* failure class independently rediscovered and
individually patched at multiple other sites, per its own comments:

- "Bug (array/string slice-index silently -> NilLit -> SIGSEGV)"
- "through to the generic fallback (NilLit), discarding every statement"
- "into a no-op `NilLit` expression statement — the deferred statement's effect [lost]"
- "fell through to the final `else` and became NilLit -- e.g. a bitfield read's tail..."
- "became NilLit -- e.g. `x += 5` compiled to a no-op..."

i.e. this file has a *generic* "unhandled/unmapped node kind → silently
substitute `ExprKind.NilLit`" fallback, and every instance found so far has
required an individual, targeted patch (there is no single fix for the
fallback itself — see the file's own accumulated comment trail for the
pattern). `spawn(...)` call expressions are simply one more, previously
unpatched instance of the same fallback. The exact dispatch site that fails
to route a `spawn`-headed call node into the normal call-conversion path was
not pinned down to a single line in this investigation (would require
tracing `compiler.core.parser`'s flat/index-based AST node-kind tags for a
`KwSpawn`-led primary expression, which was out of scope for the lane that
found this).

## Why this matters beyond one keyword

This directly blocks any HIR-level semantic check keyed on recognizing
`spawn(...)` call sites (e.g. the mission-critical robustness campaign's G8
"transfer-share" lane,
`doc/01_research/language/simple_vs_rust_safety_property_audit_2026-07-28.md`)
on the seed binary: there is no `Call` node to inspect — the whole
expression, including its arguments, has already vanished by the time HIR
lowering runs, and there is no diagnostic to grep for either. A
SafetyChecker rule cannot be "wrong" about a spawn call it never sees; it is
simply never exercised on the seed.

It is unknown whether this affects the pure-Simple self-hosted frontend
(`compiler.core.parser`'s "newer parser surface", per the bridge file's own
header, is presumably NOT this bootstrap-safe bridge) — that binary was not
buildable/available in this session to check. Given the real stdlib
(`src/lib/nogc_async_mut/actor/spawn.spl` and its callers) is presumably
compiled and exercised routinely via the self-hosted toolchain in normal
development, this is most likely SEED-ONLY. Re-verify against a freshly
built self-hosted `bin/simple` before assuming this affects production
compiles.

## Suggested fix direction (not attempted)

Find the flat-AST node-kind dispatch in
`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` (or its caller,
`compiler.core.parser`'s expression-node classification) responsible for
primary/call expressions and add explicit handling for a `KwSpawn`-headed
call, mirroring how the file's other individually-patched NilLit sites were
each fixed (return the real `Expr(kind: ExprKind.Call(...))` shape instead
of falling through to the generic `NilLit` default). Add a loud diagnostic
to the generic fallback itself as a follow-up hardening measure — silent
NilLit substitution is a recurring root cause across this file and a single
"unhandled node kind: {kind}" warning at the fallback site would have
surfaced every one of these individually-discovered bugs at write time
instead of requiring a user-visible repro each time.

## Relation to lane G8 (transfer-share)

Lane G8 implemented `safetychecker_check_transfer_module`
(`src/compiler/35.semantics/safety_checker.spl`, rule E1049) exactly as
designed — a `Call` node with a `spawn`-named `NamedVar` callee and a bare
non-`iso` class-typed `NamedVar` argument is correctly flagged. Its spec,
`test/01_unit/compiler/semantics/transfer_share_semantic_spec.spl`, proves
this against **hand-built HIR** (the same technique
`test/01_unit/compiler/borrow/iso_move_pipeline_spec.spl` uses for an
analogous parser-layer gap) specifically because real `spawn(...)` source
text cannot reach that code path on this seed until this bug is fixed. The
rule is not blocked on this bug to be correct, but it IS blocked on this bug
to ever fire against real compiled source on the seed.

---

## Resolution (2026-08-17)

**Classified by CONTENT, not by commit ancestry.** At the start of this lane the
defect was still LIVE in `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`:
`convert_flat_expr`'s dispatch chain had arms for 40+ tags and **none** for
`EXPR_SPAWN`. An earlier lane (NIL1) had only made the *fallback* loud
(`flat_bridge_report_unhandled_node`, `convert_nodes.spl:195`) — the expression
was still discarded, just noisily. Its own comment said so:
"EXPR_SPAWN has no dispatch arm above".

### Direct reproduction (9s, `bin/simple run`, no test-runner session)

```
PROBE_SPAWN_KIND=NilLit
[parser_error] line 3:1: flat AST bridge: unhandled expr node kind (tag=39) silently converted to nil/no-op ...
```

### Root cause

`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:1240` — the
`if tag == EXPR_DICT_COMP:` arm was the last one before the generic
`else:` catch-all at (pre-fix) `:1261-1267`. `EXPR_SPAWN` (tag 39) fell
straight into it. The node is produced unconditionally from ordinary source by
`src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl:477-479`
(`spawn` lexes as reserved `KwSpawn`, token kind 197, never `TOK_IDENT`).

### Sibling constructs with the identical defect shape (class axis)

Same file, same catch-all, all produced from real source text by
`primary_expr.spl`:

| tag | construct | builder | status after this lane |
|---|---|---|---|
| 39 `EXPR_SPAWN` | `spawn(w)` | `primary_expr.spl:479` | **FIXED** |
| 37 `EXPR_AWAIT` | `await f()` | `primary_expr.spl:439` | **FIXED** |
| 38 `EXPR_YIELD` | `yield 1` | `primary_expr.spl:444` | **FIXED** |
| 44 `EXPR_DO_BLOCK` | `do:` / `ce N:` | `primary_expr.spl:485,496` | still unhandled (loud fallback only) |
| 45 `EXPR_ATOM` | `` `sym `` | `primary_expr.spl:501` | still unhandled; `ExprKind` has no Atom variant |
| 50 `EXPR_NEW` | `new expr` | `primary_expr.spl:474` | still unhandled; `ExprKind` has no New variant |

`do:`/atom/`new` are left unfixed deliberately: the target `ExprKind` variant
either does not exist or the mapping is a semantic decision, not a mechanical
one. They remain covered by the loud fallback, and
`convert_nodes_loud_fallback_spec.spl` was repointed at `do:` so that spec still
probes a genuinely unhandled kind.

### Fix shape — why `Call`, not `ExprKind.Spawn`

`ExprKind.Spawn` exists in `parser_types_expr.spl`, but emitting it would have
traded a silent drop for a hard error: `20.hir/hir_lowering/expressions.spl`'s
`lower_hir_expr` has **no** `case ExprKind.Spawn` arm and falls to
`case _: self.error("unsupported expression kind", ...)`. Every live consumer of
a spawn site matches the callee NAME on a plain `Call`
(`30.types/type_system/checker.spl`, `builtin_registry.spl`,
`50.mir/mir_effects.spl`, and rule E1049 at
`35.semantics/safety_checker.spl:907`). So the bridge rebuilds
`ExprKind.Call(Ident("spawn"), [operand])`. `Await`/`Yield` ARE handled by HIR
lowering (`expressions.spl:954-966`) and are emitted as their real nodes.

This unblocks lane G8's E1049 rule against real compiled source for the first
time — previously there was no `Call` node for it to inspect.

### Evidence

Reproducing spec: `test/01_unit/compiler/frontend/flat_bridge_spawn_call_expr_spec.spl`
- BEFORE: `1 example, 1 failure` — `assert_equal failed: expected Call(spawn,1), got NilLit`
  `SPEC FILE VERDICT: ... declared>=1 executed=1 passed=0 failed=1 dropped=0`
- AFTER: `1 example, 0 failures`
  `SPEC FILE VERDICT: ... declared>=1 executed=1 passed=1 failed=0 dropped=0`

Class-detection spec: `test/01_unit/compiler/frontend/flat_bridge_keyword_expr_nillit_class_spec.spl`
- BEFORE: `4 examples, 3 failures`
  `SPEC FILE VERDICT: ... declared>=4 executed=4 passed=1 failed=3 dropped=0`
  (spawn, await, yield all collapsed; the ordinary-call control passed — so the
  spec is not vacuous)
- AFTER: `4 examples, 0 failures`
  `SPEC FILE VERDICT: ... declared>=4 executed=4 passed=4 failed=0 dropped=0`

Regressions re-run after the fix:
- `convert_nodes_loud_fallback_spec.spl` 4/4 (after repointing its spawn example at `do:`)
- `flat_ast_child_ownership_spec.spl` 7/7
- `flat_ast_speculative_diagnostics_spec.spl` 1/1
- `transfer_share_semantic_spec.spl` 8/8
- `flat_ast_address_of_spec.spl` 1 failure — **pre-existing**, proven by re-running
  it against `git show HEAD:convert_nodes.spl` restored in place: identical
  `passed=1 failed=1`. Unrelated (reference-syntax -> MIR Ref).

### Not proven

- `bin/simple test` could not produce a `Results:` line for these specs: three
  attempts were SIGTERMed (rc=143, one with a 0-byte log) under host load
  averaging 60-90 with a 6-slot queue. All verdicts above come from
  `bin/simple run <spec>`, which executes the `it` bodies and prints an explicit
  `SPEC FILE VERDICT` / `N examples, M failures` line.
- Not exercised end-to-end through a *native/JIT compile* of a spawning program;
  only the frontend bridge conversion is pinned.
- `bin/simple` here is the Rust seed, but that is irrelevant for this fix: the
  bridge is pure Simple, read as source at every run, and the probe above shows
  the seed executing the changed code path.
