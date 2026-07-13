# Issue #155 — array `.map()`/`.filter()`/`.fold()` native-build failure: classification

## Verdict: FEATURE-GAP — and NOT ORACLE-VERIFIABLE IN THIS ENVIRONMENT (primary reason for no-patch)

The task's own gate requires "native == oracle, matrix >=14/15" before any
fix lands. That gate is **unsatisfiable right now**: the self-hosted
pure-Simple binary (the real oracle/pipeline this issue is about) is not
deployed in this checkout — `bin/simple` is still the Rust bootstrap seed
(prints "this Rust-built Simple binary is a bootstrap seed only"), and
building/deploying it is out of scope here (no `cargo build`, disk near-full
across the shared box during this investigation). So **no patch can be
validated regardless of its size** — that alone is sufficient reason not to
patch.

Separately, and reinforcing the same verdict: even granting the oracle were
runnable, closing this gap for real means writing new MIR-lowering codegen
(loop + indirect closure invocation + result-array construction) for three
distinct methods — comparable in kind to the bespoke `push` special-case
added for bug #149, not a one-line resolver fix.

## Oracle check — IMPORTANT CAVEAT: source-verified only, never executed

`src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl`:
- `map` (line 614-626), `filter` (628-641), `flat_map` (643-659) are hand-coded
  as builtin array-method intrinsics, intercepted directly in
  `eval_array_method` *before* generic method/UFCS resolution ever runs. The
  code, as read, has correct-looking semantics (loop + call closure + collect).
- `fold`/`reduce`: **no match anywhere** in the interpreter source (grep for
  `"fold"`/`"reduce"` across `src/compiler/10.frontend/core/interpreter` is
  empty). Fold is not implemented in this oracle source at all — this part
  IS doubly confirmed (absent in source, and absent at runtime below).

**This is a source-reading claim, not an execution result.** The only binary
actually runnable and executed in this investigation is the Rust seed, and it
**disagrees** — it fails on map/filter too (see below), because the seed has
a wholly separate (Rust) interpreter/array-method table that also lacks
these, not because it exercises the self-hosted `.spl` interpreter above.
Per the #158 lesson (`id<i64>(42)` printed 336 despite looking correct in
source), source that reads correctly can still run wrong — **a latent
#158-style bug in the self-hosted interpreter's `map`/`filter` cannot be
ruled out**, since that code path was never actually executed here. `fold`'s
verdict does not depend on this caveat (it's absent either way); `map`/
`filter`'s "oracle is correct" claim should be read as unverified pending a
real run of the deployed self-hosted binary.

Empirically (Rust seed only — bootstrap-only, not the real pipeline this
issue is about — both `bin/simple run` and `--native`, same failure shape
either way since the seed's own array-method table also lacks these):
- `[1,2,3].map(\x: x*2)` → `Runtime error: Function 'Array.map' not found` in
  both interpreted and `--native` runs.
- `[1..5].fold(0, \acc,x: acc+x)` → `Runtime error: Function 'Array.fold' not found`
  in both modes.
- `[1..5].filter(\x: x>2)` → **silently "succeeds"** under `--native` but
  prints `<array@0x557de2666450>` instead of `[3,4,5]` — a wrong, non-crashing
  result, not a hard error (matches the #145 silent-placeholder risk pattern
  the task flagged).

The seed corroborates that **native codegen is broken** for all three; it
says nothing about whether the self-hosted interpreter's map/filter are
actually correct at runtime.

## Pinned resolution point (self-hosted native pipeline)

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`:
- Line 589 `case Unresolved:` — generic array methods fall through here when
  `MethodResolver` (try_instance_method/try_trait_method/try_ufcs in
  `resolve_strategies.spl`) can't resolve them, because the builtin `[T]`
  array type carries no symbol-bearing HIR type (per the bug #149 comment at
  lines 590-623 in the same file).
- Only `push` (line 624, `if method == "push" and args.len() == 1:`) got a
  hand-written special-case lowering (direct `rt_array_push` call) as the
  fix for #149.
- `map`/`filter`/`fold` have no equivalent arm, so they fall to line 672
  `self.error("unresolved method call: {method}", nil)`, print the
  `[mir-lower] WARNING: ... lowered to const-0 placeholder (silent-null risk,
  Task #145)` (line 681), and emit a `const 0` placeholder (lines 682-688).
- Confirmed by grep: no `"map"`/`"filter"`/`"fold"`/`"flat_map"` string
  anywhere in `src/compiler/20.hir` or `src/compiler/50.mir` — there is no
  intrinsic lowering path for these methods at all, unlike the interpreter.
- Also confirmed no stdlib `.spl` `fn map/filter/fold` exists on the plain
  `[T]` array type (only `PersistentList`/`PersistentVec`/`Map`/`Set`/
  `HashMap`/`HashSet` — real struct types with symbols — define their own).
  So there is no generic-resolution fallback to reuse either.

## Closures-as-values in native codegen: NOT the blocker

Verified a minimal `fn apply(f: fn(i64)->i64, x: i64) -> i64: f(x)` called
with a lambda: interpreted → `42` (correct); `--native` → `42` (correct,
matches oracle) **once the parameter has an explicit `fn(i64)->i64`
annotation**. Without the annotation, native segfaults (a separate, narrower
inference gap unrelated to #155 — HIR lowering requires an explicit closure
param type or it either errors in the interpreter or misbehaves natively).
So closure-passing to native functions works in principle; the actual gap is
specifically the missing intrinsic loop-lowering for `map`/`filter`/`fold`
themselves, which would need to synthesize a MIR loop invoking the closure
per-element and building the result — new codegen, not a routing fix.

## What's actually missing (to close this for real)

1. New MIR-lowering arms for `map`, `filter`, `fold` in
   `method_calls_literals.spl` (or a shared helper), each synthesizing:
   loop over `rt_core_array` elements, indirect `emit_call` through the
   already-working closure-invocation path, per-method result handling
   (`rt_array_push` for map/filter's kept elements, threaded accumulator for
   fold).
2. `fold` additionally needs interpreter support added first (no oracle
   currently exists) before it can even be characterized as a resolution
   target — right now there is nothing to match against.

No fix attempted; no `hof_155_fix.patch` produced, per task instructions.

Untried, for a future pass: `bin/release/x86_64-unknown-linux-gnu/simple.bak-*`
has several dated backups; one might be a previously-deployed self-hosted
build that could actually run the real interpreter oracle for map/filter.
Provenance of each `.bak` is unknown and a stale/broken one could mislead, so
this wasn't pursued here — but it's the cheapest path to turning the "source-
verified only" caveat above into a real execution result.

## Repro files (kept, not committed)
- `/tmp/claude-1000/.../scratchpad/hof_map.spl`, `hof_filter.spl`,
  `hof_fold.spl`, `hof_closure_arg.spl`, `hof_closure_arg2.spl`
