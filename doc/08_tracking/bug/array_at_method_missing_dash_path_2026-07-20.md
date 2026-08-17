# `array.at(i)` method does not exist — breaks production `dash_path` code, not just its spec

**Date:** 2026-07-20
**Severity:** high (production source code, not a test-only issue)
Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Found by:** whole-suite `test/unit/` triage campaign, `lib/skia` cluster

## Update 2026-08-01 — root cause, scope, and a worse sibling defect

**Seed-only.** The pure-Simple interpreter ALREADY implements `.at()` correctly
(`_EvalOps/call_method_eval.spl:833` in `eval_array_method`, flat encoding,
supported explicitly at `eval.spl:911-921`). The failing message is the Rust
seed's wording, so the gap is in the bootstrap engine only. Root cause: the
array-method dispatch in
`src/compiler_rust/compiler/src/interpreter_method/collections.rs` has
`get`/`has`/`contains`/... but no `"at"` arm, so it falls through to the
not-found error. Text `.at` is handled separately at
`interpreter_method/string.rs:368`.

> **Dead-code audit 2026-08-01 — the "seed-only" verdict SURVIVES, but the
> citation that supported it was half dead code.** This paragraph originally
> also cited `interpreter/eval_methods.spl:296`. That file was a DEAD
> duplicate: all four of its functions (`eval_method_call`,
> `eval_method_with_args`, `eval_array_method`, `eval_text_method`) were
> shadowed by package-local `_EvalOps` copies, proven by sabotage in both
> directions, and it was deleted in `f97dfbbb8ee`. **Re-derived against the
> live file:** `_EvalOps/call_method_eval.spl` `eval_array_method` really does
> carry the `at` arm (bounds-checked `0 <= i < len`, element-as-`Some`,
> `val_make_nil()` as `None`) — and it is a strict superset of the dead copy
> (it additionally has `map`/`filter`/`flat_map`/`any`). So "the pure-Simple
> interpreter already implements `.at()` correctly" **still holds**, the
> seed-only framing is intact, and the held patch is still the right patch.
> Caveat: this covers **array** `.at()` only. The live *text* method table
> (`_EvalOps/access_literal_assign_eval.spl`) has **no `at` arm at all**, in
> neither the dead nor the live copy — `text.at(i)` in the pure-Simple
> interpreter falls through to `eval_set_error`. The seed handles that case at
> `interpreter_method/string.rs:368`, so on text `.at` the two engines diverge
> in the *opposite* direction from the array case. See
> `doc/08_tracking/bug/2026-08-01_interpreter_eval_text_method_duplicate_live_subset.md`.

**There are TWO defects, and the second is worse than the reported one.** Under
the JIT, `[99,111,108].at(1)` does not error — it SILENTLY MATCHES `None`,
with `SIMPLE_JIT_STRICT=1` set. A caller gets a plausible empty result instead
of a diagnostic. The 4-line dispatch arm fixes the interpreter path only; the
JIT silent-`None` is NOT covered and remains open.

**The encoding is forced, not a design choice.** Measured in the seed
interpreter: an enum `Option` matches (`Some(42)` -> `ENUM-SOME 42`), while the
flat encoding does not — `match bytes.get(1): Some(v)/None:` leaves the
sentinel untouched and falls through EVERY arm. So the arm must build
`Value::some`/`Value::none` (`value_impl.rs:729/738`).

**Call-site survey re-measured** (vendor excluded, `Type.at(` static
constructors separated out): **218 sites expect `Option`, 0 expect a bare `T`**,
plus 137 static constructors and 36 unclear (comments, JS strings, `Ray.at`).
An earlier "~253 Option / ~8 bare" figure quoted during triage was wrong.
Design risk is therefore zero: `.at()` on an array today either errors or
always returns `None`, so no working caller depends on current behaviour.

**Not landed.** With/without numbers need a Rust seed rebuild, and the box has
been saturated (load 77-85 on 32 cores, another session holding the shared
110G target dir). Patch held at `scratchpad/at_option_seed.patch` pending a
build. Per pure-Simple-first this is bootstrap-only value — the shipping
interpreter is already correct.

## Symptom

`test/unit/lib/skia/stroke_dash_spec.spl` fails 4 of 5 examples on the
deployed binary (`bin/release/x86_64-unknown-linux-gnu/simple`, `bin/simple
test test/unit/lib/skia/stroke_dash_spec.spl --no-session-daemon`):

```
semantic: method `at` not found on type `array` (receiver value: [10, 10])
```

The spec itself (`test/unit/lib/skia/stroke_dash_spec.spl`) does not call
`.at(` anywhere — the error originates from the PRODUCTION source it
exercises, `src/lib/skia/feature/stroke/dash.spl`, which uses `.at(i)` as an
`Option`-returning safe-indexed-get on arrays extensively:

```simple
# src/lib/skia/feature/stroke/dash.spl (representative call sites)
val opt = pattern.intervals.at(i)      # line 52
val opt = pattern.intervals.at(i)      # line 62
val opt = input.segments.at(i)         # line 107
val p_opt = seg.pts.at(0)              # lines 112, 123, 134, 162, 189, ...
```

No `.at()` method is defined anywhere in the stdlib for the array/`[T]`
built-in type (searched `src/lib/common/*.spl`,
`src/compiler/10.frontend/core/interpreter/*.spl` — no `fn at(` on array,
and no interpreter dispatch table entry for `"at"` on arrays).

## Root-cause hypothesis

`dash.spl` was written against an array API that includes a safe
`.at(i) -> Option<T>` accessor (mirroring `Dict.get`/Rust's `Vec::get`), but
this method either was never implemented for arrays or was removed. Since
this is called from **production code**, not test code, this is a genuine
implementation gap: any caller of `dash_path()`/`DashPattern` construction
functions hits this at runtime, under both `bin/simple test` and (very
likely) `bin/simple run`/native builds, since it's a missing builtin method
rather than a test-vs-run evaluator divergence.

Not attempted as a triage-scope fix: adding a new stdlib array method (or
rewriting `dash.spl`'s ~10 call sites to bracket-index + explicit
bounds-check) is source/feature work, not a test-spec fix, and risks scope
creep beyond this campaign's mandate.

## Affected

- `test/unit/lib/skia/stroke_dash_spec.spl` — 4 of 5 examples:
  `"dash_path: uniform dash on a long horizontal line produces N
  sub-segments"`, `"...zero-length phase preserves dash alignment"`,
  `"...pattern [10, 0] (all-on) produces the original line length worth of
  draws"`, `"...pattern [0, 10] (all-off) produces empty path"`.
- Production: `src/lib/skia/feature/stroke/dash.spl` (`dash_path`,
  `dash_pattern_new`, and every helper touching `pattern.intervals`,
  `input.segments`, or `seg.pts` via `.at()`).
- `test/01_unit/lib/blink/css_tokenizer_spec.spl` — 7 of 8 examples fail with
  the identical `method \`at\` not found on type \`array\`` error. Root cause
  confirmed identical: the spec doesn't call `.at(` itself; production source
  `src/lib/blink/css_parser/tokenizer.spl:92` does
  `val opt = bytes.at(pos)` (also an `Option`-returning safe-indexed-get
  pattern, same shape as the `dash.spl` call sites above). Also reproduced
  under `bin/simple run` on a 3-line standalone repro
  (`val bytes: [i64] = [99, 111, 108]; bytes.at(1)`), confirming this is a
  missing builtin, not a test-vs-run evaluator divergence.
