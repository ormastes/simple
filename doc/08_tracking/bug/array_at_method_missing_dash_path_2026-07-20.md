# `array.at(i)` method does not exist — breaks production `dash_path` code, not just its spec
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-07-20
**Severity:** high (production source code, not a test-only issue)
**Status:** open — root-caused and patched 2026-08-01, fix NOT YET COMPILED
**Found by:** whole-suite `test/unit/` triage campaign, `lib/skia` cluster

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


## Evidence — 2026-11-05 (work/libbug-std-arrayat-20261105)

Re-verified against seed binary `build/phase_snapshots/phase1_1793422538/simple`
(Oct 31 build), cwd = this branch's worktree:

**The `array.at(i)` method itself is FIXED on every lane compiled into this
binary.** `handle_array_methods`
(`src/compiler_rust/compiler/src/interpreter_method/collections.rs:377`) has
the `at` arm (landed with interpreter fix `f18c5963132`, JIT fix `ceee960ca8e`,
native fix per `array_at_native_llvm_lane_2026-08-01.md`, and the pure-Simple
MIR arm at `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:5333`).
Empirical results 2026-11-05:

- `test/01_unit/lib/common/array_at_option_spec.spl` — 11/11 PASS
- `test/01_unit/lib/blink/css_tokenizer_spec.spl` — 8/8 PASS (was 7/8 failing)
- JIT probe (`simple run`, default engine): in-range/OOB/negative/empty all
  correct Option results.
- `test/01_unit/lib/skia/stroke_dash_spec.spl` — 4/5 PASS (was 4/5 failing);
  no `method 'at' not found` errors remain anywhere.

**Residual failure root cause (this change).** The one remaining red example,
`"dash_path: pattern [0, 10] (all-off) produces empty path"`, failed with
`expected false to equal true` — a DIFFERENT defect from the missing method:
`dash_path` (`src/lib/skia/feature/stroke/dash.spl`) emitted a degenerate
zero-length `move_to`/`line_to` pair whenever the dash pointer sat inside a
zero-length "on" interval (pattern `[0, 10]` alternates a 0-length on-interval
with the off-interval), so the output path was never empty. Fixed by skipping
the emission when the sub-segment has zero length (an on-interval of length 0
draws nothing, matching SkDashPathEffect). After the fix:
`test/01_unit/lib/skia/stroke_dash_spec.spl` — 5/5 PASS.

Regression checks (same binary, same run): `stroke_expand_spec` 5/5,
`array_coverage_spec` 228/228, `array_list_ops_spec` 19/19 — all PASS.
`array_set_method_spec` remains 2/7 on this binary for an unrelated reason:
the binary (Oct 31) predates the Nov 4 `set` fix `adcb88151ce` (Rust-source
only, not compiled into any available binary); its failures are all
`method 'set' not found`, unchanged by this change.
