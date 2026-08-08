# Pure-Simple AOT lane: `i64?` value-3 collision does NOT reproduce, but `if val`/`== nil` are broken worse

**Status:** OPEN (new defects; scoping task for `jit_option_i64_value3_reads_as_none_2026-07-24.md`)
**Engines:** Pure-Simple `native-build` (AOT). Seed JIT (`bin/simple run`) reproduces the
already-documented value-3 collision exactly as recorded.
**Scope of this doc:** answers "does the pure-Simple lane carry the seed's `Option<i64>`
payload-3 == nil sentinel collision" (asked from `jit_option_i64_value3_reads_as_none_2026-07-24.md`
/ `interp_index_of_digit_leading_literal_2026-07-22.md`). Answer: **no** — but it has two
different, more severe defects in the same area, found while checking.

## Pure-Simple counterpart location

`case NilLit` in `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` (not modified this
session — another session has uncommitted WIP there per task instructions). Its own comment
(lines ~2385-2415) documents materializing `nil` as `emit_const_int(3)` for exactly the same
reason as the seed (`native_i64opt_some0_collapses_to_nil`): "3 cannot collide with any real
bool payload and only collides with the specific literal int payload 3 (an acceptable, narrow
trade...)". So structurally the pure-Simple lane ALSO uses the untagged sentinel 3 — the
in-code comment predicts the same collision the seed has. Empirically, however, it does not
manifest the same way for `??` / `is_none()` (see truth table): those consumers evidently
decode/compare correctly for payload 3. What IS broken is `if val` and `== nil`, uniformly,
independent of the payload value.

## Truth table — pure-Simple AOT (`native-build`, marker-clean run, no ambiguity)

Probe: `/tmp/.../scratchpad/optprobe/main.spl`, build via
`env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build --source ... --entry-closure --entry main.spl ...`,
run the produced binary. `make_opt(v: i64) -> i64?: return v`.

| v | `v == nil` | expected | `v ?? -777` | expected | `if val x = v` | expected | `.is_none()`/`.is_some()` |
|---|---|---|---|---|---|---|---|
| 0 | false | false | 0 | 0 | **SOME** (display garbage, known unrelated defect) | SOME | is_none=false, is_some=true (correct) |
| 1 | false | false | 1 | 1 | SOME | SOME | — |
| 2 | false | false | 2 | 2 | SOME | SOME | — |
| **3** | false | false | **3** | **3 (correct — NOT collided)** | SOME | SOME | is_none=false, is_some=true (correct) |
| 4 | false | false | 4 | 4 | SOME | SOME | — |
| -1 | false | false | -1 | -1 | SOME | SOME | — |
| real `nil` | **false — WRONG** | **true** | -777 (correct, coincidentally right default) | -777 | **SOME "Option::None"** — WRONG | NONE | is_none=**true**, is_some=**false** (correct) |

Key result: **`v ?? default` and `.is_none()`/`.is_some()` are correct across the whole swept
range including 3 and real `nil`.** The seed's specific "payload 3 reads back as None" collision
does **not** reproduce on the pure-Simple AOT lane for either of those two consumer forms.

## Two different (new) defects found instead

1. **`i64? == nil` is always `false`**, even when the operand is a genuine `nil` — confirmed
   both for `Some(3)` (correctly false) and for a real `none_val: i64? = nil` (incorrectly
   false; expected true). This is worse than the seed's narrow value-3 collision: it is wrong
   for the entire domain of real `None`, not one payload value.
2. **`if val x = v` always takes the `Some` branch**, even when `v` is a genuine `nil` —
   `check_ifval(999, none_val)` printed `IFVAL=SOME Option::None` (entered the Some arm; `x`
   then printed as the garbage-formatted text `Option::None`, a symptom of the known/unrelated
   tag-misread print defect, but the *branch selection itself* is wrong, not just the display).
   This is also strictly worse than the seed's behavior (seed's `if val` correctly takes the
   `None` arm for genuine `nil`, and just mis-collides for payload 3).

## Cross-check: seed JIT (`bin/simple run`, same probe file, `if val` portion only)

```
WARNING: this Rust-built Simple binary is a bootstrap seed only...
TAG=0   IFVAL=SOME 0
TAG=1   IFVAL=SOME 1
TAG=2   IFVAL=SOME 2
TAG=3   IFVAL=NONE          <- the documented value-3 collision, reproduces exactly
TAG=4   IFVAL=SOME 4
TAG=-1  IFVAL=SOME -1
TAG=999 IFVAL=NONE          <- real nil, correct
```
(`.is_none()` is not implemented on the seed JIT path — `Runtime error: Function 'is_none' not
found` — so that column could not be cross-checked there; unrelated to this defect family.)

This is exactly the seed's already-documented behavior (see
`interp_index_of_digit_leading_literal_2026-07-22.md`). The two engines diverge in an
interesting way: seed's `if val` is correct for real `nil` and wrong only for payload 3;
pure-Simple's `if val` is wrong for real `nil` (and, vacuously, "correct" for payload 3 only
because it always says Some).

## Why no fix shipped in this pass

- The value-3-collision the task was scoped to fix does **not** reproduce in the pure-Simple
  `??`/`.is_none()` consumers that most production code paths use — there is nothing to patch
  there.
- The two defects that DO reproduce (`== nil` always false, `if val` always Some) are a
  different, larger-scope control-flow lowering bug, not a narrow sentinel-value fix, and their
  likely fix site (`case NilLit` / the if-let/if-val lowering neighborhood in
  `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`) is the exact file this session was
  told to avoid touching (another session has ~68 uncommitted lines there). Editing it blind,
  under a 900s-per-build budget, without being able to preserve the other session's WIP by
  inspection first, was judged higher-risk than valuable within this pass's budget.
- No source was edited this session; nothing to sabotage-verify or restore. `git diff` for
  `src/compiler/**` shows only the pre-existing, this-session-unrelated dirty tree already
  present at session start (confirmed via `git status --porcelain -- src/compiler`).

## Follow-up (not done here)

- Root-cause `== nil` and `if val` against `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`'s
  nil/option lowering once the other session's WIP there is committed or resolved.
- Re-sweep this exact probe (`/tmp/.../optprobe/main.spl`, preserved in this doc) once that
  lands, to confirm both defects close and the value-3 non-collision still holds.

---

## ROOT CAUSE (source-traced 2026-08-08) — both symptoms are ONE defect

**Ignore the `case NilLit` / value-3-sentinel theory above.** It is a red herring:
`??` and `.is_none()` are empirically correct for every payload including 3, so
the untagged constant is not the fault.

The chain, read straight from source:

1. **`if val v = option.?` is parser-desugared to a raw binding followed by
   `v != nil`** — stated explicitly at `mir_lowering_stmts.spl:1819-1820`. It is
   a Binary comparison node, NOT an `ExistsCheck` node.

2. **`lower_cond_expr` (`mir_lowering_stmts.spl:1773`) only special-cases
   `HirExprKind.ExistsCheck`**, for which it emits a real `rt_is_some` call.
   Everything else falls through to `case _: self.lower_expr(cond)`.

3. So the desugared `v != nil` never reaches `rt_is_some`. It is lowered as an
   ordinary Binary comparison and the branch tests the raw Option handle.

4. That Binary comparison is the SAME representation-blind path fixed for
   `Option<bool>` in `ab3af6f728e`: `bin_is_enum_eq` requires both operands to
   resolve to the same enum id, but `lower_enum_construct_named` deliberately
   skips `remember_local_hir_type` for `"Option"`, so `local_enum_type_id`
   returns -1 for BOTH operands and it falls through to a raw scalar compare of a
   boxed `rt_enum_new` handle against the raw sentinel word.

**This explains both symptoms with one mechanism:**
- `v == nil` is always FALSE — the boxed handle never equals the raw sentinel.
- `if val` always takes Some — it *is* `v != nil`, and a comparison that is
  always false makes its negation always true.

**`lower_cond_expr`'s own docstring describes this exact hazard** and guards only
the `.?` spelling:

> "the nil sentinel is the NON-ZERO integer 3 (RT_NIL = (SPECIAL_NIL << 3) |
> TAG_SPECIAL, runtime_value.h), so branching on that value directly is
> unconditionally TRUE -- a silent wrong-branch bug, strictly worse than a loud
> crash."

That is precisely what happens to `if val`. The analysis was right; the guard was
just never extended past the one syntactic form.

## Why `bool?` already works and `i64?` does not

`ab3af6f728e` made the Binary arm consult `option_value_locals` and box a raw
literal via `ensure_option_handle` when exactly one side is a registered Option
handle and the other is bool-typed or nil-marked. Measured after that fix:
`nil == nil` is TRUE for `bool?`. The i64? case evidently does not satisfy the
same operand-registration test.

**Fix direction (two candidates, prefer whichever is smaller and provable):**
- (a) Extend the `ab3af6f728e` Binary-arm handling so an i64?-typed (and
  generally any-payload) Option operand compared against `nil` boxes/compares by
  representation, not raw bits.
- (b) Teach `lower_cond_expr` to recognise the desugared `v != nil` shape over an
  Option-typed local and emit `rt_is_some` — the same treatment `.?` already
  gets. This fixes `if val` at the branch, but NOT a bare `v == nil` in value
  position, so (a) is likely still needed.

Do NOT "fix" this by making `ensure_option_handle` guess a discriminant at
runtime. Its comment ("Nil and the valid raw i64 payload 3 share the same bits.
Only the lowering provenance can distinguish them; never guess at runtime") is
correct for its own boxing job and must stay.

## Verification bar for whoever implements this

Sweep the full table — `Some(0..4)`, `Some(-1)`, real `nil` — across `if val`,
`== nil`, `!= nil`, `??`, `.is_none()`, `.is_some()`, for payload types `i64?`,
`bool?`, and `text?`. Rows whose correct answer is already "no-match"/"None" pass
by coincidence and prove nothing; the match-expected rows are the ones that
matter. `??`/`.is_none()`/`.is_some()` are correct TODAY and must not regress.
