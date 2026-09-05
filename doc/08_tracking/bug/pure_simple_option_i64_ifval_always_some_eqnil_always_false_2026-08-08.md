# Pure-Simple AOT lane: `i64?` value-3 collision does NOT reproduce, but `if val`/`== nil` are broken worse

**Status:** REOPENED 2026-08-17 -- reproduces under SIMPLE_EXECUTION_MODE=jit (see REOPENED section at end). Previously: LIKELY FIXED, unconfirmed on the AOT lane — 2026-08-10 re-check. A fix
matching this doc's own "candidate (a)" is already present in
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` (the `nil_check_operand`
/ `rt_is_none`/`rt_is_some` block, ~line 2680-2718), landed by a separate session
via a "chore: sync" commit and explicitly commented as closing this bug ID. It
routes `opt == nil` / `opt != nil` (and the `if val` desugar, which reaches this
same code via `lower_cond_expr`'s fallthrough) through `rt_is_some`/`rt_is_none`
whenever the operand's STATIC HIR type is `Optional(_)` — type-driven, not
payload- or registration-driven, so it should apply uniformly to `i64?`, `bool?`,
`text?`. A quick interpreter/seed-JIT sanity run of the doc's own probe
(`bin/simple run`, current deployed seed) now shows correct `eq_nil`/`ifval`
behavior across `i64?` (0, 3, -1, real nil), `bool?` (true/false/nil), and
`text?` ("hi"/nil) — including the real-`nil` rows that were previously always
wrong. **However**, this doc's mandated verification bar is specifically the
pure-Simple **AOT `native-build`** lane, not the seed/interpreter, and that sweep
did not finish within this session's time budget (a full-compiler `native-build`
of the probe program was still compiling after 500s+ and was not waited out).
Leaving status as OPEN/unconfirmed rather than declaring FIXED without the
required AOT evidence — see "2026-08-10 partial verification" below for exactly
what was and wasn't checked. Follow-up: re-run
`env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build
--source <probe> --entry-closure --entry <probe> -o <out>` to completion and
sweep the full truth table from this doc's "Verification bar" section.
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

## 2026-08-10 partial verification (seed/interpreter only, AOT sweep incomplete)

Probe (`bin/simple run`, deployed seed `bin/release/x86_64-unknown-linux-gnu/simple`):

```
i64 v=0: eq_nil=false ne_nil=true ifval=SOME 0
i64 v=3: eq_nil=true ne_nil=false ifval=NONE          <- seed's own known value-3 collision, unrelated
i64 v=-1: eq_nil=false ne_nil=true ifval=SOME -1
i64 nil: eq_nil=true ne_nil=false ifval=NONE           <- correct, was broken pre-fix
bool v=true: eq_nil=false ne_nil=true ifval=SOME true
bool v=false: eq_nil=false ne_nil=true ifval=SOME false
bool nil: eq_nil=true ne_nil=false ifval=NONE
text v=hi: eq_nil=false ne_nil=true ifval=SOME hi
text nil: eq_nil=true ne_nil=false ifval=NONE
```

All non-value-3 rows are correct, including every real-`nil` row, which is the
symptom this bug is about. **This is the seed JIT, not the pure-Simple AOT lane
this doc's verification bar requires** — `bin/simple native-build` on the same
probe was started but did not finish compiling within this session's time
budget. Do not close this doc until that AOT sweep is run and matches.

## 2026-08-10 AOT native-build attempt — blocked by an unrelated SIGSEGV

The `native-build` for the full probe (`i64?`/`bool?`/`text?` truth table)
eventually completed (~500s+ full-compiler build, no incremental cache hit) and
produced a binary, but running it crashes immediately:

```
[simple-runtime] Fatal: SIGSEGV at address 0x1000000
Backtrace: probe_bin(+0x32c4) -> libc -> libc -> probe_bin(+0x3129) -> probe_bin(+0x2e88)
```

Three-frame backtrace, crash at a suspiciously round low address, before any of
the probe's own print output appears — this looks like an unrelated
runtime/entry-point defect (possibly in `native-build`'s `--entry-closure`
startup path for a standalone script outside the main compiler tree), not
something caused by the Option/nil fix under test. Confirming that
categorization, and getting a full AOT truth-table result, needs another
build-and-run cycle that this session's time budget does not allow (each
native-build of the full compiler for this single-file probe costs 500s+, with
no faster incremental path found).

**Net status unchanged: OPEN/unconfirmed on the AOT lane.** The seed/interpreter
evidence above still stands as partial confirmation that the fix's logic is
correct; the AOT lane specifically remains unverified, now for two compounding
reasons: (1) the required build is very slow, (2) the resulting binary hit an
apparently-unrelated crash before this session could observe the truth-table
output. Follow-up should first isolate whether the SIGSEGV is generic to any
`native-build --entry-closure` single-file probe (try the simplest possible
`fn main(): print("hi")` through the same path) before re-attempting this bug's
specific sweep.

## REOPENED 2026-08-17 — closed on an UNPINNED engine

The prior closure rested on an invocation that did not pin
`SIMPLE_EXECUTION_MODE`, so it is evidence about one arbitrary engine, not
about the defect. Re-probed in a minimal single-file probe, both arms pinned,
`rc` read on the line AFTER the command. Binary: bin/simple (stale Rust seed, bin/release/x86_64-unknown-linux-gnu/simple, 59536728 B, mtime 2026-08-16 22:59).

| probe | interpreter | jit | expected |
|---|---|---|---|
| `mk(3) == nil` where `fn mk(v: i64) -> i64?` | `false` rc=0 | **`true`** rc=0 | `false` |
| `mk(3) ?? -777` | `3` rc=0 | **`<value:0xfffffffffffffcf7>`** rc=0 | `3` |
| `none_val ?? -777`, `none_val: i64? = nil` | `-777` rc=0 | **`<value:0xfffffffffffffcf7>`** rc=0 | `-777` |
| `none_val == nil` | `true` rc=0 | `true` rc=0 | `true` |

So the payload-3 sentinel collision DOES still reproduce under the JIT, and `??`
additionally leaks a raw tag box into `to_string()` — the same
`<value:0x...>` shape as `native_to_i64_nil_coalesce_print_tagbox_leak_2026-07-20`.
`0xfffffffffffffcf7` is `-777` as a payload, so the correct value is inside the
box and only the unboxing is missing. The "LIKELY FIXED" status is not supported
on the JIT arm. The pure-Simple AOT `native-build` bar this doc sets for itself
remains separately unmet.

Engine-identity control (`val p60 = 1152921504606846976` INSIDE `fn main()`):
interpreter `1152921504606846976`, jit `-1152921504606846976` — so the jit arm
demonstrably JIT-compiled and was not demoted. Note the same control at TOP
LEVEL does NOT diverge; a top-level body runs interpreted regardless of the pin.

Any "re-verified by source inspection" stamp above is void per repo policy.
Full method, population counts and probe paths:
`<scratchpad>/rv/UNPINNED_ENGINE_REVERIFICATION_2026-08-17.md`.
