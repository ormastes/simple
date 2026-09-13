# BUG: a `bool`-declared parameter accepts a non-bool silently — and the JIT corrupts it

## Re-measured 2026-09-13 — still OPEN. Both halves live; the corruption now renders as `error`, and the lanes disagree three ways

Binary: Rust seed `build/vt4/bootstrap/simple.exe` (sha256 `dc138d50276d…`),
Windows.

### Half 1 — the missing check: UNCHANGED, still unenforced on BOTH lanes

`fn takes_bool(b: bool)` accepts an `i64`, a `text`, a bare `nil` and an
`i64?` without any diagnostic on either lane. Nothing rejects. `coerce_param`
still has no bool arm, as the sibling entry pins.

### Half 2 — what the parameter actually holds, `print "{b}"` inside the callee

| argument | JIT (default) | interpret |
|---|---|---|
| `true` | `true` | `true` |
| `1` | `true` | `true` |
| `0` | `false` | **`true`** |
| `nil` | **`error`** | `false` |
| `opt_nil()` (`i64?` = nil) | **`error`** | `false` |
| `"x"` | `true` | `true` |

and the branch each one selects in `if b:`:

| argument | JIT | interpret |
|---|---|---|
| `0` | ELSE | **THEN** |
| `nil` | **THEN** | ELSE |
| `opt_nil()` | **THEN** | ELSE |

Three things this pins down that the original report could not:

1. **The JIT re-tagging half is still live.** The reported garbage tag
   `<special:N>` is gone as a *rendering*, but the value is still corrupt: a
   `bool` parameter handed `nil` stringifies as the literal text `error` and is
   simultaneously **truthy**. That is strictly worse than a visible
   `<special:N>` — it looks like a legitimate error string.
2. **The two lanes now disagree in both directions**, so neither can serve as
   the oracle for the other. `0` is falsy on the JIT and truthy in the
   interpreter; `nil` is truthy on the JIT and falsy in the interpreter. A spec
   asserting either behaviour is green on one runner and red on the other,
   which is the cross-runner hazard this cluster was filed about.
3. **The JIT `nil`-is-truthy row is the same defect** as the reopened
   `not_over_nil_returns_false_in_run_engine_2026-08-04.md` (literal `not nil`
   is `false` on the JIT, `true` in the interpreter). Fixing nil truthiness on
   the JIT should move both.

Note the interpreter's `0` -> `true` row is not in the original report and may
be new: passing integer `0` to a `bool` parameter yields a truthy `true` there.

Entry stays OPEN. Not fixed here — `src/compiler_rust/**` was off-limits during
this pass (concurrent bootstrap).

**The "fix once, close all of these" list is now three, not four.**
`exists_operator_returns_payload_not_bool_2026-08-04.md` was closed 2026-09-13
as an **invalid premise**: `.?` evaluating to `T?` rather than `bool` is the
ratified contract
(`doc/07_guide/quick_reference/syntax_quick_reference.md:539-550`, `num.?  #
i64?: Some(num)`), the same call already made on its sibling
`exists_check_on_optional_i64_returns_payload_2026-08-01.md` on 2026-08-08.
Its 158 red examples were remediated spec-side (sampled 8 of the 36
`branch_coverage_*` files: 630 examples, 1 failure). So that report was never
evidence for a compiler defect, and the real defect behind this cluster is the
missing bool coercion measured above — `coerce_param` having no bool arm —
together with the JIT's nil-truthiness.


**Status:** OPEN
**Found:** 2026-08-04
**Related — SAME root cause, found independently by parallel lanes the same day.
Fix once, close all of these. This file is the UNIT-tier record; its unique
content is the JIT re-tagging half (`<special:N>`) and the two specs a prior
session papered over:**
- `optional_passed_to_bool_param_is_neither_coerced_nor_rejected_2026-08-04.md`
  — system-tier census, and it pins the missing check to seed
  `arg_binding.rs:84 coerce_param` (no bool arm). **Read that one first.**
- `exists_operator_returns_payload_not_bool_2026-08-04.md`
- `exists_check_contract_reddens_46_app_branch_coverage_specs_2026-08-04.md` (app tier)
- `jit_if_nil_takes_true_branch_2026-08-04.md` (the engine-divergence half)
**Severity:** high — every `bool` type annotation on a parameter is unenforced.
The interpreter passes the wrong-typed value straight through; the JIT
re-tags it into a garbage `<special:N>` value. 28 specs in
`test/01_unit/std/` are red because of it, and a previous session papered
over two of them by editing the spec instead of the compiler.
**Files:**
- `src/compiler/10.frontend/parser_types_expr.spl:298` (declares `.?` semantics)
- `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` (ExistsCheck lowering)
- affected specs: `test/01_unit/std/auto_comprehensive_{1,2,4..12,14..23,25..30}_spec.spl`
  and their legacy duplicates under `test/unit/std/`

## Symptom

Minimal repro (`/tmp/probe_bool.spl`):

```
fn take_bool(b: bool) -> text:
    "got={b}"

fn main():
    val opt = Some(42)
    print "A:{opt.?}"
    if opt.?:
        print "B:truthy-branch-taken"
    else:
        print "B:falsy-branch-taken"
    print "C:{take_bool(opt.?)}"
    print "D:{take_bool(42)}"
```

| line | expected | `SIMPLE_EXECUTION_MODE=interpreter` | `SIMPLE_EXECUTION_MODE=jit` |
|------|----------|-------------------------------------|-----------------------------|
| A `opt.?` | `Some(42)` per the doc, see below | `42` | `42` |
| B `if opt.?:` | truthy | truthy ✅ | truthy ✅ |
| C `take_bool(opt.?)` | `true`, or a compile error | **`got=42`** | **`got=<special:82>`** |
| D `take_bool(42)` | a compile error | **`got=42`** | **`got=<special:44>`** |

Row **D** is the core of it: an integer *literal* passed to a `bool` parameter
is accepted with no diagnostic. `.?` is not required to trigger this.

As it reaches the suite:

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/01_unit/std/auto_comprehensive_10_spec.spl
  ✗ option coverage 1
    expected 42 to equal true
Results: 30 total, 29 passed, 1 failed
```

from `auto_comprehensive_10_spec.spl:93-96`, whose whole body is

```
val opt = Some(42)
check(opt.?)            # check(condition: bool) -> expect(condition).to_equal(true)
```

## Root cause

Two layers, both proved.

**1. No check and no coercion at a typed parameter boundary.** Row D above is
the proof: `take_bool(42)` type-checks. Neither the pure-Simple type checker
nor MIR lowering compares the argument's type against the declared `bool`, so
the raw `i64` is bound to `b` unchanged. This has nothing to do with `.?` —
`.?` is merely the most common way to produce a non-bool in a boolean-looking
position.

**2. The JIT then re-tags that value through the bool lane and corrupts it.**
`take_bool(42)` prints `<special:44>` and `take_bool(opt.?)` prints
`<special:82>` — the payload plus the bool tag, decoded as a "special" value.
So this is not merely a permissive pass-through: on the engine ordinary
programs actually run on, the value is *destroyed*. Interpreter and JIT
disagree (`got=42` vs `got=<special:44>`), which also means a spec suite (which
runs on the interpreter) can never observe the JIT corruption.

**Contributing: the documented semantics of `.?` contradict themselves.**

- `doc/07_guide/quick_reference/syntax_quick_reference.md:505,523` —
  "Existence Check (`.?`) — Returns `T?`", and `opt.?` is "pass-through
  (already optional)".
- `doc/07_guide/language/short_form.md:145` — "`list.?` # **true** if list is
  non-empty".
- `src/compiler/10.frontend/parser_types_expr.spl:298` —
  `ExistsCheck(Expr)  # .? — value if present, nil if absent`, i.e. it sides
  with the first doc.
- `.claude/memory/reference_seed_exists_check_lowers_to_bool.md` — the Rust
  **seed** lowers `.?` to a bool, i.e. it sides with the second doc.

Observed behaviour matches neither doc exactly: row A shows `opt.?` yields the
raw payload `42`, not `Some(42)`, so the "pass-through (already optional)"
claim in the quick reference is also wrong.

## Why not fixed now

Every available fix is a language-semantics decision with repo-wide blast
radius, and picking one unilaterally inside a test-repair lane would be worse
than leaving it visible:

- **Making `.?` return `bool`** is definitively wrong — it would break the
  `if val name = input.?:` binding idiom documented at
  `syntax_quick_reference.md:531`, which needs the value.
- **Coercing truthiness at `bool`-typed boundaries** would turn these 28 specs
  green, but it silently legalises `take_bool(42)` across the whole codebase.
- **Rejecting the mismatch at compile time** is the type-correct answer, but it
  turns these specs from "1 failing example" into "does not compile", and until
  someone measures how many existing `bool` parameters are being fed non-bools
  it is not landable.

The JIT `<special:N>` corruption (layer 2) is independently a defect and should
be fixed regardless of which way layer 1 is decided.

## Re-investigated 2026-08-10 — confirmed genuinely architectural, not declined-by-default

Re-checked whether a minimal `.spl`-side validation fix exists (a type-check
at the call boundary that rejects non-bool args to `bool` params) instead of
accepting this doc's own "needs semantics decision" framing at face value.
Searched `src/compiler/35.semantics/` and `src/compiler/20.hir/` for an
existing call-argument type-checking pass to hook a `bool`-specific rejection
into (`check_call_args`, `typecheck_call`, `validate_call_args`,
`infer_call`) — none exists as a general mechanism; the only argument-type
lint hits are `lint/duplicate_typed_args.spl` and `lint/primitive_api.spl`,
neither of which checks argument-vs-parameter type compatibility at all.
There is no boundary to attach a minimal, scoped `bool`-only check to without
first building general call-site argument type-checking — that is exactly
the "unmeasured repo-wide blast radius" the original analysis already
identified, confirmed at the code level rather than asserted.

The JIT half (`<special:N>` corruption) lives in the seed's native codegen
per `optional_passed_to_bool_param_is_neither_coerced_nor_rejected_2026-08-04.md`'s
own pin to `arg_binding.rs:84 coerce_param` — that file is
`src/compiler_rust/**`, out of scope for `.spl`-side work and explicitly off
limits for this pass.

**Conclusion stands as originally characterized: this is architectural, not
merely declined.** The two axes are independent and both need dedicated,
larger-scoped work:
1. A general call-argument type-checking pass in the pure-Simple semantics
   layer (does not exist yet at all — this is new infrastructure, not a
   one-line guard) — needed before a `bool`-specific rejection can be scoped
   safely.
2. A Rust-seed JIT fix to `coerce_param` so a wrong-typed value at minimum
   doesn't get corrupted into a garbage `<special:N>` tag, independent of
   whether layer 1 ever lands — this is `src/compiler_rust`, off limits here.

No code change made in this pass; re-affirming the prior "needs semantics
decision" status with the above as the concrete evidence trail (searched
locations, why no minimal hook point exists, exact off-limits boundary).

**Do not "fix" this by editing the specs.** That already happened:
`auto_comprehensive_13_spec.spl:95` and `auto_comprehensive_24_spec.spl:95`
have had `check(opt.?)` rewritten to `check(opt != nil)`, which is why those
two files are green while the other 28 identical files are red. That workaround
hid the defect rather than removing it, and it should be reverted once the real
fix lands.
