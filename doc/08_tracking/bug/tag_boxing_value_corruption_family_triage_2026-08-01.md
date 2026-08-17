# Tag-boxing value-corruption family — three-lane triage

- **Filed:** 2026-08-01
- **Status:** re-verified 2026-08-17 — **all four original repros are now GREEN
  on both interpreter and JIT.** #2 is fixed for the shape reported here, but a
  *residual* of the same class is live and split out to
  `coalesce_optional_accessor_sentinel_value_eaten_jit_2026-08-17.md`.
  (Historical status line: 1 of 4 FIXED and landed; 1 does not reproduce; 2 OPEN.)
- **Verdict on the family:** **NOT one root cause. Four separate sites.** PROVED.

Four defects were filed separately and looked like one shared cause — a tagged
value crossing a boundary without being decoded, with the `value << 3` box
convention and `3` doubling as the nil sentinel. This document records the
three-lane measurement that took each one apart.

Every row below was measured on `src/compiler_rust/target/bootstrap/simple`
built from the commit noted, with:

| lane | how it was reached |
|------|--------------------|
| interpreter | `SIMPLE_EXECUTION_MODE=interpret <bin> file.spl` |
| JIT | `<bin> file.spl` (the default engine) |
| native | `<bin> compile --native file.spl -o out && ./out` |

`SIMPLE_NO_JIT=1` does nothing; a typo'd `SIMPLE_EXECUTION_MODE` value silently
runs the JIT, so confirm the lane with a known-divergent oracle before trusting
a reading.

## Summary

| # | symptom | interp | JIT | native | verdict |
|---|---------|--------|-----|--------|---------|
| 1 | `list.get(i)` returns `value << 3` | correct | correct | correct | DOES NOT REPRODUCE — fixed upstream since 2026-07-28 |
| 2 | `??` on a raw i64 whose value is 3 | correct | correct (2026-08-17) | unsupported | **FIXED as reported**; residual on optional accessors split out |
| 3 | `.find()` result breaks `text[:idx]` | error | **WRONG** | error | **FIXED** — was never tag-boxing |
| 4 | `to_text` on an erased `Any` bool | correct | correct | not re-run | **FIXED (interpreter+JIT) — verified 2026-08-07**, see update below |

The four do not share a cause. #3 was a lexer/parser collision in a different
subsystem entirely. #1 no longer reproduces on any lane. #2 and #4 are both
JIT-only but sit at different sites and have different mechanisms. Fixing any
one of them would not have moved the others.

## 1 — `list.get(i)` returns `value << 3` — DOES NOT REPRODUCE

```simple
fn main():
    var a = [5, 7]
    print "A {a[0]} {a.get(0)}"
    a[1] = 9
    print "B {a[1]} {a.get(1)}"
    var b = []
    b.push(42)
    print "C {b[0]} {b.get(0)}"
```

| lane | result |
|------|--------|
| interpreter | `A 5 5` / `B 9 9` / `C 42 42` |
| JIT | `A 5 5` / `B 9 9` / `C 42 42` |
| native | `A 5 5` / `B 9 9` / `C 42 42` |

All three lanes agree and all three are correct, including the exact receiver
shapes the original report called uniformly broken (literal list, stored-into,
pushed-into). The `xs[i]`-instead-of-`xs.get(i)` workaround is no longer load
bearing for correctness.

**Do not treat this as licence to re-add `mut` under `src/os/crypto/**`.** The
original report's BIP-39 note turned on W1006 demoting that module to the
interpreter; that demotion is still what makes the module's arithmetic run on
the correct lane for the OTHER open defects here.

## 2 — `??` on a raw i64 whose value is 3 — FIXED as reported; residual split out

**Update 2026-08-17 — re-measured on the deployed `bin/simple`
(`bin/release/x86_64-unknown-linux-gnu/simple`, Rust seed, mtime 2026-08-16),
both lanes via `SIMPLE_EXECUTION_MODE`:**

| case | interpreter | JIT |
|------|-------------|-----|
| `val n = 3` -> `n ?? 777` | 3 | **3** (was 777) |
| `s.index_of("(") ?? 999999` | 3 | **3** (was 999999) |
| every value 0..8, plus `0-3` and `1+2` | correct | correct |

Classified by CONTENT, not ancestry: `lower_coalesce`
(`src/compiler_rust/compiler/src/hir/lower/expr/control.rs:1774`) now lowers
`??` to the identity when the left operand's `TypeId` is a statically
non-nullable scalar, with a long comment naming this exact defect. That is the
fix, and it is present in current source.

**Residual, still LIVE — new doc.** The same fix deliberately EXEMPTS the
optional accessors (`first/last/get/min/max/pop/remove/at`, control.rs:1815-1822),
which keep the runtime nil check. So `[3, 9].first() ?? -1` returns **-1** under
the JIT and **3** under the interpreter. Filed as
`doc/08_tracking/bug/coalesce_optional_accessor_sentinel_value_eaten_jit_2026-08-17.md`,
gated (RED by design) by
`test/01_unit/compiler/codegen/coalesce_sentinel_collision_class_spec.spl`
and its run-path probe. The reported shape alone stays green — only the
class-sweep detection spec caught it.

### Original report (OPEN, JIT ONLY) — superseded by the update above

```simple
fn main():
    val s = "get(x):"
    val paren = "("
    print "A raw={s.index_of(paren)}"
    print "B coalesce={s.index_of(paren) ?? 999999}"
    val n = 3
    print "C n3={n ?? 777}"
    val m = 2
    print "D n2={m ?? 777}"
    val z = 0
    print "E n0={z ?? 777}"
```

| lane | A raw | B coalesce | C n3 | D n2 | E n0 |
|------|-------|-----------|------|------|------|
| interpreter | 3 | 3 | 3 | 2 | 0 |
| JIT | 3 | **999999** | **777** | 2 | 0 |
| native | \- | \- | \- | \- | \- |

Native cannot compile `??` at all: `cannot compile to standalone native binary
... main: [TryOperator]`. So there is no native reading, and a native spec
cannot gate this.

**Correction to the earlier report.** The prior note recorded "BOTH engines
corrupt — Rust seed interpreter AND the deployed native binary", and concluded
from that a host-path spec would not false-green. That is wrong at this commit:
the interpreter is CORRECT and only the JIT corrupts. A spec run under
`bin/simple_seed test` executes the tree-walking interpreter and will therefore
pass while the defect is fully live on the default engine.

Note case C: the receiver is not a search result at all, just `val n = 3`. Any
i64 whose value is 3 is affected, so this is not scoped to `index_of`/`find`.
Cases D and E pin that it is specifically the value 3 and not a general failure.

**Mechanism.** `TAG_SPECIAL = 0b011` (`src/compiler_rust/runtime/src/value/tags.rs:7`)
and `rt_is_none` (`src/compiler_rust/runtime/src/value/objects.rs:332`) tests

```rust
if value.0 == 0 || value.0 == super::tags::TAG_SPECIAL {
```

so a raw, unboxed machine word of 3 is nil by construction. The interpreter
holds a properly typed `Value` and never reaches that comparison; the JIT hands
`rt_is_none` an unboxed i64. The parse side is `Expr::Coalesce`
(`parser/src/expressions/postfix.rs:538`), lowered at
`compiler/src/hir/lower/expr/control.rs:925` (`lower_coalesce`).

**Why it is not a one-line fix.** `HirType` has no Optional variant, so `??`
cannot tell an `Option<i64>` from a raw `i64` and cannot decide whether the nil
test is even meaningful. The real fix is the existing plan at
`doc/03_plan/compiler/type_system/seed_hirtype_optional_plan.md`. Suppressing
the nil test whenever HIR says "int" would fix these cases but silently break
any genuine `Option<i64>` that HIR has already collapsed to int.

**Standing rule until fixed:** never write `search(...) ?? default` on a text or
array receiver; compare `< 0`. `?? -1` is always redundant and `?? 0` is worse.

## 3 — `.find()` result breaks `text[:idx]` — FIXED, and never tag-boxing

**This was misdiagnosed.** It is not a tag-boxing defect. It is a lexer/parser
collision, and it had nothing to do with `.find()`.

The discriminator that settles it — a single space:

| expression | JIT result on `"abcdefg"`, `q = 5` |
|------------|-----------------------------------|
| `r[:q]` | `f` — WRONG, evaluated `r[q]` |
| `r[: q]` | `abcde` — correct |
| `r[:5]` | `abcde` — correct |
| `r[:(q)]` | `abcde` — correct |

A tag-boxed bound would have produced a shifted offset, not the single character
at the bound, and a space could not have repaired it. The cause: the lexer fuses
`:` plus an identifier character into a symbol literal
(`parser/src/lexer/mod.rs:444`), so `r[:q]` reached the parser as `Symbol("q")`,
missed the "slice with no start" branch, and fell through to the plain-index
path. `r[:5]` was safe because a digit cannot start a symbol name; `r[: q]` was
safe because the space stops the fusing. `.find()` was incidental — any variable
bound reproduced it, including `val plain = 3`.

| lane | before | after |
|------|--------|-------|
| interpreter | error: `cannot index string with type` symbol | correct |
| JIT | silently returned `r[idx]` | correct |
| native | error: `NotYetImplemented("symbol")` | error: `CollectionOps` |

Fixed in `b47e4212c17a44bf144fa067446ec7ef6e823c3b`. The `s[start:end]` path
already carried a Symbol-to-Identifier rewrite; that was lifted into a shared
helper and applied to the `s[:end]` path too. Gated by nine new examples under
BUG-RT-001 in `test/01_unit/std/runtime_parser_bugs_spec.spl`, each red before
the fix with a `symbol` type error and green after.

**The native lane is still unfixed, for a different reason.** `CollectionOps`
means the native backend has no slice lowering at all. That gap predates this
fix and was simply masked by the symbol error arriving first. Filed here rather
than silently left implicit.

The 49 `[:identifier]` sites in owned `.spl` code were all slice bounds, none of
them symbol-keyed indexing, so the fix carried no ambiguity cost. The
`.substring()` rewrites previously landed as workarounds remain correct and do
not need reverting.

## 4 — `to_text` on an erased `Any` bool — FIXED, verified 2026-08-07

**Update 2026-08-07:** re-ran the repro below (both the combined 4-case
version and an isolated 2-line-output version containing only the
`Any`-parameter case, to rule out the "one unsupported op demotes the whole
program to the interpreter" trap) against today's deployed `bin/simple`
(`bin/release/x86_64-unknown-linux-gnu/simple`, self-identifies at startup as
"a bootstrap seed only", mtime 2026-08-07 04:52). Confirmed real JIT
engagement via `RUST_LOG=cranelift=debug` — the isolated probe alone produced
68 lines of Cranelift IR ending in the call/return for `show()`. Ran a second
time under `SIMPLE_EXECUTION_MODE=interpret`. Both re-run lanes now render
`erased_true=true` / `erased_false=false` correctly; JIT no longer prints
`nil`/`0` for a bool passed through an `Any`-typed function parameter.
**Native was not re-run** — this update only covers interpreter and JIT, per
the two lanes asked for; native's "correct" in the table above is carried
over unverified from the original report. No specific fixing commit was
identified by searching recent `src/compiler_rust/` history (checked
`81c58562fac`, the tuple-printer fix from item spirit above — it touches
`io_print.rs` tuple formatting only, not bool/Any call-argument passing, so it
is not the fix). Locked in for the interpreter lane (the only lane
`bin/simple test` can reach) with
`test/01_unit/language/any_erased_bool_to_text_spec.spl` — that spec does
**not** cover the JIT lane where the defect actually lived; JIT status must be
re-verified manually via `bin/simple run` + `RUST_LOG=cranelift=debug` per this
update, not by the test suite.

### Original report (OPEN, JIT ONLY) — superseded by the update above

```simple
fn show(v: Any) -> text:
    return v.to_text()

fn main():
    val t: Any = true
    val f: Any = false
    print "direct_true={true.to_text()}"
    print "erased_true={show(t)}"
    print "erased_false={show(f)}"
    val arr: [Any] = [true, false]
    print "arr0={arr[0].to_text()} arr1={arr[1].to_text()}"
```

| lane | direct_true | erased_true | erased_false | arr0 / arr1 |
|------|-------------|-------------|--------------|-------------|
| interpreter | true | true | false | true / false |
| JIT | true | **nil** | **0** | true / false |
| native | true | true | false | true / false |

**The boundary is the function parameter, not `Any` erasure in general.** A bool
read out of an `[Any]` array and formatted is correct on all three lanes; only
a bool passed into an `Any`-typed parameter corrupts, and only under the JIT.
That narrowing is new — the earlier report attributed the fault to
`rt_to_string` mishandling an erased bool, but `rt_to_string` formats the array
case correctly on the same lane in the same program, so the formatter is not
the broken component. The JIT is passing the bool through the call boundary
unboxed, and `rt_to_string` is then decoding a raw `1`/`0` as a tagged word.

Native being correct rules out the shared runtime formatter and points at the
Cranelift call-argument path specifically.

**Workaround unchanged:** compare directly, `value == true` / `value == false`,
which is unaffected on every lane.

## Method note

Two of the four original reports were wrong about which lanes were affected,
and one was wrong about the subsystem. Both errors pointed the same way — toward
believing a shared cause existed. The three-lane table is what separated them,
and in every case the interpreter was the correct lane, so any spec that runs
only under the interpreter is not a gate for this family.

Fixture validity bit twice nearly produced a false reading: `"x={x}"` written
into a repro is an interpolation, not a literal, and needs `\{`. A repro that
errors is not evidence about the defect. See
`reference_a_sweep_that_doesnt_enumerate_the_family_leaves_siblings`.
