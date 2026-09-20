# BUG: matching a `Result` value with `Some`/`nil` arms hits NEITHER arm — silently on interpret, exit 2 with no message on JIT

- **id:** option_pattern_against_result_value_matches_nothing_2026-09-19
- **status:** OPEN (the language defect). The one production casualty found so far is FIXED — see "Casualty" below.
- **severity:** P1 — a wrong answer with no diagnostic on one lane, and a non-zero exit with **no output at all** on the other
- **found:** 2026-09-19, while landing an 8-day-old unpushed commit and discovering main had diverged

## Symptom

A `match` whose scrutinee is `Ok(...)`/`Err(...)` but whose arms are
`case Some(v)` / `case nil` matches **nothing**. There is no type error, no
warning, and the two lanes fail differently.

Probe (whole file):

```simple
fn returns_ok() -> text:
    Ok("the-template")

fn main() -> i64:
    val r = returns_ok()
    var seen = "none"
    match r:
        case Some(v):
            seen = "Some:" + v
        case nil:
            seen = "nil"
    print "option-match = " + seen
    var seen2 = "none"
    match returns_ok():
        case Ok(v):
            seen2 = "Ok:" + v
        case Err(e):
            seen2 = "Err:" + e
    print "result-match = " + seen2
    0
```

| lane | `option-match` | `result-match` | exit | stderr |
|---|---|---|---|---|
| `SIMPLE_EXECUTION_MODE=interpret` | `none` — **neither arm ran**, the variable kept its initialiser | `Ok:the-template` | 0 | empty |
| default (JIT) | **blank line** — the concatenation produced nothing | `Ok:the-template` | **2** | **empty** |

The control row matters: the *same* value matched with `Ok`/`Err` arms works on
both lanes, so the value is fine and the scrutinee is fine. It is the
Option-pattern-over-Result-value combination that vanishes.

Two things make this worse than a plain mismatch:

- **The interpret lane leaves the binding at its previous value and exits 0.**
  Downstream code proceeds with whatever was there before — this is a wrong
  answer, not a crash.
- **The JIT lane exits 2 with nothing on stdout or stderr.** A non-zero exit
  with no diagnostic anywhere is the hardest possible failure to trace back to
  its cause.

Note also that `fn returns_ok() -> text` returning `Ok("...")` is itself
accepted without complaint, which is how the mismatch gets created in the first
place.

## Casualty in production code (fixed separately)

`CompilationContext.load_template` is declared `-> GenericTemplate?` and its one
call site (`src/compiler/40.mono/instantiation.spl`) matches
`case Some(value)` / `case nil`. Both implementations were declared `-> text`
and returned `Ok(...)` / `Err(...)`:

- `src/compiler/70.backend/linker/linker_context.spl` — `LinkerCompilationContext`
- `src/compiler/80.driver/pipeline/compiler_context.spl` — `CompilerCompilationContext`

Three different types for one method. The linker context is live — built at
`src/compiler/70.backend/linker/lazy_instantiator.spl:265` and handed to
`TemplateInstantiator` on the next line — so on the lazy-instantiation path a
template that **exists** was neither returned nor reported missing, and the
`self._drop_in_progress(key)` cleanup in the `nil` arm never ran.

Both implementations are now aligned to the trait's Option contract
(`-> GenericTemplate?`, returning `Some(...)` / `nil`).

### How it got this way, which is the instructive part

An unpushed commit from 2026-09-11 fixed the same contradiction by unifying
everything on `Result<GenericTemplate, text>` — trait, call site, and both
implementations. It never landed. Meanwhile another session fixed the **call
site** the other way, to `Some`/`nil`, matching the trait. Each change was
locally reasonable; together they left the two implementations stranded in a
third type. Landing the 2026-09-11 commit as-is would have reverted the newer
call-site change, so the Option direction — the one already on `main` — was
followed instead.

## Why no spec caught it

`test/01_unit/compiler/common/compilation_context_template_contract_spec.spl`
now pins the Option contract in both the hit and miss directions, including an
example that fails specifically if **neither** arm runs (the defect's
signature). It deliberately does **not** assert what an Option pattern does to a
Result value: that is the defect, and asserting the broken answer would bless
it.

No spec could have caught the original, because nothing constructed these two
contexts — `grep` over `test/` finds zero references to either class.

## What to fix in the language

A pattern whose enum family does not match the scrutinee's should be a
compile-time error. Failing that, a `match` that falls off the end of every arm
must not be silent — and must certainly not exit 2 with nothing written
anywhere. The exit-2-no-message behaviour should be treated as its own defect
even after the type mismatch is rejected.

## Related

- `duplicate_impl_method_definitions_silent_first_wins_2026-08-08` and
  `nested_fn_name_collision_across_scopes_2026-09-19` — the same theme: two
  declarations of one name that disagree, with nothing checking they agree.
