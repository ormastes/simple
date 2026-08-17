# BUG: declared function return types are not enforced by any engine

- **Filed:** 2026-08-09
- **Lane:** G4
- **Severity:** High (silent wrong values; hides entire defect classes)
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Discovered via:** `dotq_tail_position_in_bool_returning_fns_2026-08-09.md`

## Symptom

A function may return a value of any type from a signature declaring any other
type. No error, no warning, no coercion — the foreign value is passed straight
through to the caller.

## Reproduction (2026-08-09, `bin/simple run`)

```
fn ret_text() -> bool:
    "not-a-bool"

fn tail_dotq(xs: [text]) -> bool:
    xs.?          # yields [text]? per spec, never a bool

fn main():
    print("ret_text => " + ret_text().to_text())
```

Rust seed / default JIT:

```
ret_text           => <special:129>
tail_dotq nonempty => true
tail_dotq empty    => true
EXIT=0
```

Interpreter (`SIMPLE_EXECUTION_MODE=interpreter`), same source:

```
error: semantic: method `to_text` not found on type `array` (receiver value: [x, y])
EXIT=1
```

Three facts:
1. `ret_text() -> bool` returning a `text` literal compiles and runs to
   completion with **exit 0**, yielding the garbage value `<special:129>`.
2. The interpreter propagates the raw `array` out of a `-> bool` function; the
   only diagnostic arrives incidentally, from a *downstream* method lookup, and
   names the wrong thing (`to_text` not found) rather than the return-type
   violation.
3. The two engines produce different values for the same `-> bool` function, so
   the missing check also masks an engine-divergence bug.

## Impact

This is the gate that would have caught all 42 sites in the companion `.?` bug
at authoring time, five of them in compiler error-reporting paths. More broadly,
every `-> T` signature in the codebase is currently documentation rather than a
contract, so no return-type-shaped defect can be caught statically.

## Why it is not fixed in this change

Turning on return-type checking is not a contained edit:

- It belongs in `src/compiler/35.semantics/` / `src/compiler/30.types/type_system/checker.spl`,
  and must agree with the implicit-return (tail-expression) rule, `return` in all
  branch positions, `->` on lambdas, trait/impl method signatures, and generics.
- It will fail-loud across a large existing corpus that has never been checked —
  42 known `-> bool` violations alone, plus whatever else exists. Landing it
  without first repairing the corpus turns the build red.
- Two engines must be made to agree first (see fact 3 above); enforcing a
  contract that the backends implement differently just relocates the bug.

## Recommended sequencing

1. Repair the 42 `.?` sites (companion doc).
2. Add the checker in **warning** mode; census the true violation count.
3. Repair the census, then promote to error.

Do not promote to error before step 2 reports a number.


## Re-measurement 2026-08-17 (P0-core silent-wrong lane) — REPRODUCED, and worse

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 59,536,728 bytes, mtime
2026-08-16 22:59:37 UTC (Rust seed).

```
fn wrong_ret() -> i64:
    "notanint"

fn main():
    val v = wrong_ret()
    print v
```

| engine | output |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpreter` | `notanint` |
| `SIMPLE_EXECUTION_MODE=jit`         | `2910620488929` |

Exit 0 on both; no diagnostic from any phase.

The doc records this as "declared return types are not enforced by any engine",
which is true but understates the consequence. Two things this measurement adds:

1. **The two engines do not merely both fail to check — they produce DIFFERENT
   wrong answers.** The interpreter keeps the string, so `v` is a `text` in an
   `i64` binding and downstream arithmetic will fail somewhere else entirely,
   far from the cause. The JIT keeps the raw slot and prints it as an integer.
2. **The JIT's number is a heap address, not a value.** `2910620488929` is
   `0x2A5_5B0F_8FE1`-scale — the tagged heap pointer to the string, printed as
   an `i64` because the binding said `i64`. So an unenforced return type does
   not just yield a wrong number; it **leaks a live heap pointer into integer
   arithmetic**, where it can be added, compared, indexed with, or written to a
   file. That is a materially different severity argument from "the type is not
   checked", and it belongs in the case for prioritising the fix that this doc's
   "Why it is not fixed in this change" section defers.

No fix attempted here. The doc's own assessment that the fix is neither small
nor contained is not disputed by this measurement.

## Re-reproduced 2026-08-17 (batch_00) — still live, and the divergence widened

Confirmed on the deployed seed (`bin/simple`, mtime 2026-08-16 22:59). Fixture:

```simple
fn ret_text() -> bool:
    "not-a-bool"

fn main():
    val v = ret_text()
    print("ret_text => " + v.to_text())
```

| engine | exit | output |
|---|---|---|
| jit (default)                       | 0 | `ret_text => true` |
| `SIMPLE_EXECUTION_MODE=interpreter` | 0 | `ret_text => not-a-bool` |

Two changes since the 2026-08-09 filing, both making this *worse*, not better:

1. The JIT value drifted from `<special:129>` to **`true`**. The original garbage
   value at least looked wrong on sight; `true` is a plausible bool and will not
   attract a second glance. The defect is unchanged — a `text` literal is still
   being returned from a `-> bool` signature with no check — but its symptom is
   now camouflaged.
2. The interpreter no longer errors on this shape. On 2026-08-09 it happened to
   fail downstream (`method to_text not found on type array`). Here it exits **0**
   and prints the raw text straight through a `-> bool` signature. Both engines
   now exit 0 with different answers, so the incidental diagnostic that used to
   catch this case is gone.

Not fixed here, for the reason the original filing gives: enforcement belongs in
`30.types/type_system/checker.spl` / `35.semantics` and will fail loud across an
unrepaired corpus (42 known `-> bool` violations alone). This entry records only
that the bug is **live and re-confirmed**, and that the "already fixed?" question
is settled in the negative.

## 2026-08-17 (CRITICAL lane C3) — re-reproduced, root cause CORRECTED, staged fix landed

### Reproduction (EXECUTION evidence)

Fixture `fn ret_text() -> bool: return "not-a-bool"`, binary `bin/simple`
(Rust seed, mtime 2026-08-16 22:59):

| engine | rc | stdout |
|---|---|---|
| jit (default)                       | 0 | `<special:177>` |
| `SIMPLE_EXECUTION_MODE=interpreter` | 0 | `not-a-bool` |

Still live, still divergent, still exit 0 on both. (The JIT value has drifted
again — `<special:129>` → `true` → `<special:177>` — which only reinforces that
it is a raw slot being reinterpreted, not a value.)

### This doc's stated root cause is WRONG in both halves

1. **`30.types/type_system/checker.spl` is DEAD CODE.** Its own header,
   lines 11-19, states: *"`class TypeChecker` below has ZERO callers repo-wide
   and has never executed. It is NOT the compiler's type checker."* Writing
   enforcement there would have produced a second checker that never runs.
2. **The return-type check already exists and is already correct**, at
   `src/compiler/30.types/type_infer/inference_control.spl:564-574`:

   ```
   val has_return_type = fn_.return_type.kind != HirTypeKind.Infer(0, 0)
   if has_return_type:
       match self.infer_block(fn_.body):
           case Ok(body_ty):
               match self.subsume(body_ty, fn_.return_type):
                   case Err(e): self.error(e)
   ```

So this was never a missing-check bug. It is a **fail-open reporting** bug, in
two independent layers, both in
`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:797`:

- the whole pass was gated behind `SIMPLE_TYPECHECK_WARN=1`, **off by default**;
- even switched on, `run_typecheck_warn_pass` returned `[text]` and the caller
  only `log_warn`ed it — **it never pushed `ctx.errors`**, so the build could
  not fail regardless of what the diagnostics said.

This is the **same class** as the sibling lane's finding that unresolved `use`
imports surface only as `[use-warning]` at rc=0, and that an unknown extern
function logs an ERROR and then returns a default: a correct diagnostic is
computed and then discarded. Confirmed shared shape, not a coincidence.

### Fix landed: staged/opt-in enforcement, default unchanged

Blanket hard-error was rejected deliberately, per this doc's own step 2 ("do not
promote to error before step 2 reports a number"). Instead the pass is now
profile-gated exactly like the safety pass directly below it, which solved the
identical problem in lane SE1 (2026-07-28):

- new `src/compiler/80.driver/driver_typecheck_severity.spl` — `TypecheckPassSeverity`
  {Advisory, Warn, Deny} + `typecheck_pass_severity()` reading
  `SIMPLE_TYPECHECK_PROFILE`, reusing the shared `normalize_profile_name` table
  so profile names cannot drift between the two projections.
- `driver_hir_pipeline_passes.spl` — `run_typecheck_warn_pass` now takes `ctx`
  and routes each diagnostic: Advisory → log only (today's behaviour); robust →
  `ctx.add_warning`; critical/verified → `ctx.add_error` (fails the build).
- `driver_hir_pipeline_lowering.spl` — the pass runs when either
  `SIMPLE_TYPECHECK_WARN=1` (unchanged) **or** a non-Advisory profile is set.

Default (unset) is Advisory, i.e. byte-for-byte the previous behaviour. No
existing build changes.

### Corpus census — PARTIAL, and honestly so

- `-> bool` functions in `src/**` whose tail expression is a bare `.?`:
  **10** (`grep -rn -A3 -- "-> bool:" src/ --include=*.spl`, matching a bare
  `x.?` tail within 3 lines). The doc's "42 known violations" figure covered
  the whole corpus including `test/`, so the `src/` half appears to have been
  partly repaired since filing.
- **The real census — the number step 2 asks for — was NOT obtained.** It
  requires running `run_typecheck_warn_pass` over all ~993 modules, and the
  pure-Simple 80.driver pipeline is not executable here: the deployed
  `bin/simple` is the Rust seed, which does not run these `.spl` passes at all,
  and the stage-3 self-host bootstrap is the live blocker. **Do not promote past
  Advisory until that census is run on a self-hosted binary.**

### Specs

- `test/01_unit/compiler/types/declared_return_type_enforced_spec.spl`
  (reproducing; + fixtures `fixture_declared_return_type_violation.spl`,
  `fixture_declared_return_type_ok.spl` as the control arm)
- `test/01_unit/compiler/types/fail_open_diagnostic_pass_detection_spec.spl`
  (detection spec for the CLASS: a driver pass that computes a diagnostic it has
  no route to report)

The reproducing spec is **expected RED on the deployed seed** and is left red
per `.claude/rules/testing.md`: the seed cannot execute the pure-Simple driver,
so `SIMPLE_TYPECHECK_PROFILE` cannot reach it. Unblock condition: a self-hosted
`bin/simple`.

Status: remains **OPEN** — the mechanism is in place and default-safe, but
enforcement is not on, and the census that would justify turning it on is
unmeasured.
