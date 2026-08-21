# Why 69% of `check-no-jit-module-drop.shs`'s scope was "unmeasurable" — and how much of that gap is real

Date: 2026-08-18
Lane: COVERAGE
Guard: `scripts/check/check-no-jit-module-drop.shs`
Defect class fenced: paren-less accessor (`.length`, `.len`, `.size`, `.empty`,
`.chars`, `.first`, `.last`, `.capacity`) on a builtin container, which silently
de-JITs the WHOLE enclosing module to the tree-walk interpreter.
Background: `doc/08_tracking/bug/paren_less_accessor_whole_module_de_jit_2026-08-08.md`

## The problem this report addresses

Run as the hook runs it (`--candidates`), the guard reported:

```
PASS — 415 module(s) checked, 0 paren-less accessor de-JIT drops
       (127 compiled clean, 288 unmeasurable), selftest fired in both directions
```

288 of 415 modules — 69% — were classified UNMEASURABLE and explicitly excluded
from the verdict. The guard was honest about it, but a headline of
"415 module(s) checked" with the qualifier in a parenthetical is easy to misread
as 415 measured. It was 127.

## Finding 1 (the load-bearing one): most of the gap was never a gap

The oracle is `bin/simple compile <f> -o out.smf`, and any non-zero exit that did
not carry the accessor diagnostic was counted UNMEASURABLE. That conflated two
very different things:

- failures that happen **before or instead of** HIR lowering — the module's
  function bodies were never lowered, so the oracle genuinely never looked;
- failures that happen **after** HIR lowering completed — the module WAS fully
  lowered, the accessor gate WAS evaluated, and the failure is downstream.

`cannot compile to standalone SMF: N function(s) contain constructs that require
the interpreter` (`src/compiler_rust/compiler/src/pipeline/execution.rs:286`) is
the second kind. It is a property of the lowered result, not a gate in front of
lowering.

**Proved by mutation, not by reading the compiler.** Appending

```
fn zz_probe_accessor():
    val xs = [1, 2, 3]
    print xs.length
```

to `src/app/portal/git_views.spl` — a real module that fails with the
standalone-SMF error — makes the compiler report `cannot infer field type while
lowering` INSTEAD. The accessor error strictly precedes the standalone-SMF error.
So "standalone-SMF error present AND accessor signature absent" is positive
evidence of absence: lowering ran to completion and found nothing.

The same mutation applied to modules failing for the OTHER reasons
(`Undefined(...)`, `parse:`, `lint:`) did NOT surface the injected `.length` —
those genuinely never reach lowering and correctly stay unmeasured. Verified on
`src/app/model3d/main.spl`, `src/app/interpreter/memory/refc_binary.spl`,
`src/app/interpreter/perf/perf_spec.spl`.

## Finding 2: the WHY breakdown

(counts filled in from the post-change run — see the verdict at the bottom)

## Finding 3: cross-contaminated logs

`WORK` and the per-drop logs lived at fixed paths under a shared `$LOG_DIR`, and
~10 sessions share this checkout. Two concurrent instances raced on the same
`$LOG_DIR/work/one.log`, and the second instance's startup `rm -rf "$WORK"`
deleted the first's scratch mid-scan — which is why logs named for one file were
found containing another file's error. Fixed: every run now writes under a
run-unique `$LOG_DIR/run-<pid>-<epoch>/`, and the two summary lists are published
at the stable paths only by an atomic rename at the END of the run, so a reader
can never see a half-written list from a run still in flight. (The 31-line
`unmeasurable.txt` observed mid-investigation was exactly that: a truncated list
belonging to a run still in progress.)

## What changed in the guard

1. New classification `LOWERED_CLEAN` — measured, counted toward coverage, on the
   evidence above. It is NOT an allowlist and NOT a silent pass: it is a weaker
   but sufficient oracle, and the reason string it keys on is the only one with
   that property.
2. Selftest grown from 2 fixtures to 5, still fatal, still bidirectional:
   - `xs.length` -> DROP
   - `xs.len()` -> CLEAN
   - `?`-operator module (non-standalone-SMF, no accessor) -> LOWERED_CLEAN
   - same module + `zs.length` -> DROP
   - module with an undefined identifier + `.length` -> UNMEASURABLE
   The last fixture is the one that holds the line: if a future widening of
   `LOWERED_RE` ever let a never-lowered module count as measured, it fires.
3. Verdict wording: SELECTED and MEASURED are now two distinct numbers with a
   percentage, and the NOT-MEASURED count is stated as NOT covered. "checked" is
   no longer used as a headline noun.
4. The NOT-MEASURED remainder is bucketed by reason in the output
   (undefined-identifier / parse / lint / smf-emission / silent-timeout / other)
   so the gap reads as several tractable problems rather than one opaque number.
5. Run-unique log directory (Finding 3).

Fail-closedness re-proved by mutation after the change: blinding `DROP_RE`,
widening `LOWERED_RE` to `error`, and narrowing it to a non-matching string each
made `--selftest` exit 2 with a specific diagnosis. Restored script exits 0.

## Residual risk

Nothing here reduces the guard's strictness. The remaining NOT-MEASURED modules
are still not covered, and the honest position is that closing them needs a
better probe harness, not a looser verdict:

- **undefined-identifier** is the largest tractable class. These modules resolve
  only inside their package/import context; the probe compiles each file
  standalone. A harness that compiles the module with its declared imports (or
  drives the module through the project entry that owns it) would convert most of
  this class to measured. That is real work, not a one-liner.
- **lint** failures are the compiler refusing before it starts; a `--no-lint`
  compile path (which does not currently exist as a flag) would recover them.
- **parse** failures are genuine source defects and belong to other lanes.
- **silent/timeout** needs a longer `JIT_DROP_TIMEOUT` or a less loaded host;
  earlyoom is actively SIGTERMing multi-GB processes on this box, so some of this
  class is host noise rather than a property of the source.
