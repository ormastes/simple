# `native-build` pays a ~209 s fixed cost per invocation regardless of input size, and emits no reuse receipt

- **ID:** native_build_fixed_cost_floor_hides_incrementality_2026-08-08
- **Date:** 2026-08-08
- Status: OPEN (P3)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Severity:** high for developer loop cost; not a correctness defect.

## Why this doc exists

`05f677a1dcc` landed the correction that **incremental is already the default**
(`--no-incremental` / `--clean` are the opt-outs, and `SIMPLE_NATIVE_INCREMENTAL=1`
is a no-op on the default pipeline). That closed the *flag* question.

This doc reports what happens when you stop reading flags and put a clock on it.
The headline is not the one I expected to write: the dominant cost is not
recompilation at all.

## The measurement

Deployed pure-Simple binary, `bin/simple native-build`, same host, back to back,
on a loaded box (~20 competing builds). Fixture modules are 2–4 lines each.

| run | inputs | command | wall | max RSS |
|-----|--------|---------|------|---------|
| **floor** | **1 module (2 lines)** | `native-build --clean` | **209.16 s** | 2,605 MB |
| cold | 7 modules | `native-build --clean` | 261.68 s | 2,637 MB |
| warm, nothing changed | 7 modules | `native-build` | 225.32 s | 2,611 MB |
| warm, one file edited | 7 modules | `native-build` | 267.66 s | 2,612 MB |

**A single two-line module takes 209 seconds to build.** That is the floor, and
it is 80% of the seven-module cold build. Six additional modules cost ~52 s
total, about **8.75 s of marginal cost per module** against a ~209 s fixed
per-invocation tax.

## What follows, and what does NOT

**Do not** read the warm rows as "incrementality is broken." They cannot carry
that claim. The cache-sensitive portion of a 7-module build is only the ~52 s
marginal band; the 225–268 s spread across the warm runs is the same order as
the noise from competing load. The one-file-edit run came out *slower* than
cold, which is a tell that noise dominates rather than that a rebuild is
pathological. An earlier draft of this doc concluded "rebuilds reuse nothing";
that conclusion was not supported by its own data and has been withdrawn.

What the data **does** support:

1. **The fixed floor is the real developer-loop cost.** At ~209 s for one
   trivial module, no amount of incremental reuse can make the edit-build loop
   fast. Optimising module-level reuse before cutting the floor targets at most
   20% of the wall clock on a 7-module build, and proportionally less on a
   smaller one. Compare the same class of problem in `bin/simple lint`
   (383 modules re-parsed per invocation, ~4.4 s / 339 MB every run, no cache) —
   the repo rule in `.claude/rules/code-style.md` that production wrappers should
   execute cached compiled artifacts rather than raw source applies here too, and
   at 209 s the violation is two orders of magnitude more expensive.

2. **There is no reuse receipt.** Grepping stdout+stderr of all four runs for
   `cache|reuse|incremental|skip` returns **0 lines**. The default pipeline never
   states what it reused. This is why the flag reading was never going to settle
   the question and why the experiment above needed a floor control to be
   interpretable at all: there is nothing to read, so every "incremental works
   now" claim is unfalsifiable.

## What would close it

In priority order:

1. **Emit a reuse receipt on the default pipeline** — one line per unit, reused
   vs recompiled, with the cache key. Cheapest item here, and it is a
   precondition for anyone measuring items 2–3 honestly rather than by stopwatch
   subtraction.
2. **Profile and cut the ~209 s floor.** Establish where it goes (compiler
   startup, module-graph load, backend init, link) before optimising. It is the
   whole game.
3. Only then revisit per-module cache granularity, with a fixture large enough
   that the marginal band exceeds the noise — on these numbers that means
   **dozens** of modules, not seven.

## Reproduce

```
bin/simple native-build --clean <ONE trivial module> -o out   # the floor -- do this FIRST
bin/simple native-build --clean <N modules> -o out            # cold
bin/simple native-build         <N modules> -o out            # no-op warm
# touch one module, then repeat the warm run
```

Measure with `/usr/bin/time -f "%es %MkB"`. Take the floor before anything else:
without it the other three numbers cannot be interpreted, which is the mistake
this doc's first draft made.

Do not use a `bin/simple build` bootstrap run for this — different pipeline,
different receipt, and conflating the two is how the original flag confusion
arose.

## Related

- `05f677a1dcc` — incremental is already the default (flag-level correction)
- [[reference_simple_native_incremental_is_a_noop_on_the_default_pipeline]]
- [[reference_lint_startup_tax_383_modules_no_cache]] — same shape, smaller scale
- `doc/08_tracking/bug/plain_parse_loop_never_checks_par_had_error_silent_swallow_2026-08-08.md`
  — the collect-all-errors half of the same "default build behaviour" campaign
