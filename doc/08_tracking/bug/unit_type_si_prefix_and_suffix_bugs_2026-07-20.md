# Bug: unit-literal SI prefixes `_k`/`_m` (milli) don't scale, and semantic-wrapper `.suffix()` returns the wrong string

- **Date:** 2026-07-20
- **Status:** open (found triaging `test/feature/usage/unit_types_spec.spl`)
- **Area:** unit-type SI-prefix literal parsing / semantic-wrapper unit
  registry (interpreter or lexer, not isolated further in this pass), deployed
  seed at `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

Three independent failures, all "Status: Implemented":

```
✗ uses kilo prefix
  unit length(base: f64): m = 1.0
  val dist = 5_km
  expect dist.value() == 5000    --> expected 5 to equal 5000 (kilo scaling not applied)

✗ uses milli prefix
  unit time(base: f64): s = 1.0
  val dur = 500_ms
  expect dur.value() < 1.0        --> expected 500 < 1 to hold (milli scaling not applied)

✗ supports helper functions around semantic wrapper units
  unit Milliseconds: u64 as ms
  val total = plus_two(42_ms)     # 42_ms + 2_ms
  expect total.value() == 44      --> passes
  expect total.suffix() == "ms"   --> expected time to equal ms
```

Notably `2_Mm` (mega prefix) in the same file's "uses mega prefix" example
**passes** (`2000000.0`, correct) — so SI-prefix handling is not uniformly
broken, only kilo (`k`) and milli (`m`) are affected in the tests exercised
here.

The third failure is distinct: `total.suffix()` returns the string `"time"`
instead of `"ms"`. `"time"` is not a substring/identifier appearing anywhere
in *this* example's own `unit Milliseconds: u64 as ms` declaration — it
matches the name of an unrelated `unit time(base: f64): s = 1.0` declared in
a **different** `it` block earlier in the same file ("uses milli prefix",
line 163). This looks like the same class of global/non-module-scoped-registry
collision already documented elsewhere in this repo for classes and top-level
functions (same name declared in two different scopes overwrites a shared
global table) — here affecting locally-scoped `unit` declarations across
sibling `it` blocks in one file, with `.suffix()` apparently resolving against
whichever `unit` definition registered last/matches loosely, rather than the
one lexically in scope for `total`'s declared type.

## Fix direction (not applied — compiler-internals change, needs rebuild)

1. SI-prefix multiplier table: verify the lookup/multiplier for `k` (kilo,
   ×1000) and `m` (milli, ×0.001) specifically — `M` (mega, ×1e6) works, so
   the table exists and is reachable; something case- or key-specific to `k`
   and lowercase `m` is wrong (possibly a collision between milli-`m` and the
   unrelated base-unit label `m` used for meters in `unit length(...)` in the
   same file, or between kilo-`k` and some other reserved key).
2. `unit` declaration registry: confirm `unit` types declared inside separate
   `it`/`describe` blocks are scoped per-block (or per-file) and not
   overwriting each other in a shared global table by matching some other key
   (e.g. base numeric type `u64`/`f64`) instead of the declared name.

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/unit_types_spec.spl --no-session-daemon
```
Not checked against the pure-Simple self-hosted compiler or a compiled/native
path — only the Rust seed interpreter was probed. Not isolated to a minimal
standalone repro in this pass (time-boxed); the full spec file is the
reproduction vehicle.
