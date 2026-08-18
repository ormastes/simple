# Bug: unit-literal SI prefixes `_k`/`_m` (milli) don't scale, and semantic-wrapper `.suffix()` returns the wrong string

- **Date:** 2026-07-20
- **Status:** OPEN — re-measured RED 2026-08-17 (see "Re-verification 2026-08-17" below)
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

## Re-verification 2026-08-17 — STILL RED (executed, not inferred)

Binary identity:

```
$ readlink -f bin/simple
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
$ stat -c '%s %y' "$(readlink -f bin/simple)"
59537240 2026-08-17 12:58:51.339525019 +0000
```

Command and result:

```
$ bin/simple test test/feature/usage/unit_types_spec.spl --no-session-daemon
SI Prefixes
  ✗ uses kilo prefix
    expected 5 to equal 5000
  ✓ uses mega prefix
  ✗ uses milli prefix
    expected 500 < 1.0 to hold
Semantic Wrapper APIs
  ✓ uses unit wrappers in public function signatures
  ✗ supports helper functions around semantic wrapper units
    expected time to equal ms
SPEC FILE VERDICT: ... declared>=21 executed=21 passed=18 failed=3 dropped=0
Results: 21 total, 18 passed, 3 failed
```

All three original failures reproduce byte-identically on the 2026-08-17 binary
(`5` vs `5000`, `500 < 1.0`, `time` vs `ms`), and `2_Mm` still passes — the
kilo/milli asymmetry is unchanged.

### Why not fixed in this pass (not feasible in `.spl`)

The unit-literal SI-prefix path is **Rust-seed-only**. The multiplier lookup is
`decompose_si_prefix` in `src/compiler_rust/compiler/src/interpreter_unit.rs:49`,
called from `src/compiler_rust/compiler/src/interpreter/expr/units.rs:70,94`;
`.suffix()` resolution is in
`src/compiler_rust/compiler/src/interpreter_method/special/types.rs`. The
pure-Simple `src/compiler/30.types/units/unit_registry.spl` contains no
`si_prefix` symbol and no `k`/`m` multiplier table at all, so there is nothing on
the `.spl` side to correct. `bin/simple` is the Rust seed (it prints the seed
banner on every run above), so any fix requires a Rust edit plus a seed rebuild —
outside a `.spl`-only change and outside this pass's scope. Left OPEN with the
fresh RED evidence above.

## Re-run 2026-08-17 on the NEWLY REDEPLOYED Rust seed — STILL RED

Binary identity: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
md5 `669150b61f2f20401a6a895ae54e9fee`, size 59550432, mtime
2026-08-17 20:10:45 UTC.

```
$ timeout 3000 nice -n 19 bin/simple test \
    test/feature/usage/unit_types_spec.spl --no-session-daemon
  ✗ uses kilo prefix
    expected 5 to equal 5000
  ✓ uses mega prefix
  ✗ uses milli prefix
    expected 500 < 1.0 to hold
  ✗ supports helper functions around semantic wrapper units
    expected time to equal ms
Results: 21 total, 18 passed, 3 failed
EXIT=1
```

**Verdict: STILL-OPEN.** All three failures reproduce byte-identically on the
newly redeployed seed, and `2_Mm` still passes — the kilo/milli asymmetry is
unchanged by the rebuild.
