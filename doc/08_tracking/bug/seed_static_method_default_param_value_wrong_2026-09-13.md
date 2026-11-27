# Seed interpreter: static-method default parameter fills the constant 3, not the declared value

Status: FIXED (already, verified 2026-11-06; re-verified 2026-11-11 lane interp12 on fresh seed 46fe8f6b6def — `static_default 105 42 105` under both `SIMPLE_EXECUTION_MODE=interpret` and the default run lane) — see "Resolution" and "Addendum 2026-11-11"
Date: 2026-09-13
Severity: HIGH — silent wrong answers; no error is raised
Component: Rust seed interpreter (`src/compiler_rust`), static-method overload/default fill
Found: while triaging `seed_static_method_default_params_unreachable_2026-06-11.md`
Binary: `bin/simple` Rust seed v1.0.0-rc.1 (Windows)

## Symptom

Omitting a defaulted parameter on a **static class method** binds the constant `3`
instead of the declared default expression. Free functions are unaffected.

## Repro (measured)

```spl
class Probe:
    static fn make(a: i64, b: i64 = 100) -> i64:
        print("b={b}")
        a + b
    static fn one(x: i64 = 42) -> i64:
        print("x={x}")
        x
fn freefn(a: i64, b: i64 = 100) -> i64:
    print("free b={b}")
    a + b
fn main():
    Probe.make(5)
    Probe.one()
    freefn(5)
main()
```

`bin/simple run` prints:

```
b=3
x=3
free b=100
```

Declared defaults of `0`, `42` and `100` all yield `3`. With `b: i64 = 0`,
`Probe.make(5)` returns `8` rather than `5`.

## Notes

- This is the successor defect to `seed_static_method_default_params_unreachable_2026-06-11.md`
  (that one is closed: the method is now reachable; only the filled VALUE is wrong).
- `constructor_overload_score` and the default-fill loop in
  `src/compiler_rust/compiler/src/interpreter_method/special/objects.rs:288-296` LOOK correct
  (they evaluate `param.default` in an empty env), so the failing dispatch is probably a
  different static-method path — needs a debugger, not a re-read.
- Not fixed here: `src/compiler_rust` must not be edited while a bootstrap is running.

## Resolution (verified 2026-11-06)

No longer reproduces on a seed built from `release/1.0.0` @ `ecb705896a4` (debug).
`test/fixtures/seed_interp/static_method_default_param_repro.spl` prints
`static_default 105 42 105` (`Probe.make(5)`, `Probe.one()`, `freefn(5)`)
under both `SIMPLE_EXECUTION_MODE=interpret` and the default `run` lane.
No code change in this pass.


## Addendum 2026-11-11 (lane interp12) — re-verified FIXED on fresh seed 46fe8f6b6def

**Verification actually run** (worktree simple-p3-interp12-20261111, seed-smoke):

```
SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe SIMPLE_EXECUTION_MODE=interpret \
  ./bin/simple.exe run test/fixtures/seed_interp/static_method_default_param_repro.spl --no-cache
# static_default 105 42 105        (rc=0)

# default run lane:
./bin/simple.exe run test/fixtures/seed_interp/static_method_default_param_repro.spl --no-cache
# static_default 105 42 105        (rc=0)
```

Declared defaults (`100`, `42`) bind correctly for static methods and the free
control on both engines. Verdict: STALE (no new code change this lane).
