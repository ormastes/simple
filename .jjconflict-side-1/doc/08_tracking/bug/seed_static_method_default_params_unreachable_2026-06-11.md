# Seed interpreter: static methods with default params unreachable with fewer args

- **Status:** FIXED IN SEED — pending redeploy (workaround in shell.spl still in place)
- **Fixed:** 2026-06-12 in `src/compiler_rust/compiler/src/interpreter_method/special/objects.rs`
- **Found:** 2026-06-11 while fixing
  `std_shell_file_dir_ops_false_2026-06-11.md` (S1)
- **Severity:** medium — silently makes any static class method with optional
  parameters uncallable with fewer arguments; error surfaces as
  `unknown static method <name> on class <cls>`, hiding the real cause.

## Detail

`constructor_overload_score` in
`src/compiler_rust/compiler/src/interpreter_method/special/objects.rs` (~line 38)
requires an EXACT argument-count match and ignores default parameter values.
Example: `class dir` had `static fn create(path, recursive: bool = false)`;
calling `dir.create(path)` with 1 arg never matched the 2-param signature.

## Repro

```
class Probe:
    static fn make(a: i64, b: i64 = 0) -> i64:
        a + b
fn main():
    print(Probe.make(5))   # interpreter: unknown static method make on class Probe
main()
```

## Fix direction

Score overloads accepting `provided_args >= required_params` and
`provided_args <= total_params`, filling trailing defaults — mirror however
free-function default params are handled. Add an interpreter regression test.
Rust seed edit — needs the next authorized seed batch (queue with B3/B5).

## Fix applied

`constructor_overload_score` in `objects.rs` updated to:
- Count `required_params` = params without a `default` expression
- Accept calls where `required_params <= provided <= total_params`
- Award a 100-point exact-count bonus so exact overloads beat default-fill overloads
- The execution code (lines ~162+) already filled defaults correctly; only the
  scoring gate needed fixing

Before: `Probe.make(5)` → `unknown static method make on class Probe`
After:  `Probe.make(5)` → `5`

5 regression tests added in `objects.rs` `#[cfg(test)] mod tests`:
- `static_method_with_default_param_called_with_fewer_args` — core repro
- `static_method_exact_count_still_works` — exact-count path intact
- `exact_match_overload_preferred_over_default_fill` — overload preference
- `static_method_too_few_required_args_errors` — still errors correctly
- `static_method_too_many_args_errors` — still errors correctly

All 5 tests pass. `cargo build --release -p simple-driver` succeeds clean.
Shell spec `test/01_unit/lib/std/shell/file_system_spec.spl` stays 9/9.

## Workaround applied

`src/compiler_rust/lib/std/src/shell.spl` `class dir` reshaped to 1-param
methods (`create`, `create_recursive`, `remove`, `remove_recursive`) with
correct externs — see the S1 fix in `std_shell_file_dir_ops_false_2026-06-11.md`.
The workaround remains in place until the seed is redeployed.
