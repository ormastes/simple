# Seed interpreter: static methods with default params unreachable with fewer args

- **Status:** open (workaround: avoid default params on static class methods)
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

## Workaround applied

`src/compiler_rust/lib/std/src/shell.spl` `class dir` reshaped to 1-param
methods (`create`, `create_recursive`, `remove`, `remove_recursive`) with
correct externs — see the S1 fix in `std_shell_file_dir_ops_false_2026-06-11.md`.
