# Native binaries silently drop an interpolated `print` containing a call

- **Status:** OPEN — native/AOT codegen, **silent data loss** (exit 0, no output)
- **Filed:** 2026-08-10
- **Severity:** high. This is a *fail-open* defect: the build succeeds, the binary
  runs, the exit code is 0, and the expected output simply never appears. It is
  strictly worse than a loud build failure, and it silently invalidates any
  native-lane check whose oracle is "it built".

## What happens

A `print` of a plain literal works natively. A `print` of an **interpolated**
string whose placeholders contain a **call** produces no output at all.

Measured with the deployed seed against a pinned pristine tree at origin
`275d6466cd2`, i.e. with **no source edits of any kind**:

| binary (origin-built, unmodified) | source | native output | interpreter oracle |
|---|---|---|---|
| `hello.spl` | `print "HELLO-NATIVE"` | `HELLO-NATIVE` | `HELLO-NATIVE` |
| `n3.spl` | `print "P1={c.get()}"` | *(nothing)*, rc=0 | prints |
| `n6.spl` | interpolated + call | *(nothing)*, rc=0 | prints |
| `n5.spl` (after the desugar fix) | `print "N5={bump(c)},{bump(c)}"` | *(nothing)*, rc=0 | `N5=1,2` |

`hello.spl` is the positive control and separates "native output is broken" from
"this program is broken": non-interpolated `print` reaches stdout fine.

## Why it matters beyond the missing text

`n3` and `n6` are two of the three `PASS` rows in the bisection table of
`class_scalar_field_assignment_fails_native_mir_lowering_2026-08-10.md`. They were
scored `PASS` purely on `native-build` exit status; nobody executed the binaries.
Both in fact produce **no output**. Any bisection or gate that treats
"native-build succeeded" as PASS is fail-open against this defect.

## Unblock condition

A native binary built from a program whose `main` does
`print "X={f()}"` must write the same bytes to stdout as
`SIMPLE_EXECUTION_MODE=interpret ... run` does. Re-run the four rows above; all
four must match the interpreter oracle, with `hello.spl` still passing as the
control, and the check must assert on the **output**, never on the exit code.
