# LLVM backend does not lower `ResultMatchSemantic`

**Status:** Open — top remaining blocker for native-building `Result`-using stdlib modules
**Observed:** 2026-08-24
**Area:** 70.backend / LLVM lowering

## Relationship to the io_runtime blocker

Split out of `io_runtime_import_borrow_local13_native_build_2026-08-24.md`
(FIXED in `9e3eb1adccd`). That record's two defects — the expression-position
`if val` binding loss in the seed interpreter, and the Return borrow check
rejecting every `Ref`-containing function — are both fixed, and both of its
filed signatures now count **zero** on the io_runtime fixture.

This is the **third, distinct** defect that surfaced underneath them. It is
what now blocks `use std.nogc_sync_mut.io_runtime`.

## Reproduction

Seed built from the fixed tree; exit code read DIRECTLY into a variable on the
line after the command, never through a pipe.

```simple
use std.nogc_sync_mut.io_runtime

fn main():
    val v = env_get("HOME")
    print("control ok")
```

```text
$ "$SEED" native-build control.spl -o control.bin
$ NB_RC=$?
NB_RC=1
```

## Verbatim error

```text
error: E-BACKEND-LLVM-INST-ResultMatchSemantic: LLVM backend does not lower ResultMatchSemantic at unknown location
error: semantic: panic: compile error: E-BACKEND-LLVM-INST-ResultMatchSemantic: LLVM backend does not lower ResultMatchSemantic at unknown location
```

Measured 7 occurrences on a `std.nogc_sync_mut.io.file_ops` fixture.

## Scope

Affects modules whose functions return `Result<...>` and match on it —
`io.file_ops` and `io_runtime` confirmed. Modules that do not reach this
instruction now native-build and run end to end (`std.common.math`,
`std.nogc_sync_mut.io.signal_stubs`, both verified NB_RC=0 with the produced
binary executed).

## Not this defect

Two further, independent MIR-lowering gaps were measured on the same pass and
are NOT this record:

- `std.common.text` — `MIR lowering error: unresolved method call: index_of`
- `std.nogc_sync_mut.fs` — `MIR lowering error: undefined variable Dir`

## Diagnostic-quality note

The error reports `at unknown location` — no file, line, or function. The same
gap on the interpreter side is what made the previous defect unlocalizable
until a provenance probe was added (`SIMPLE_DEBUG_UNDEFINED_VAR=1`, see the
parent record). Attaching a real span here is worth doing before investigating.
