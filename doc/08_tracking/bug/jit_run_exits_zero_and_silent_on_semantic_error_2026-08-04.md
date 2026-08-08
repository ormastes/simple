# `bin/simple run` (JIT) exits 0 and prints NOTHING on a hard semantic error

**Status:** OPEN
**Found:** 2026-08-04
**Severity:** high · **Area:** compiler / JIT driver
**Found during:** legacy-feature-test triage (`test/03_system/feature/language`)

## Symptom

Minimal repro — a program whose only defect is an unqualified enum-variant
reference (bare enum literals are an unimplemented future feature, see
`doc/07_guide/quick_reference/syntax_quick_reference.md:1469`):

```simple
# build/probe_legacy_feature/probe_enum.spl
enum Status:
    Active
    Disabled

fn to_text(s: Status) -> text:
    match s:
        case Status.Active: "active"
        case Status.Disabled: "disabled"

fn main():
    val a = Active               # <- not resolvable
    print "bare-module-level: {to_text(a)}"
```

Default engine (JIT):

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple run build/probe_legacy_feature/probe_enum.spl
EXIT=0            # and no program output, no diagnostic
```

Interpreter, same file:

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run build/probe_legacy_feature/probe_enum.spl
error: semantic: variable `Active` not found
```

Actual: exit 0, empty stdout, no diagnostic — indistinguishable from a program
that ran and printed nothing.
Expected: the same `semantic: variable 'Active' not found` diagnostic and a
non-zero exit, as the interpreter produces.

Control: `build/probe_legacy_feature/hello.spl` (a `fn main` that prints) DOES
print under the same JIT invocation, so this is not "`run` never executes
`main`" — it is the erroring module being dropped silently.

## Root cause

Proved so far: the divergence is engine-selection, not source. The identical
file, same binary, same working directory, differs only by
`SIMPLE_EXECUTION_MODE=interpreter`. The JIT path swallows a hard semantic
error, produces no artifact, runs nothing, and still reports success. This is
the same failure class already recorded for the JIT fallback path — the runner
prints `[jit-fallback] HIR lowering error: ... whole module dropped to the
interpreter` for *supported* fallbacks and offers `SIMPLE_JIT_STRICT=1` to make
those fatal, but a *semantic resolution* failure produces no message at all.

Not yet isolated to a line in the driver; the observable contract violation is
what is proved here.

Measured with the binary deployed at the time:
`bin/release/x86_64-unknown-linux-gnu/simple` (2026-08-04 02:04), which
self-identifies as a Rust bootstrap **seed** ("this Rust-built Simple binary is
a bootstrap seed only"). The finding therefore applies to the seed's JIT path;
re-confirm against a self-hosted deploy before closing.

## Why not fixed now

Fail-open exit codes in the JIT driver are exactly the class of change that
needs its own lane: every green run recorded against `bin/simple run` since this
regression is suspect, so the fix has to arrive together with a re-baseline, and
the driver's error propagation is Rust-seed code in `src/compiler_rust/` rather
than pure Simple. Filed rather than patched blind.

## Why it matters here

Any legacy spec or probe that shells out to `bin/simple run` and scores the exit
code is fail-open against this: a program that cannot even resolve its symbols
scores as a pass.
