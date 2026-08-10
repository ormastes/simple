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

## 2026-08-09 re-measurement — still OPEN, and worse than "prints nothing"

Re-measured while chasing a report that "`x = obj.m()` and `[obj.m()]` die
silently with exit code 0". That report is a **false premise** (see below), but
the probe re-confirmed *this* defect and sharpened it in two ways.

Binary for all rows: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
which self-identifies as the Rust **bootstrap seed**. AOT rows are
`bin/simple native-build --entry-closure`, which executes the **pure-Simple**
compiler from `src/compiler/**`.

> **AOT-row caveat — read before reusing these numbers.** At the time of
> measurement this shared working copy carried another session's *uncommitted*
> wide-integer heap-boxing work in `src/runtime/runtime_native.c`
> (`RT_VALUE_HEAP_INT` / `RtCoreWideInt` / `rt_value_int_wide`; none of it exists
> on `origin/main`, cf.
> `int61_bit_truncation_jit_scalars_and_native_container_boxing_2026-08-09.md`).
> That in-flight code called `rt_value_int_wide` nine lines above its own
> definition, so `runtime_native.c` failed to compile under C99
> implicit-declaration rules and **every** `native-build` run died with
> `BUILD_RC=1`, no binary, and zero `^error:` lines from the Simple compiler —
> a build break that is easy to misread as a compiler defect. A local
> forward declaration (`int64_t rt_value_int_wide(int64_t value);`) restores the
> lane; it is deliberately NOT committed here because the surrounding feature
> belongs to that other session and landing it would carry their unfinished work.
> The AOT rows below were taken with that local declaration applied. They are
> unaffected by it — it only decides whether the runtime compiles at all — but
> anyone reproducing on a clean `origin/main` checkout will not hit the break,
> since none of the wide-int code is there yet.

| probe (value position) | interpreter | seed JIT | AOT `native-build` |
|---|---|---|---|
| `val a = Active` (bare enum variant) | rc=1 `semantic: variable 'Active' not found` | **rc=0**, prints `E-end 0` | — |
| `val x = totally_undefined_thing` | rc=1 `semantic: variable ... not found` | **rc=0**, prints `H-end 0` | **rc=1, no binary** |
| `val x = b.nosuchmethod()` | rc=1 `method ... not found on type 'Box'` | rc=70, loud `Function 'Box.nosuchmethod' not found` | — |
| `val xs = [b.nosuchmethod()]` | rc=1 same | rc=70, loud | — |

### Sharpening 1 — it fabricates `0`, it does not "drop the module"

This doc's Symptom section says the JIT produces "no program output". That is
not the general shape. With `print(...)` calls on both sides of the bad binding,
the JIT **runs the whole program to completion** and substitutes **`0`** for the
unresolved symbol: `H-start` / `H-end 0` / rc=0. So the failure mode is not a
silently-dropped module — it is a **fabricated value in a program that reports
success**, which is strictly worse for any consumer than producing nothing.
(The original repro showed no output because its `print` was itself downstream
of the failed resolution.)

### Sharpening 2 — unresolved *methods* already fail closed; only *variables* fail open

The JIT is not uniformly fail-open. An unresolved **method** call exits **70**
with a clear `Runtime error: Function 'Box.nosuchmethod' not found`. Only
unresolved **variable / bare-enum-variant** references in value position fall
through to the silent const-0 path. Anyone narrowing this defect should probe
variables, not methods.

### The AOT lane fails CLOSED

`native-build` on the unresolved-variable probe exits **1 and emits no binary**.
So this is a seed-JIT-specific fail-open, not a whole-toolchain property, and
the pure-Simple lane is not implicated by these probes. That matches this doc's
existing note that the driver's error propagation is Rust-seed code in
`src/compiler_rust/` — which is why no fix is applied here.

### The "`x = obj.m()` / `[obj.m()]` silent rc=0" report is REFUTED

Both shapes were built and run on all three engines with a well-formed method
(`class Box: n: i64; me get() -> i64`). All three produce correct output and
rc=0-with-output:

- interpreter: `A-got 7`, `B-len 1`
- seed JIT: `A-got 7`, `B-len 1`
- AOT `native-build`: builds `BUILD_RC=0`, binary runs rc=0, prints
  `A-start A-got 7 A-end` and `B-start B-len 1 B-end`

There is no defect in binding a method-call result to a variable or placing it
in a list literal. The real silent-rc=0 shape is the unresolved-**variable** row
above, i.e. this bug, which was already filed on 2026-08-04.

## 2026-08-09 re-verification (worktree agent)

Re-ran the original bare-enum-variant repro fresh in an isolated worktree with
no pure-Simple `bin/simple` deployed (gitignored symlink target absent), using
the main repo's seed binary directly
(`/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple`,
which still self-identifies as "bootstrap seed only"):

```
$ bin/simple run probe_enum.spl
bare-module-level: 0
EXIT=0
```

Confirms the doc's "fabricates 0" finding exactly — same fabricated-const-0,
rc=0 behavior as the 2026-08-09 table above. Root cause remains in the Rust
seed's JIT driver (`src/compiler_rust/**`), which is out of scope for a
`.spl`/`.shs`-only fix per this session's mandate. **Confirmed
ARCHITECTURAL-OPEN** — no safe root-cause fix available in pure-Simple source;
leaving OPEN with this fresh evidence rather than closing.

## Why it matters here

Any legacy spec or probe that shells out to `bin/simple run` and scores the exit
code is fail-open against this: a program that cannot even resolve its symbols
scores as a pass.
