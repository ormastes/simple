# `native-build` crashes on module-level globals with a binary-expression initializer (self-hosted compiler, not the Rust seed)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

Filed while following up on
`doc/08_tracking/bug/jit_run_file_pipeline_gaps_2026-07-30.md`'s own
side-finding that `native-build --entry`/`--entry-closure` was failing in
that pass's environment. That document's initial read of the failure
("worker exited with code 1", tracing to warnings in unrelated
compiler-internal files) was itself a misdiagnosis — corrected here.

## PROVED: the real error, and what it is not

`--verbose` output shows the actual fatal error clearly once the noise
(hundreds of pre-existing style-lint warnings the tool prints while
processing every file it touches) is filtered out:

```
[STDERR] [native-build] Driver start: inputs=1 backend=cranelift mode=dynload
[ERROR] MIR error: MIR lowering error: unsupported MIR type kind: HirTypeKind::Infer((0, 0))
[STDERR] [native-build] Driver finished
[STDERR] error: native-build worker exited with code 1.
```

`inputs=1` confirms `--entry-closure` correctly scoped the *compile* to
the one target file — the many `src/compiler/*.spl` warning lines seen
in a plain (non-`--verbose`) run are not evidence of scanning unrelated
files by mistake; see the architecture note below for why they appear at
all. The actual failure is a single, precise internal error.

**Not stale cache / not environmental.** Reproduced identically with
`--clean --no-incremental --cache-dir <fresh empty dir>`. Rules out a
stale incremental-cache artifact as the cause.

## Architecture finding: `native-build`, invoked via the deployed/self-hosted binary, dispatches to the pure-Simple self-hosted compiler — NOT the Rust seed's `native_project` module

The error string `"unsupported MIR type kind: {type_.kind}"` does not
exist anywhere in `src/compiler_rust/**` (grepped the whole tree). It
exists in exactly one place: `src/compiler/50.mir/_MirLowering/
function_lowering.spl:586`, part of the **pure-Simple, self-hosted**
compiler implementation.

This means `native-build` on the deployed/self-hosted `bin/simple`
(and on a freshly cargo-built Rust-seed candidate binary acting as its
own interpreter for the same worker script — both were tested and both
reproduce identically) does its actual compilation work by
**interpreting the self-hosted compiler's own `.spl` source** as the
compiler, not by calling into `src/compiler_rust/compiler/src/pipeline/
native_project/*.rs` (the Rust module this pass's parent document,
`jit_run_file_pipeline_gaps_2026-07-30.md` §§1-12, spent considerable
effort reading and diffing `run_file_jit` against). This explains the
`src/compiler/*.spl` warning noise precisely: those are not unrelated
files accidentally swept in — they *are* the compiler doing the
compiling, loaded and interpreted as source.

**Caveat this creates for the parent document:** §§1-12 there compared
two Rust-seed code paths (`run_file_jit` vs. `native_project::
compiler.rs`) against each other, which is a valid, self-consistent
comparison for characterizing the Rust seed's own internal behavior
(relevant to bootstrap-stage native builds driven by the seed itself),
but it is **not** what `bin/simple native-build` actually executes for
an ordinary end user on the deployed, self-hosted binary. That document
should carry this caveat; not rewritten here since this pass is scoped
to filing the crash, not re-auditing that document's framing.

## Minimal repro (two independent forms confirm the trigger is "binary-expression module-level initializer", not identifier references specifically)

```simple
val BASE = 10
val DERIVED = BASE + 5     # identifier reference inside a binary op

fn main():
    print("BASE={BASE} DERIVED={DERIVED}")
```
```simple
val DERIVED = 5 + 5        # two literals, no identifier reference at all

fn main():
    print("DERIVED={DERIVED}")
```

Both crash identically:

```
$ simple native-build --entry main.spl --entry-closure -o out --backend cranelift
[ERROR] MIR error: MIR lowering error: unsupported MIR type kind: HirTypeKind::Infer((0, 0))
error: native-build worker exited with code 1.
```

**Controls that succeed**, isolating the trigger precisely:

| Fixture | native-build result |
|---|---|
| No module-level globals at all (`fn main(): print("hello")`) | Succeeds, runs correctly |
| `val X = get_value()` (function-call initializer) | **Succeeds — and correctly prints `X=42`** |
| `val DERIVED = BASE + 5` (identifier + literal, binary op) | Crashes: `HirTypeKind::Infer((0, 0))` |
| `val DERIVED = 5 + 5` (two literals, binary op) | Crashes: identically |

`HirTypeKind::Infer(id: i64, level: i64)` (`src/compiler/20.hir/
hir_types.spl:685`) is a Hindley-Milner-style type-inference placeholder;
`(0, 0)` is the very first type variable ever allocated, never unified.
The `case _:` fallback at `function_lowering.spl:586` — the HIR-type-to-
MIR-type conversion function — has explicit cases for `Named`, `Never`,
and (with an explicit "fail-soft... degrade to the tagged any/i64 slot"
comment) `Error`, but no case for `Infer`. Something upstream in the
self-hosted compiler's own type-inference pass creates a fresh type
variable for the binary operator's result (or an operand) and never
substitutes it with a concrete resolved type before HIR is handed to MIR
lowering, for this specific construct.

## Bonus finding: the self-hosted compiler's function-call module-init handling is MORE complete than the Rust seed's

`val X = get_value()` compiled and ran **correctly** (`X=42`) via
`native-build` — in contrast to both `run_file_jit` and `simple compile
--native` (both give `X=0`, the write-side defect documented in
`jit_run_file_pipeline_gaps_2026-07-30.md` §12-§13). This means that
document's §13.3 framing — treating "affects AOT" as a single, uniform
fact about "the shared codegen backend" — needs a precise correction:
the write-side defect, as characterized there, is specific to the **Rust
seed's** `generate_module_init` (`codegen/common_backend.rs`), which
`simple compile --native` shares with `run_file_jit`. The self-hosted
compiler is an independently-implemented pipeline with its own,
different completeness for this exact case — it gets function-call
initializers right, and has its own, different, newly-discovered bug for
binary-expression initializers instead of the Rust seed's silent-zero
behavior. Two independent implementations, two independent (and
different-shaped) defects for two different initializer forms — not one
shared defect.

## Severity and disposition

This is a **real, reproducible, minimal-repro regression** in the
self-hosted compiler's own MIR lowering, not an environmental or
stale-cache artifact (ruled out with `--clean --no-incremental` and a
fresh cache directory) and not a "files I didn't mean to compile"
red herring (the `src/compiler/*.spl` warnings are the compiler itself,
correctly loaded to do the compile). It is a **hard crash** (no output
binary produced, non-zero exit, "worker exited with code 1"), not a
silent-wrong-answer defect — the safer failure mode of the two, but it
means `native-build` cannot build any project containing a module-level
global with a non-trivial (needs real type inference, not just
const-folding) initializer expression at all, today.

**Not fixed this pass.** Filed per instruction ("if it's a real
regression, minimal repro and file it"). A fix belongs in the self-hosted
compiler's own type-inference/unification code
(`src/compiler/20.hir/**`, wherever `Infer` type variables for a global
initializer's binary-op result are supposed to get resolved before HIR
lowering hands off to MIR) or, as a narrower stopgap matching the
existing `Error`-case precedent, adding an `Infer` arm to
`function_lowering.spl`'s `case _:` fallback that degrades to the same
`MirType.i64()` fail-soft slot `Error` already uses — either is a
distinct piece of work in a codebase (`src/compiler/**`) this session's
JIT-focused sweep never otherwise touched, and is left for its own pass.
