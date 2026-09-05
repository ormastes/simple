# Rust-seed native codegen: bool-arg function call returns wrong value after inlining

**Status:** Found, NOT fixed (out of scope for the lane that found it) **Found:** 2026-07-17,
while verifying the C3 (`and`/`or` short-circuit) fix in
`simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md`.
**Path:** `src/compiler_rust` `CompilerPipeline::compile_native` /
`compile()` (cranelift native path), via the `compiler/tests/compile_and_run.rs`
harness (`compile_native_and_run`).

## Repro

Minimal, **no `and`/`or` involved at all**:

```simple
fn f(x: bool) -> i64:
    if x:
        return 1
    return 0

fn main() -> i64:
    return f(false)
```

Expected: `0`. Actual: `1`.

- `f(true)` alone (single call) returns the correct `1`.
- `f(false)` alone (single call) returns the wrong `1` — deterministic, not flaky.
- Same wrong result whether the argument is the literal `false` token or a
  runtime-computed falsy expression (`1 > 2`).
- `f`'s own compiled body is provably correct in isolation (traced by hand at
  the Cranelift CLIF level: `block0` loads/branches on the param correctly,
  both arms return the right constant). The bug is in how `main`'s call site
  marshals/constant-propagates the `false`-valued argument when `f` gets
  inlined into `main` — `main`'s own CLIF dump shows `f`'s body fully inlined
  (no `call` instruction), and the false-argument path's `icmp_imm`
  nonetheless resolves as if the argument were truthy.
- A separate, related symptom: `fn main() -> i64: return f(false) + f(true)`
  (two calls to the same small function, combined via `+`) crashes the host
  process with SIGSEGV (jump to an unmapped address, `r11`/`r14` show
  poison-looking bit patterns typical of an uninitialized/garbage value used
  as a control-flow target) — reproduces identically with a plain `if x:` `f`
  body, i.e. with zero `and`/`or`/short-circuit code involved.

## Why this matters

This blocks black-box `cargo test` verification of *any* fix to boolean
control flow in the cranelift native backend when it's exercised through a
separate callee taking a `bool` parameter — including the C3 short-circuit
`and`/`or` fix. `f`'s own CLIF is sound; only the call across the (inlined)
function boundary corrupts the value. Likely candidates: the inliner's
handling of `false`-typed/valued arguments during constant propagation, or
`main`'s block-param/value aliasing when the callee's blocks get spliced in
(see the alias chains — many `vN -> vM` lines — in the CLIF dump for `main`
in the repro above).

## Verification workaround used for C3

Static analysis (manual CLIF trace) of `f`'s own compiled body, plus the
pre-existing hosted interpreter path (`bin/simple run`, unaffected — it has
its own, already-correct, short-circuit evaluator in
`interpreter/expr/ops.rs`), were used instead. Dynamic native-codegen
verification of C3 needs this bug fixed (or a repro shape that avoids
separate-function `bool` arguments) first.

## Contained regression coverage

The exact two-call shape is preserved as the ignored Rust integration test
`native_bool_argument_false_survives_inlined_calls` in
`src/compiler_rust/compiler/tests/compile_and_run.rs`. Its decimal-packed
result, `f(false) * 10 + f(true)`, must equal `1`, so the tens digit directly
covers the broken `f(false)` value while the ones digit checks the known-good
`f(true)` control.

The test is intentionally ignored while this issue is OPEN because the current
native path can return the wrong value or crash the test process. Remove the
`#[ignore]` only after the standalone `f(false)` repro returns `0` and the
two-call packed repro repeatedly returns `1` without a crash.

## Suggested next step

Bisect the inliner / cranelift GVN pass with `SIMPLE_DEBUG_DUMP_CLIF`-style
instrumentation (temporary — none currently lands with this doc) around
`compiler/src/codegen/instr/body.rs`'s per-function compile loop, focused on
how a `false`-literal/computed argument's `Value` gets propagated across the
inlined call boundary vs. a `true`-valued one (which works).
