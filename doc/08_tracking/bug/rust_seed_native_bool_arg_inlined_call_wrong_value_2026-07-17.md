# Rust-seed native codegen: bool-arg function call returns wrong value after inlining

## VERIFIED FIXED 2026-08-17 — does not reproduce

Classified by content and execution, not SHA ancestry (brief correction #1).
Executed against the deployed `bin/simple`, default lane:

```
fn pick(flag: bool) -> i64:
    if flag: 111
    else:    222
print(pick(true))   # => 111
print(pick(false))  # => 222
val t = true; val f = false
print(pick(t))      # => 111
print(pick(f))      # => 222
```

Both the literal-argument form (which is what gets inlined and const-folded)
and the variable-argument form return the correct value. Two distinct
non-zero constants are used deliberately: a 0/1 pair would pass even if the
bool were being reinterpreted as its raw payload.

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

## 2026-08-17 — triage shard A6: reproducer located, class spec added

- The doc names `codegen/instr/body.rs` as the suspect file. That file contains
  no inliner at all: it is MIR vreg type stamping (`build_vreg_types`), and its
  only "inline" occurrence is a comment at line 71. The "inlining" in the title
  is the original author's inference from a CLIF dump, not a located code site.
  Root cause is therefore still UNLOCATED; do not treat body.rs as confirmed.
- A live reproducer already exists in-tree and is currently disabled:
  `src/compiler_rust/compiler/tests/compile_and_run.rs:241-256`,
  `#[ignore = "OPEN: Rust-seed native inlining corrupts false bool arguments; ..."]`
  `fn native_bool_argument_false_survives_inlined_calls()`, asserting
  `compile_native_and_run("... return f(false) * 10 + f(true)") == 1`.
  Un-ignore it the moment it passes; that is the reproducing gate.
- Class-detection spec added:
  `test/01_unit/compiler/codegen/native_bool_argument_marshalling_class_spec.spl`
  — sweeps seven members of the bool-argument-marshalling class in a single
  native-build subprocess (literal `false`, runtime falsy expr, both polarities
  packed into one decimal, bool RETURNED not branched on, bool in the second
  parameter slot, bool forwarded through two hops, `not`-produced bool), each
  asserted against absolute literals plus an explicit absence check for the
  false-arrives-truthy fingerprint.
