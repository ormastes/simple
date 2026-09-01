# Bug: if/elif/else chain mis-routed to else inside a BDD it-closure

- Date: 2026-06-30
- Component: interpreter / test runner (BDD it-block closure evaluation)
- Severity: medium (breaks otherwise-correct specs; not a library defect)
- Status: RESOLVED 2026-06-30 — seed fix landed (`block_execution.rs` closure
  `Node::If` handler now walks `elif_branches`).

> NOTE: the original title/hypothesis below ("enum value corrupted when passed
> as a function arg") was a MISDIAGNOSIS. Minimal isolation (see Actual root
> cause) proved the call/enum framing is a red herring; the real defect is the
> closure-block `if` executor silently dropping every `elif` branch.

## Symptom

In `test/01_unit/lib/common/compress_utilities_spec.spl`, the example
"reports the runtime-selected tier with a stable public name" fails:

```
expected avx2 to equal neon
```

The spec computes a payload-less enum value, passes it to a helper, then
compares it with `==`:

```
val detected = compression_simd_tier_detect()          # CompressionSimdTier.avx2 on this host
val name = compression_simd_tier_name(detected)         # "avx2"  (correct)
if detected == CompressionSimdTier.scalar: ...
elif detected == CompressionSimdTier.avx2: ...          # NOT taken (bug)
else: expect(name).to_equal("neon")                     # taken -> fails
```

`detected` is genuinely `avx2` (the prior `.to_equal` assertion passes and
`compression_simd_tier_name(detected)` returns `"avx2"`), yet the subsequent
`detected == CompressionSimdTier.avx2` evaluates false **inside the it-block**.

## Actual root cause (isolated via minimal repros)

The same code runs correctly under `bin/simple run`. The failure is specific to
BDD it-block closure evaluation in the test runner, in BOTH default and
`SIMPLE_EXECUTION_MODE=interpret` modes.

Decisive minimal isolation (scratchpad probes):
- `if detected == Tier.avx2: ... else: ...` (single if/else) → PASSES.
- `if detected == Tier.scalar: ... elif detected == Tier.avx2: ... else: ...`
  (the matching branch is an **elif**) → FAILS, taking the `else` branch.
- Two separate `if` statements, or an `if/else` whose `else` does the avx2 check
  → PASS. Pre-computing `detected == Tier.avx2` into a `val` stays `true`.

So enums, function arguments, and write-back are **not** involved. The defect is
purely structural: the closure-block `if` executor never evaluated
`elif_branches`.

`IfStmt` carries `condition`/`then_block`, `elif_branches:
Vec<(Option<Pattern>, Expr, Block)>`, and `else_block`. The canonical
`interpreter_control.rs::exec_if` walks the elif branches between the main
condition and the else (it even carries a note about a previous identical bug,
lines 184-185). But the BDD it-block closure path uses a *separate* `Node::If`
handler in `interpreter_call/block_execution.rs` (two copies, ~L446 and ~L1145)
which only handled the let-pattern, the main condition→then_block, and the
else_block — **silently dropping every `elif` branch**. When the main condition
was false, control jumped straight to `else`, so `if scalar / elif avx2 / else
neon` reported `neon`.

## Fix

`src/compiler_rust/compiler/src/interpreter_call/block_execution.rs` — both
closure-block `Node::If` handlers now gate on a `handled` flag and iterate
`if_stmt.elif_branches` (mirroring `exec_if`: plain-condition `.truthy()` and
`Option<Pattern>` elif-binding via `pattern_matches`) before falling through to
`else_block`. As a side effect this also fixes the latent case where a failed
main `if let`/`if val` pattern skipped elif branches.

## Impact / verification

`compress_utilities_spec` was 10/11; after the fix it is **11/11, 0 failures**.
The underlying library code
(`compression_simd_tier_detect/_name/_from_simd_profile`) was always correct —
verified standalone. Any spec using an `if/elif/else` chain inside an `it` block
was affected, regardless of the value type being compared.
