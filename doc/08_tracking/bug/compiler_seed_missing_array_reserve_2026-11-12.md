# Rust seed lacks the `Array.reserve` builtin (2026-11-12)

Status: open
Area: src/compiler_rust (bootstrap seed codegen) vs src/lib stdlib parity

## Symptom

Every spec that exercises product code paths which call `.reserve(...)` on a
builtin array fails at runtime under the Rust seed with:

```
Runtime error: Function 'Array.reserve' not found
Runtime error: unresolved symbol -- this is a code-generation dispatch gap,
not a program error. Refusing to substitute a placeholder value ...
```

Confirmed on the phase-2 Windows lane (seed `bin/simple.exe`, release/1.0.0).
Example: `test/02_integration/compiler/cache/coherent_snapshot_cas_spec.spl`
(9 of 9 examples fail) imports
`compiler.frontend.snapshot.compile_snapshot_freezer`, whose line 79 calls
`combined.reserve(left.len() + right.len())` on a builtin array.

Minimal repro fixture (run with the seed):

```
fn main():
    val a: [i64] = []
    a.reserve(4)
    a.push(1)
    print(a.len())
```

## Root cause

Product code under `src/compiler` and `src/lib` uses `array.reserve(...)`
(~20 files, e.g. `10.frontend/snapshot/compile_snapshot_freezer.spl`,
`20.hir/hir_codec_support.spl`, `55.borrow/hir_ownership_*.spl`,
`nogc_async_mut/async_ring/simple_ring.spl`). The pure-Simple toolchain
implements this builtin; the Rust bootstrap seed never emitted a dispatch for
it, so any seed-run spec touching those modules fails with the dispatch gap.
This is a seed/stdlib parity gap, not a defect in the specs or in the
pure-Simple product code.

## Unblock

Implement `Array.reserve` in the seed (or regenerate the seed from a
pure-Simple build that has it). Until then, the affected integration specs
can only run green under the rebuilt pure-Simple producer.
