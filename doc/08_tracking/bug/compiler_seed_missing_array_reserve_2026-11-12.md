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

## FIXED 2026-11-13 (wave-2 deep-fix lane, work/compiler-seed-deepfix-20261113)

`[T].reserve(additional)` now dispatches on every seed lane. The defect was a
whole dispatch surface, not one switch: the HIR array-method table had no
`reserve` entry (the call fell through to generic dynamic dispatch typed
`Any`, and codegen emitted a cross-module fallback for the unresolvable name
"Array.reserve" -> `rt_function_not_found`, exit 70). Changes:

- `hir/lower/expr/mod.rs` — type `reserve` VOID (static dispatch).
- `interpreter_method/collections.rs` — `reserve` arm: evaluate the arg,
  return unit. NOT in the self-update MUTATING_METHODS list (contents are
  unchanged; write-back would clobber the receiver with the unit value).
  `method_registry/builtins.rs` registers it with `is_mutating: false` for
  the same reason (the record's canonical repro reserves on a `val` array;
  reserve is a capacity hint, not an observable mutation).
- Cranelift JIT: `codegen/instr/closures_structs.rs`
  `try_compile_builtin_method_call` gains a `reserve` arm compiled as a NO-OP
  returning the receiver (capacity hint with no observable effect; no runtime
  call emitted). `codegen/instr/methods.rs` and `common_backend.rs` updated to
  match; the LLVM lane (`codegen/llvm/*`) maps `reserve` to the real runtime
  grower `rt_array_reserve`.
- Runtime: new `rt_array_reserve` in `runtime/src/value/collections.rs`
  (grows only the element buffer for len+additional across byte-packed /
  u64-packed / generic layouts; header stays stable), re-exported through
  `value/mod.rs`, declared in `codegen/runtime_sffi.rs` and
  `elf_utils.rs`, and exposed to the interpreter SFFI table
  (`interpreter_extern/sffi_array.rs`).

Verification (tracked seed rebuilt via the pinned bootstrap profile and
deployed to bin/simple.exe): the record's minimal repro prints 1 under both
`SIMPLE_EXECUTION_MODE=interpret` and `=jit` (previously: dispatch-gap abort
in both). Pinned spec `coherent_snapshot_cas_spec.spl`: 9/9 failing -> 6/9
passing. The remaining 3 examples ("checkout-relative presentation roots",
"digest corruption quarantine", "final-component symlink") fail with
`cas-root-authority-unavailable` from `cache_host_open_root_v1`
(src/compiler/80.driver/cache/cas/verified_cas_store.spl:128) -- a host
filesystem-authority path unrelated to the reserve dispatch gap, not
investigated in this lane. Canary context_log_modes_spec stays 4/4.

NOTE: a seed refresh (rebuild + redeploy of bin/simple.exe) is required to
deploy this Rust-side fix; the rebuilt binary is intentionally not committed.
