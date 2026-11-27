# Seed LLVM backend rejects float `%`, so the seed cannot build the simple-core archive (2026-11-22)

Status:
- Compile gap: FIXED in seed source (this change). Takes effect in the next seed build. The
  Phase 1 seed `ac2e90625c2a` in use today still fails.
- Canonical float `%` semantics: OPEN, for the owner to decide (see "Open").

## Symptom

Coordinator-requested archive build, Windows MSVC, LLVM 23:

```
SIMPLE_BINARY=<seed ac2e90625c2a>/simple.exe SIMPLE_CORE_BUILD_DIR=<wt>/build/essential-apps/simple-core \
  TARGET=x86_64-pc-windows-msvc sh scripts/check/check-simple-core-runtime-smoke.shs
simple_core_archive_complete=false
error=archive_part_failed:core_any_ops
  src/runtime/simple_core/core_any_ops.spl: llvm codegen: semantic: Unsupported float binop: Mod
```

The seed supports `native-build --emit-archive`. The first part, `core_any_ops.spl`, fails at
`rt_any_mod` line 94, `any_as_f64(left) % any_as_f64(right)`. No `libsimple_runtime.a` is produced,
so every essential app built with `--runtime-bundle simple-core` is blocked on both compilers.

## Root cause

`src/compiler_rust/compiler/src/codegen/llvm/instructions.rs`: the float-float binop match
handled Add/Sub/Mul/Div/Pow and comparisons, but `Mod` fell through to
`unsupported_operation("float binop", Mod)`.

## Fix

Lower float `Mod` with LLVM `frem`, which is truncated (C fmod, sign of the dividend). That
matches:
- the seed interpreter: `src/compiler_rust/compiler/src/interpreter/expr/ops.rs:1211-1234`,
  Rust `%` on f64/f32. It gives `-7.5 % 2.0 == -1.5` and errors when `r == 0`.
- both `rt_any_mod` runtime twins: `src/compiler_rust/runtime/src/value/collections.rs:4533`
  and `src/runtime/runtime_any_ops.c:32`, which uses `fmod`. The simple-core archive's
  `rt_any_mod` must agree with them.

A first revision used floored modulo; review blocked it as inconsistent with the above.

## Open (owner decision)

1. **Cross-backend divergence on mixed signs.** The seed Cranelift backend is floored
   (`codegen/instr/core.rs:376-382`, `a - floor(a/b)*b`). The seed interpreter, both runtime
   twins, and now LLVM truncate. Additionally, `simple.exe run` of
   `fn f64_mod(a: f64, b: f64) -> f64: a % b` printed `-7.5 % 2.0 = 0.5` and
   `7.5 % -2.0 = -0.5` (floored) on this seed. That `run` path apparently does not go through
   `ops.rs` and should be included in the decision. No language doc fixes the sign rule.
2. **`r == 0`.** The interpreter raises E3001 "modulo by zero". `frem` (LLVM) and `fmod`
   (C runtime) return NaN.

## Specs

- Reproducing: `src/compiler_rust/compiler/tests/llvm_float_mod_native.rs` builds
  `test/fixtures/native/f64_mod/main.spl` with LLVM/core-C, runs it, and expects
  `PASS float-mod-truncated-semantics`.
- Generalization: the fixture checks all four f64 operand-sign combinations
  (7.5%2.0=1.5, -7.5%2.0=-1.5, 7.5%-2.0=1.5, -7.5%-2.0=-1.5).
- Verified 2026-11-22 (Windows MSVC, LLVM 23, `cargo test --release -j 8 --test
  llvm_float_mod_native --features llvm`):
  - with the fix: `test result: ok. 1 passed; 0 failed`.
  - with `instructions.rs` from `origin/release/1.0.0`: `Unsupported float binop: Mod`,
    `test result: FAILED. 0 passed; 1 failed`.

## Related defect (open, not fixed here)

f32 on the seed LLVM/core-C lane is broken independently of `%`. In the same native fixture,
`fn f32_add(a: f32, b: f32) -> f32: a + b` called as `f32_add(5.5f32, 2.0f32)` returned `0.0`,
and an f32 `%` result printed as an integer. f32 is therefore not in this fixture. It needs
its own record and spec.

## Unblock condition

Rebuild the seed with this fix. Re-run `check-simple-core-runtime-smoke.shs` with it, then the
essential-apps queue with `SIMPLE_SIMPLE_CORE_PATH=<archive>`.
