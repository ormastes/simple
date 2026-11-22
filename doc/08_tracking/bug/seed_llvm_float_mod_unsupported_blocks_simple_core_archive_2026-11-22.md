# Seed LLVM backend rejects float `%`, so the seed cannot build the simple-core archive (2026-11-22)

Status: FIXED in seed source (this change). Takes effect in the next seed build; the
Phase 1 seed `ac2e90625c2a` in use today still fails. No `.spl` workaround applied.

## Symptom

Coordinator-requested archive build, Windows MSVC, LLVM 23:

```
SIMPLE_BINARY=<seed ac2e90625c2a>/simple.exe SIMPLE_CORE_BUILD_DIR=<wt>/build/essential-apps/simple-core \
  TARGET=x86_64-pc-windows-msvc sh scripts/check/check-simple-core-runtime-smoke.shs
simple_core_archive_complete=false
error=archive_part_failed:core_any_ops
  src/runtime/simple_core/core_any_ops.spl: llvm codegen: semantic: Unsupported float binop: Mod
```

The seed does support `native-build --emit-archive`. The first part it compiles is
`core_any_ops.spl`, and that part fails at `rt_any_mod` line 94:
`any_as_f64(left) % any_as_f64(right)`. No `libsimple_runtime.a` is produced.

Consequence: every essential app built with `--runtime-bundle simple-core` is BLOCKED on both
compilers. The bundle needs `SIMPLE_SIMPLE_CORE_PATH`, and no archive exists on this host. The
sanctioned producer is Stage 4 (`bootstrap-from-scratch.sh:7080`).

## Root cause

`src/compiler_rust/compiler/src/codegen/llvm/instructions.rs`, float-float binop match: it
handled Add/Sub/Mul/Div/Pow and comparisons, but `Mod` fell through to
`unsupported_operation("float binop", Mod)`. The cranelift backend implements it as floored modulo
(`codegen/instr/core.rs`, `BinOp::Mod`, `is_float`: `a - floor(a/b)*b`). The interpreter agrees
(Phase 1 `run`: `-7.5 % 2.0 == 0.5`, `7.5 % -2.0 == -0.5`).

## Fix

Add the `BinOp::Mod` arm computing `l - llvm.floor(l / r) * r` (f64 or f32 intrinsic by
operand type). LLVM `frem` was deliberately not used: it is C fmod and would disagree with
the interpreter and cranelift on mixed signs.

## Specs

- Reproducing: `src/compiler_rust/compiler/tests/llvm_float_mod_native.rs` builds
  `test/fixtures/native/f64_mod/main.spl` with LLVM/core-C, runs the binary and expects
  `PASS float-mod-floored-semantics`.
- Generalization: the fixture covers all four f64 operand-sign combinations.
- Verified 2026-11-22 (Windows MSVC, LLVM 23, `cargo test --release -j 8 --test
  llvm_float_mod_native --features llvm`): with the fix, `test result: ok. 1 passed; 0 failed`.
  Without the fix (`instructions.rs` from `origin/release/1.0.0`), it reproduces the defect:
  `llvm codegen: semantic: Unsupported float binop: Mod`, `test result: FAILED`.
- The fixture also passes on the Phase 1 interpreter (`run`).

## Related defect (open, not fixed here)

f32 on the seed LLVM/core-C lane is broken independently of `%`. In the same native fixture,
`fn f32_add(a: f32, b: f32) -> f32: a + b` called as `f32_add(5.5f32, 2.0f32)` returned `0.0`,
and an f32 `%` result printed as an integer (`17587646354272`). f32 was therefore removed from
this fixture. It needs its own record and spec.

## Unblock condition

Rebuild the seed with this fix. Re-run `check-simple-core-runtime-smoke.shs` with it, then the
essential-apps queue with `SIMPLE_SIMPLE_CORE_PATH=<archive>`.
