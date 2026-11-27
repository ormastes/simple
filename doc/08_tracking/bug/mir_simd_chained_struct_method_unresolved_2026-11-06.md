# mir_simd_chained_struct_method_unresolved_2026-11-06

Status: fix-implemented-verification-pending (P2). Fixed by #7107 (`afcd87b7409`).

## Symptom
Stage3 native build of module `lib.nogc_sync_mut.simd` (ML-KEM NTT SIMD path)
fails with 8 `unresolved method call` errors.

## The 8 calls
All `.to_array()` on a free-call result of a same-module SIMD struct:
`src/lib/nogc_sync_mut/simd.spl` lines 799, 800, 846, 848, 902, 903, 950, 952
(`simd_add_i32x8 / simd_sub_i32x8 / simd_mul_i32x8 / simd_add_i32x4 /
simd_sub_i32x4 / simd_mul_i32x4 (...).to_array()` on `Vec8i` / `Vec4i`).
They are the module's only same-module struct *instance* calls; the other
calls (`splat` static, `push`/`len`/`to_i32`/`to_i64` builtins) resolve.

## Root cause
`receiver_declared_or_result_type` (method_calls_literals.spl ~2176) does give
call receivers their declared Named return type, so dispatch reaches the
`struct_method_key_present_v1` branch, which read
`self.struct_method_syms[k].id` in one expression. Stage3 miscompiles that
struct-valued dict bracket-read + field read, so every same-module instance
call fell to "unresolved method call ... struct_method_syms=yes". #7107 binds
the SymbolId to a typed local first. `s3_fable46.exe` (2026-11-05 21:23)
predates #7107 (2026-11-06 10:44).

## Repro
```
s3.exe native-build --entry-closure --entry <probe using std.nogc_sync_mut.simd> \
  --source src/lib --runtime-bundle core-c-bootstrap --target x86_64-pc-windows-gnu \
  --backend llvm --keep-going --go-to-end -o out.exe
```
On this lane's tree, a copy of s3_fable46 SEGVs (rc=139) after HIR even on the
hello canary, so the run is pipeline-broken; diagnosis is from source.

## Tests
`test/01_unit/compiler/50.mir/mir_chained_text_methods_spec.spl` — free-call,
nested-call and static-call result receivers (+ builtin text sibling cases).
Verify: native-build the simd probe on a stage3 built at or after #7107.
