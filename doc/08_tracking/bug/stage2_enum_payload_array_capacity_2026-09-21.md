# Stage 2 multi-field enum payload allocation uses an uninitialized capacity

Date: 2026-09-21. Source base: PR #1259 head `21407c7f41509264143368e894348d255aaedd9b`.
The preserved rejected Windows Stage 2 binary has SHA-256
`1e509d5797cd1051344ae2709f34b2ec04062ecfca05a54e7968fc9b6cd2dbbb`.
Its original source-input receipt records a dirty fingerprint, so the commit
alone is not a complete binary provenance claim.

## Reproducer and fault

The LLVM-backend positional `native-build` of
`scripts/check/cert/redeploy_gate/fixtures/hello_world.spl` reaches HIR and
access-violates at `simple.exe.rejected+0x1efa38` reading through `r13=0`.
The loaded LLVM-C.dll is
`C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc/bin/LLVM-C.dll`,
SHA-256 `1286e894afc98486963246a3f786459b63efb8bd3e4a00193530013fe46aa1fe`.
The dump is
`.simple/storage/build/diagnostics/stage2_hir_av/positional-llvm.dmp`;
the CDB transcript is `cdb-positional-llvm.log` in the same directory.

Preserved COFF object `a9773c81687f6cd3.o` maps that instruction to
`HirLowering.try_lower_host_gpu_lane_expr` reading the callee's `kind` after
`ExprKind.Call(callee, args)` extraction. The Call enum object's payload is
the nil sentinel `3`; `rt_enum_payload` also returns `3`. A live breakpoint
on `rt_enum_new` confirmed the Call constructor received `r8=3`.

Preserved COFF object `7561c3e04515a4fd.o` maps the constructor caller to
`convert_flat_expr` in `convert_nodes.spl`. Immediately before creating the
two-field Call enum payload, generated code invokes `rt_array_new` with a
stale pointer in the Windows first-argument register RCX. The runtime
requires `rt_array_new(int64_t cap)`; its declaration is `runtime.h:564`.
The impossible allocation warning during surface building has the same
cause: `parser_type_kind_array_discriminant` constructs a two-field
`TypeKind.Array` sample through the same omitted-capacity path.

## Cause and repair

`src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs` emitted
`MirInst::Call(rt_array_new, args: vec![])` for multi-field enum payloads.
The repair emits `ConstInt` for the field count and passes its register as
the sole argument. Conversion from `usize` to `i64` is checked; an
unrepresentable count returns a lowering error before allocation. Unit and
single-field enum constructors do not enter this branch. The positive count
has the same 64-bit representation for the C runtime's signed `i64` and the
Rust runtime's unsigned `u64` capacity parameters.

The focused MIR test for `Type.Int(bits: 64, signed: true)` failed before the
repair with `two-field enum payload must pass capacity 2 to rt_array_new` and
passed afterward (1 passed, 4077 filtered). It checks the capacity constant,
call argument, and that the allocated array is the `EnumWith` payload. The
GREEN test log is `.simple/storage/build/diagnostics/stage2_hir_av/green-mir-test.log`.

Linux uses the same MIR lowering and a one-argument `rt_array_new` ABI. With
the omitted argument, its capacity register is unspecified; the repair sets
the argument explicitly on every target. This is a source-level
cross-platform conclusion. A Linux binary run was not performed.

The patched Rust bootstrap producer built an isolated Windows Stage 2 compiler
with LLVM 23.1.1 `clang-cl`: 900 compiled, 0 cached, 0 failed. That compiler
then completed the positional LLVM `native-build` of the canonical
`hello_world.spl` fixture with exit code 0. Its HIR post-lowering error count
was 0; the generated executable exited 0 and printed `hello`. The build log,
positional log, and run output are respectively
`.simple/storage/build/diagnostics/stage2_hir_av/patched-stage2-build.log`,
`patched-positional.log`, and `patched-hello-run.log` in the same directory.
This checks the pure-Simple positional compiler path; explicit `--entry`
invocation routes through the Rust FFI and is not equivalent evidence.
