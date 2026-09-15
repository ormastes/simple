# LlvmBackend.compile_module() fails on any module: duplicate `rt_eprintln` declaration

- Status: OPEN (2026-09-13)
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed, `sha256sum` first 8:
  see `readlink -f bin/simple` in this worktree — shared with `/home/yoon/dev/simple`)
- Found while implementing todo 213 (`test/integration/compiler/llvm_backend_e2e_spec.spl:189`,
  "Create minimal MirModule and compile").

## Repro

```
use compiler.backend.llvm_backend.LlvmBackend
use compiler.backend.backend_types.{CodegenTarget, OptimizationLevel}
use compiler.mir.mir_data.MirModule

val backend = LlvmBackend.create(CodegenTarget.X86_64, OptimizationLevel.Debug)
val module = MirModule(name: "e2e_minimal", functions: {}, statics: {}, constants: {}, types: {})
val result = backend.compile_module(module)
result.unwrap()   # panics
```

`bin/simple test` on that spec produces:

```
semantic: called unwrap on Err: llc failed (exit 1):
llc: error: llc: /tmp/simple_llvm_3800900.ll:67:14: error: invalid redefinition of function 'rt_eprintln'
declare void @rt_eprintln(ptr)
             ^
```

i.e. `generate_runtime_declarations_for_target()` (called from
`LlvmBackend.compile_module`, `src/compiler/70.backend/backend/llvm_backend.spl`)
emits `declare void @rt_eprintln(ptr)` more than once in the generated LLVM IR
module, which `llc` rejects as an invalid redefinition. This happens for an
otherwise-empty MIR module (zero functions), so it reproduces unconditionally —
`compile_module()` cannot currently succeed on ANY input.

## Impact

- Blocks todo 213 (llvm_backend_e2e_spec.spl "compiles minimal LLVM IR to
  object code") from being implemented for real; the spec still only checks
  `LlvmBackend.create()` field defaults, not an actual compile.
- Consistent with the previously-filed
  `doc/08_tracking/bug/native_build_fails_on_hello_world_aarch64_2026-09-06.md`
  finding that native-build fails on trivial input — this looks like the same
  family of runtime-declaration generation bug, possibly the direct cause.

## Suggested fix location

`generate_runtime_declarations_for_target()` /
`generate_runtime_declarations()` in
`src/compiler/70.backend/backend/llvm_backend.spl` (and/or
`llvm_backend_tools.spl`) — de-duplicate declared runtime symbols before
emitting them into the IR text, or find where `rt_eprintln` is declared twice
in the template list.
