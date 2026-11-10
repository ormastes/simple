# LlvmBackend.compile_module() fails on any module: duplicate `rt_eprintln` declaration
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: FIXED (verified 2026-11-11, lane rt3) — the duplicate
  `declare void @rt_eprintln(ptr)` was dropped from
  `generate_wasm_runtime_declarations` by `9566e7565aa5` (2026-11-06); the
  regression spec passes 4/4 on the fresh seed. See the 2026-11-11 addendum.
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


---

## 2026-11-11 — Lane rt3 triage verdict: FIXED

**Fixing change:** `9566e7565aa5` (2026-11-06, "fix(llvm): drop duplicate
rt_eprintln wasm runtime declaration") removed the second
`declare void @rt_eprintln(ptr)` from
`generate_wasm_runtime_declarations()` in
`src/compiler/70.backend/backend/llvm_backend_tools.spl`, and added the
regression spec `test/01_unit/compiler/backend/llvm_runtime_decls_unique_spec.spl`
which scans every declaration generator in both backend files and asserts each
`@rt_*` symbol is declared at most once per generator. The fix is an ancestor
of the current base.

**History:** this row was briefly closed by the 2026-11-09 wave4 stale-close
(`dc4733c1942b`), then reverted to `fix-implemented-verification-pending` by
`31449a6b6afc`; the verification below is the pending confirmation.

**Verification (seed-smoke, seed build 46fe8f6b6def):**
- `test/01_unit/compiler/backend/llvm_runtime_decls_unique_spec.spl` 4/4 PASS
  (both `llvm_backend.spl` and `llvm_backend_tools.spl` declare each runtime
  symbol at most once per generator).
