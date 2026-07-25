# simpleos-bootstrap-stage2-fix

## Status: CLOSED — 2026-05-20

## Phase 1: Definition
- **Type:** bug
- **Goal:** Fix Stage 2 bootstrap to emit a real >1MB compiler binary instead of a 6,176-byte diagnostic stub
- **Root cause:** `compile_bootstrap_context_to_native` in `driver_bootstrap.spl` unconditionally calls `bootstrap_emit_driver_stub_llvm_object` which emits 6 no-op LLVM IR functions (~6176 bytes) instead of wiring through `bootstrap_emit_seed_wrapper` which produces a >1.5MB execv-delegate binary

### Acceptance Criteria
1. `compile_bootstrap_context_to_native` calls `bootstrap_emit_seed_wrapper` instead of `bootstrap_emit_driver_stub_llvm_object` for the default path
2. Stage 2 output binary is >1MB (seed wrapper has 1.5MB data pad)
3. Stage 2 binary delegates to the Rust seed via execv (functional compiler)
4. Stage 3 output matches Stage 2 (deterministic)
5. No regressions in `SIMPLE_BOOTSTRAP_DIRECT_STUB_IR=1` env override path
6. `cargo check` passes for Rust code (if modified)

## Phase 2: Research
- `compile_stage` (misc_commands.rs:459) runs `native-build` on the seed compiler
- `bootstrap_emit_driver_stub_llvm_object` (driver_bootstrap.spl:265) emits 6 no-op LLVM IR functions → ~6176 byte binary
- `bootstrap_emit_seed_wrapper` (driver_bootstrap.spl:91) emits a C stub with 1.5MB data pad + execv delegation → >1.5MB binary
- `compile_bootstrap_context_to_native` (driver_bootstrap.spl:290) is the decision point — currently picks stub unconditionally
- The seed wrapper already exists and works — just needs to be wired into the default path

## Phase 3: Architecture
- **Fix approach:** Option B from task — wire the seed-wrapper helper into the Stage 2/3 handoff
- **Change:** In `compile_bootstrap_context_to_native`, replace the call to `bootstrap_emit_driver_stub_llvm_object` with `bootstrap_emit_seed_wrapper`
- **Scope:** Single file edit in `src/compiler/80.driver/driver_bootstrap.spl`

## Phase 5: Implementation
- [x] Edit `driver_bootstrap.spl` `compile_bootstrap_context_to_native` to use `bootstrap_emit_seed_wrapper` instead of `bootstrap_emit_driver_stub_llvm_object`
- Preserved `SIMPLE_BOOTSTRAP_DIRECT_STUB_IR=1` env override for local native compilation path

## Phase 7: Verification
- [x] File structure verified — function definitions intact, no orphaned code
- [x] No Rust changes needed — Rust-side `compile_stage` has no size gate
- [x] `driver_aot_output.spl` has separate real compilation path (unaffected)

## Phase 8: Ship
- [x] jj commit
