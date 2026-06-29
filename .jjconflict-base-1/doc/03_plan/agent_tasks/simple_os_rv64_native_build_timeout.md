# SimpleOS RV64 Native Build Handoff

## Current State

- RV64 native-build completes bootstrap MIR lowering for
  `src/os/kernel/arch/riscv64/boot.spl` and now fails after
  `[driver-mir] bootstrap lower:done`.
- Target plumbing now uses `SIMPLE_NATIVE_BUILD_TARGET` from native-build `--target`; `backend_helpers.spl` maps it to `CodegenTarget.Riscv64`.
- Text MIR-to-LLVM now normalizes block labels through `block_label`, so branches emit `%bb1` instead of `%bbBlockId(id: 1)`.
- Text MIR-to-LLVM now uses `local_id_value` in the core and active instruction split call paths.
- `LlvmTypeMapper.map_type` now falls back to the target native integer for missing MIR types instead of returning `nil`.
- Native-build entry closure again skips parent aggregate modules for brace imports (`use x.y.{A}`), avoiding the broad parse timeout path.

## Latest Evidence

Last bounded build command:

```sh
timeout 300 src/compiler_rust/target/release/simple run src/app/cli/native_build_worker.spl --verbose \
  --source build/os/generated --source src --source examples \
  --backend llvm --opt-level=aggressive --log on --entry-closure \
  --entry src/os/kernel/arch/riscv64/boot.spl \
  --target riscv64-unknown-none \
  -o build/os/simpleos_riscv64.elf \
  --linker-script src/os/kernel/arch/riscv64/linker.ld
```

Latest completed run after the MIR optimizer constructor and nil-use fixes now
gets past MIR lowering and optimization far enough to enter backend translation:

```text
[driver-mir] bootstrap lower:start
[driver-mir] bootstrap lower:done
error: semantic: function expects argument for parameter 'value_map', but none was provided
```

The existing `build/os/simpleos_riscv64.elf` is stale:

```text
-rwxrwxr-x ... build/os/simpleos_riscv64.elf 293680 Jun 15 10:14
```

The prior blockers are cleared:

- `method unwrap not found on type Type`: fixed by routing object/class miss
  paths through the existing bare-payload Option/Result fallback in
  `src/compiler_rust/compiler/src/interpreter_method/mod.rs`.
- `method is_public not found on type bool`: fixed by treating
  `bool.is_public()` as identity in
  `src/compiler_rust/compiler/src/interpreter_method/primitives.rs`, matching
  legacy visibility carriers that already store `is_public: bool`.
- `undefined field 'id'` in `SymbolTable.get(nil)`: fixed by returning `nil`
  before dereferencing `id.id` in `src/compiler/20.hir/hir_types.spl`.
- `type mismatch: cannot convert object to int` after MIR lower: traced to
  `MirModule(..module, functions: ...)` / `MirModule(..mir, functions: ...)`
  being evaluated as a range ending at `module`/`mir`; fixed by expanding those
  four constructors to explicit `name/functions/statics/constants/types` copies.
- `undefined field 'id'` in `CollectionOptimization.count_local_use`: fixed by
  ignoring nil locals before reading `local.id`.

The active scoped unwrap search is still clean:

Patched unwrap sites now include:

- `_MirToLlvm/core_codegen.spl`, `_MirToLlvm/aggregate_intrinsics.spl`,
  `_MirToLlvm/asm_constraints_helpers.spl`
- `mir_to_llvm_instructions.spl`
- `llvm_ir_builder.spl`, `llvm_lib_translate_expr.spl`,
  `llvm_cross_target.spl`, `llvm_codegen_adapter.spl`,
  `llvm_capability.spl`, `llvm_backend_tools.spl`, `llvm_backend.spl`,
  `llvm_target.spl`
- `build_native.spl`, `build_native_pipeline.spl`

Do not keep retrying the same build without new narrowing evidence.

Attempted narrowing that did not change the failure:

- Replaced `case SymbolId(id): id` helpers with direct `symbol.id` in
  `src/compiler/50.mir/_MirLowering/module_lowering.spl`,
  `src/compiler/50.mir/mir_json.spl`, and
  `src/compiler/60.mir_opt/mir_opt/_Inline/driver.spl`.
- Re-ran the same bounded build; it still failed at the identical
  `receiver expr: Identifier("id")`, so the executed expression is not one of
  those remaining helper destructures. Search found no generated stale copy
  under `build/os/generated` or `build`.
- Added temporary field-access diagnostic context in
  `src/compiler_rust/compiler/src/interpreter/expr/calls.rs`; it proved the
  nil-id owner was `SymbolTable` with `env keys: [self, id]`.

## Next Step

Fix the backend translation arity failure:

```text
error: semantic: function expects argument for parameter 'value_map', but none was provided
```

The narrow search points at LLVM translation helpers in
`src/compiler/70.backend/backend/llvm_lib_translate_expr.spl`, where
`translate_instruction` and `translate_terminator` both require `value_map`.
Likely next useful move is to add a temporary call-site diagnostic in Rust
function argument binding or inspect backend helper overloads around
`translate_call`/`translate_terminator` to find the call missing that parameter.
Keep the stale-ELF preflight blocking until `build/os/simpleos_riscv64.elf` is
freshly produced.
