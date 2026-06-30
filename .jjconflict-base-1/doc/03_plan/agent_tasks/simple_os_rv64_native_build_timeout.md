# SimpleOS RV64 Native Build Handoff

## Current State

- RV64 native-build reaches LLVM IR emission for
  `src/os/kernel/arch/riscv64/boot.spl`; it no longer stops in MIR lowering,
  MIR optimization, backend helper arity dispatch, or missing
  `MirToLlvm.translate_instruction`.
- The current build still does not produce a fresh ELF. Existing artifact:
  `build/os/simpleos_riscv64.elf`, mtime `2026-06-15 10:14:53`, size `293680`.
- Temporary `bin/simple` symlink cleanup is working; latest post-run check:
  `bin_simple_absent=1`.
- Last bounded build log is `build/os/native_rv64_last.log`.

## Latest Evidence

Last bounded build command:

```sh
SIMPLE_NATIVE_BUILD_ENTRY=src/os/kernel/arch/riscv64/boot.spl timeout 300 \
  src/compiler_rust/target/release/simple run src/app/cli/native_build_worker.spl --verbose \
  --source build/os/generated --source src --source examples \
  --backend llvm --opt-level=aggressive --log on --entry-closure \
  --entry src/os/kernel/arch/riscv64/boot.spl \
  --target riscv64-unknown-none \
  -o build/os/simpleos_riscv64.elf \
  --linker-script src/os/kernel/arch/riscv64/linker.ld
```

Latest failure:

```text
[driver-mir] bootstrap lower:start
[driver-mir] bootstrap lower:done
error: AOT compile error in os.kernel.arch.riscv64.boot:
llc-18: /tmp/simple_llvm_1978471.ll:6:23: error: expected type
define i64 @boot_main(nil %l1, nil %l2) nounwind {
                      ^
```

Generated IR is now less broken than before:

- Parameter names are real MIR locals (`%l1`, `%l2`) instead of `%arg0`.
- Branch labels are raw block ids (`%bb1`) instead of `%bbBlockId(id: 1)`.
- Operand locals are raw locals (`%l24`) instead of `%lLocalId(id: 24)`.

Remaining issue:

- LLVM parameter and call result types still emit as `nil`.
- Adding unsigned integer handling to `LlvmTypeMapper` did not change this, so
  the active `nil` source is upstream of, or bypassing, that mapper.
- Function call names still emit as `@unknown_*`, so function-symbol operand
  lowering is also incomplete on this text LLVM path.

## Fixes Landed In This Lane

- Rust interpreter fallback now handles bare Option/Result payload methods in
  object/class miss paths, clearing `method unwrap not found on type Type`.
- Rust primitive bool method handling now supports `bool.is_public()`.
- `SymbolTable.define`/`get` no longer construct/index symbol ids through the
  broken path that produced nil `id.id`.
- Driver MIR bootstrap cache no longer stores the native boot entry as the
  hosted bootstrap entry.
- Four `MirModule(..module, functions: ...)` spread constructors were expanded
  to explicit field copies to avoid range-expression misparse.
- `CollectionOptimization.count_local_use` ignores nil locals before reading
  `local.id`.
- Cranelift and LLVM-lib free helper functions were prefixed to avoid global
  helper-name collisions with `MirToLlvm` method dispatch.
- `MirToLlvm` now has an explicit `translate_instruction` dispatch method.
- `MirToLlvm` core text generation now uses raw local/block ids for the active
  parameter, operand, and terminator paths.
- `LlvmTypeMapper` now maps `U8/U16/U32/U64` to signless LLVM integer widths and
  includes them in size/alignment.
- Temporary Rust diagnostics used for narrowing were removed.

## Next Step

Do not rerun the same build without new narrowing evidence.

Inspect why `MirToLlvm.get_local_type()` receives/stores `nil` for boot locals
despite `boot_main(hart_id: u64, dtb_addr: u64)`. Good next probes:

- Log or inspect `body.locals` and `local.type_.kind` inside
  `_MirToLlvm/core_codegen.spl::translate_function`.
- Confirm whether `self.type_mapper.map_type(local.type_)` is dispatched to
  `LlvmTypeMapper.map_type` or a trait/default mapper that still lacks unsigned
  support.
- Inspect function-symbol `MirOperand` lowering so calls stop emitting
  `@unknown_*`.

Keep the stale-ELF preflight blocking QEMU/WM checks until
`build/os/simpleos_riscv64.elf` is freshly produced.
