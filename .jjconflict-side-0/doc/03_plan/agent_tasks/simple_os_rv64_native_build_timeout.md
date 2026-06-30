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

Latest failure after the local-map and MIR-local metadata fixes:

```text
[driver-mir] bootstrap lower:start
[driver-mir] bootstrap lower:done
error: AOT compile error in os.kernel.arch.riscv64.boot:
llc-18: /tmp/simple_llvm_2147735.ll:27:36: error: '%l15' defined with type 'i1' but expected 'i64'
  %l16 = call i64 @unknown_nil(i64 %l15)
                                   ^
```

Generated IR is now less broken than before:

- Parameter names are real MIR locals (`%l1`, `%l2`) instead of `%arg0`.
- Branch labels are raw block ids (`%bb1`) instead of `%bbBlockId(id: 1)`.
- Operand locals are raw locals (`%l24`) instead of `%lLocalId(id: 24)`.
- LLVM function parameter, call-result, call-argument, and return types no
  longer emit `nil`; they are normalized to native integer fallbacks where MIR
  type data is missing.
- `_uart_put(byte: u64)` now references its real argument local instead of the
  undefined `%l2`.
- `_start` no longer fails on `ret i64 %l1`; bootstrap MIR locals are retained
  in `MirBuilder.new_local`, and `MirToLlvm` treats synthetic return locals as a
  default return value when they reach a terminator.

Remaining issue:

- `boot_main` emits a bool const as `i1` (`%l15`) but the call path still passes
  it as `i64` to `@unknown_nil`, so `llc` rejects the IR.
- Function call names still emit as `@unknown_*`, so function-symbol operand
  lowering is incomplete on this text LLVM path.
- Later `boot_main` IR still contains memory/condition types as `nil`
  (`alloca nil`, `store nil`, `icmp ne nil`); `llc` currently stops before
  those.

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
- `MirToLlvm` now has local native-int fallbacks for missing primitive/local
  operand types at emitted parameter, call, and return boundaries.
- `MirLowering.local_map` now keys by raw symbol id so equivalent `SymbolId`
  values resolve the same parameter/local.
- `MirBuilder.new_local` now records locals even in `SIMPLE_BOOTSTRAP=1`, which
  preserves `LocalKind.Arg`/`Return` metadata for the LLVM text backend.
- `MirToLlvm.translate_const` now updates `local_types` to the type it actually
  emits; the remaining bool mismatch shows another call-typing path still
  forces native-int.
- Temporary Rust diagnostics used for narrowing were removed.

## Next Step

Do not rerun the same build without new narrowing evidence.

Inspect why the call argument printer still emits `i64 %l15` even though
`translate_const` emits `%l15 = add i1 1, 0`. Good next probes:

- Inspect `translate_call` and any callee-signature or unknown-call fallback path
  that can override `get_operand_type(arg)`.
- If no callee signature is available, use the operand's actual type for call
  arguments and insert an explicit cast only when a known callee requires it.
- Inspect function-symbol `MirOperand` lowering so calls stop emitting
  `@unknown_*`.
- After the bool mismatch is fixed, continue with the remaining `alloca nil` /
  `icmp ne nil` type sites in `boot_main`.

Keep the stale-ELF preflight blocking QEMU/WM checks until
`build/os/simpleos_riscv64.elf` is freshly produced.
