# SimpleOS focused compiler target closure remains overbroad

## Evidence

The final bounded target build used the zero-weak pure-Simple stage2 compiler,
`src/app/simpleos_tool/main.spl`, Cranelift, strict entry closure, and the real
Simple-core archive. It reached LLD, retained objects at `/tmp/.tmp0hcW9T`, and
failed with 397 external missing symbols after subtracting definitions from all
objects and the runtime archive.

The first failures are real filesystem/process ABI gaps (`rt_dir_create`,
`rt_file_read_bytes`, `rt_file_write_bytes`, `rt_file_write_text_at`,
`rt_file_copy`, `rt_getpid`). The remaining set also contains unreachable
backend families (Cranelift SFFI, CUDA, JIT, SQLite, broad CLI hooks) because
`compiler.driver.driver` imports `driver_pipeline`, `driver_aot_output`, and the
generic backend selector into module-granularity objects. Cranelift does not
emit independently discardable sections for all of those functions, so LLD
cannot discard the unused references before symbol resolution.

## Required fix

Cranelift's `ObjectBuilder` defaulted to one `.text` and one data section per
module. Enable its existing per-function/per-data-object sections so the strict
LLD `--gc-sections` pass can discard unreachable backend families without
ignoring unresolved symbols. This minimal compiler fix is implemented with a
focused object-section regression; its test build was twice interrupted by
external filesystem state (disk exhaustion, then concurrent target deletion)
before the test executable ran.

After rebuilding the pure compiler in a fresh session, recount the remaining
strict closure. Do not satisfy it with weak or zero stubs. The reviewed hot-path
list has 32 real Simple-core gaps; it also exposed two correctness defects that
must precede live compiler proof: dictionaries currently alias arrays and cannot
accept text keys, and `rt_enum_check_discriminant` returns true unconditionally.
If section GC does not remove the generic families, extract the strict
single-file frontend/MIR/LLVM runner described in the SPipe state instead of
adding optional backend ABI.

## Completed prerequisites

- Static guest `clang`, `llc`, and `lld` have `_start` and zero undefined symbols.
- The focused tool invokes `llc` directly on SimpleOS and uses mounted sysroot paths.
- The FAT producer stages the real tools, CRT, runtime, libc, linker script, and source.
- The production FAT/NVMe ring-3 loader remains the launch path; no SMF compatibility
  loader is accepted.

## 2026-07-11 focused-dispatch follow-up

The Cranelift section regression passed and a fresh zero-stub stage2 compiler
(`372deb53d7e98f5b7b9f77bc0bfc2e49e3780c82ddd1677200bf3fefe30c1f2f`)
self-hosted stage3 successfully. Object relocation review then proved that the
remaining optional backends were retained by live runtime dispatcher branches,
not by section coalescing.

`src/app/simpleos_tool` now bypasses `CompilerDriver` and uses a concrete
standalone parse/HIR/MIR/LLVM pipeline plus the concrete interpreter. The final
strict target link reduced the prior 397/500-symbol failure to 15 symbols and
kept objects at `/tmp/.tmpffD0yH`. Remaining owners are frontend debug mode,
interpreter GPU/value conversion, sugar/LLD dynamic bridges, and option panic.

No target ELF was produced. The three-cycle cap was reached, so these symbols
were not stubbed and the target build was not retried.

## 2026-07-11 target ELF and live filesystem follow-up

The final 15-symbol closure was repaired at owner boundaries and a strict fresh
build produced a real static target ELF (SHA-256
`10d52ba87e706cc424fa450e87a93645d2164ed45299e2155fbb6d2906b6f3a9`). QEMU
then resolved `/USR/BIN/SIMPLE` from the canonical FAT image, streamed its ELF,
passed two arguments, and entered ring 3.

The live gate found two later startup/runtime defects. CRT0 now rejects an
undefined or reversed weak `__bss_end`, preventing an unbounded BSS clear. The
next run reached `--version` and exited zero, but lacked a standalone user heap.
Adding the existing 64 MiB heap contract exhausted production PMM/page mappings
at page 5065. This was the third capped retry, so REQ-005 remains blocked on a
production-compatible heap size or demand-mapped allocator; no further QEMU run
was made.

### Heap failure root correction

Parallel PMM/VMM/heap audits mapped the failure exactly: stale reservation end
`0x14000000` caused heap allocation `0x15750000` to zero the page containing
`g_pmm` and `g_vmm`; the current kernel actually ends at `0x16f51000`. The
production entry now passes existing linker-derived start/end accessors to PMM
and uses the QEMU default 512 MiB physical bound. The 64 MiB user heap fits the
remaining range, so demand paging is unnecessary for this blocker.

The source-contract regression is present. Its pure-stage2 interpreter run was
stopped after 90 seconds without output; the QEMU gate was not repeated after
the prior three-run cap.

### Version argv follow-up

A fresh three-run cycle verified correct PMM bounds and the entire 64 MiB heap,
PT_LOAD, stack, and ring-3 entry path. The first run exposed tagged values from
the C linker-boundary helpers; those shared helpers now return raw addresses.
The next runs exposed a separate argument-state issue: Cranelift emitted
SimpleCore's mutable module-global setter as a no-op and hardcoded argc zero.

The two argument slots now use existing SimpleOS libc static storage through a
narrow owner boundary. A strict target rebuild passes (616 modules, zero
failures), and disassembly proves `rt_set_args` stores through the C owner while
`rt_cli_get_args` reloads argc/argv. New ELF SHA-256 is
`7859f1522e587765409dd8655b572ac76a392f8b609cde8cdae0ed1a3bb61b98`.
The three-run cap prevents another QEMU claim this cycle.
