# SimpleOS ELF32 C-provider preparation

This is preparation evidence for the six-CPU lint/test goal. It does not certify
the complete runtime, either linker, a compiler phase, or any guest execution.
No SDK builder or provider source was changed by this lane.

## Retained campaign

`build/verify/simpleos-32-provider-20261123/` contains exact commands, input and
tool SHA-256 hashes, stderr, ELF headers, symbol lists, and deterministic provider
archives. `prepare.py` is a diagnostic capture script under the ignored build
directory, not a production builder. The provider source and header inputs were
unchanged across compilation.

| Target | Provider C files | ILP32 assertions | Strong duplicates | Archive imports after provider definitions | After actual libc C definitions |
|---|---:|---|---:|---:|---:|
| i686 | 12/12 compiled | PASS | 0 | 188 | 30 |
| arm32 | 11/11 compiled | PASS | 0 | 204 | 46 |
| riscv32 | 11/11 compiled | PASS | 0 | 215 | 57 |

Each successful provider object is little-endian ELF32 with the exact machine:
i386 (3), ARM (40), or RISC-V (243). Pointer, `uintptr_t`, `size_t`, `int`, and
`long` are 32 bits; `int64_t` is 64 bits. This checks the C data model, not the
full generated-Simple ABI or struct calling convention.

The separate libc dependency census compiled the current 32-bit recipe's 39 C
files for each target (117/117). It did not execute or qualify the SDK builder,
assemble CRT/syscall objects, link a user program, or inspect its live closure.
The recipe and libc source hashes remained unchanged during this census.

The first symbol analysis accidentally treated weak definitions as unresolved
when computing imports. The corrected analysis uses retained `llvm-nm` output;
it did not recompile green files. Five weak definitions resolve three array-byte
helpers and two heap counters. Strong-duplicate counts remain zero. The original
inventories and `weak-definition-census-correction.sdn` are retained.

## Composition and ABI flags

The shared sources are `src/runtime/{runtime_native,runtime_simd_utf8,
runtime_contracts,runtime_memory,runtime_time,runtime_timestamp,runtime_pool,
runtime_memtrack,runtime_legacy_core,runtime_simpleos_syscall_adapters}.c` and
`src/runtime/startup/baremetal/runtime_log.c`. Only i686 adds
`startup/baremetal/runtime_port_io.c`: its actual x86 branch serves COM1 logging.
ARM/RISC-V use the logging source's architecture-specific MMIO branches.

Target flags match the existing 32-bit libc recipe:

- i686: `--target=i686-unknown-none-elf -march=i686`.
- arm32: `--target=armv7a-none-eabi -marm -mfloat-abi=soft`.
- riscv32: `--target=riscv32-unknown-elf -march=rv32imac -mabi=ilp32 -mno-relax`.

All use `-fno-pic`, freestanding/no-stdlib/no-builtin flags, no stack protector,
exceptions or unwind tables, function/data sections, and `-O2`. Runtime provider
flags additionally use `-nostdlibinc`, the SimpleOS libc include directory,
`__simpleos__=1`, `SIMPLE_RUNTIME_MEMORY_OWNER=1`, and
`SIMPLE_RUNTIME_TIME_OWNER=1`. Full expanded argument arrays are retained beside
each object; they are authoritative over this summary.

## Remaining ownership and linkage work

Archive import counts are inventories, not observed tool link errors. Section GC
can discard unused routines. Actual lint/test roots and their surviving
relocations must decide which imports need providers.

The post-libc inventories include these compiler ABI families:

- i686: signed/unsigned 64-bit division and remainder.
- arm32 soft-float: AEABI double operations/conversions, integer division,
  `__aeabi_memclr8`, and `__clear_cache`.
- riscv32 soft-float: double operations/conversions, 64-bit division/remainder,
  64-bit atomics, `__atomic_is_lock_free`, and `__clear_cache`.

The installed LLVM provider contains only a Windows x86_64 builtins archive; it
is incompatible with all three targets. Existing owned build orchestration is
`src/os/port/llvm/build.shs` (`stage3_compiler_rt`) and
`src/os/port/llvm/compiler_rt_cmake.cmake`. It builds standard LLVM compiler-rt
builtins for the selected triple and stages them under the Clang resource
directory. The default checked local LLVM-source paths were absent. The native
SimpleOS link route in `src/compiler/70.backend/backend/simpleos_native_linkers.spl`
passes explicit archives to both engines and does not currently add a
target-selected compiler-rt archive. Merely installing it in a Clang resource
directory therefore does not repair that direct-link route.

The minimum recipe change is to build/obtain a pinned, exact-target compiler-rt
archive; verify all selected members' ELF class/machine and ABI; include it in
both engines' archive group with actual digest/member provenance; and verify the
surviving undefined set from the real tool roots. Do not use host libgcc, add
an unchecked library after SDK receipt generation, or allow a native-linker
fallback to count as the Simple engine.

RV32 emits 8-byte atomic helper calls because its 32-bit atomic ISA cannot make
those operations lock-free. LLVM's standard `compiler-rt/lib/builtins/atomic.c`
provides a real lock-based fallback using lock-free pointer-sized compare/exchange
when a platform lock implementation is not selected. This is an available
implementation direction, not validated SimpleOS support. Pin the actual source,
include the atomic builtins, prove 32-bit atomics and scheduler/interrupt
compatibility, inspect helper recursion, and execute tests before admission.
Neither ordinary loads/stores nor a claimed single CPU substitutes for atomic
semantics. [LLVM atomic implementation](https://github.com/llvm/llvm-project/blob/main/compiler-rt/lib/builtins/atomic.c)

`__clear_cache` has actual existing architecture owners in the 64-bit syscall
assembly, but not in the inspected 32-bit syscall assembly. ARM instruction-cache
maintenance needs a real user/kernel cache-sync contract; RV32 requires its
architecture/privilege-correct cache synchronization. An empty stub would not
establish executable-code visibility.

Ten `rt_*` names remain in each unrooted provider census: six process APIs and
four SIMD feature queries. The existing `simple_core/core_process.spl` exports
`rt_process_wait`; `runtime_process.c`, `runtime_process_tree.c`, and
`runtime_process_owned.c` contain the other process owners but are not selected
by this C-provider composition. `runtime_simd_dispatch.c` contains the SIMD
queries and is also not selected. These must be reviewed against the live tool
closure and target support; the presence of a hosted C definition alone does not
qualify it for SimpleOS. Most other remaining names are libc/network/format
helpers. The 39-file census excludes `simpleos_netdb.c`, for example, so a
definition there is not proof that the current archive supplies it.

When the 32-bit SDK builder adopts runtime providers, its input-capture policy
must expand beyond libc/CRT to the actual architecture-owned source/header list,
expanded flags, and archive members. Existing libc-only receipts cannot qualify
these newly prepared provider archives. The 20-part pure-Simple runtime also
still requires a real compiler build and link evidence.
