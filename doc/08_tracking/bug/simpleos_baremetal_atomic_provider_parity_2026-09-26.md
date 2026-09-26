# SimpleOS bare-metal atomic providers lack three-architecture parity

**Status:** Open release blocker; three-architecture source providers are candidates.

The x86 `rt_extras.c` runtime previously represented `rt_atomic_int_*` as a
boxed `int64_t` with plain reads, writes, compare-and-set, and fetch operations
under a “single-core” comment. An SMP kernel cannot use those operations as
an atomic owner. The candidate x86 repair preserves the handle ABI and uses
freestanding `__atomic_*` operations with sequential consistency. A host
contention test and x86 cross-compile/disassembly cover the source primitive;
an SMP guest test is still required. The x86 bool family now decodes codegen's
tagged true/false values and includes CAS, fetch-and, fetch-or, and fetch-not.

The AArch64 boot runtime and canonical RISC-V 64 boot runtime now include one
freestanding `src/runtime/startup/baremetal/atomic_runtime.inc.c` provider for
the complete typed integer/bool family. It uses raw i64 arguments as declared
by the Simple atomic SFFI and accepts tagged bool literals. The separate
`examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c`
constructor is an example route, not the canonical RISC-V product provider.
Host contention and raw-8/tagged-bool tests passed for the shared provider;
AArch64 and RV64 objects emitted hardware atomic instructions. The AArch64
full boot C file cross-compiled. Standalone compilation of the canonical RV64
C file hit unrelated existing declarations before target emission, so this
change has no source-matched full RV64 build or linked-symbol receipt.

Repeatable focused gates are
`sh scripts/check/check-simpleos-x86-baremetal-atomics.shs` and
`sh scripts/check/check-simpleos-multiplatform-atomic-provider.shs`.

Completion still requires linked provider identity, explicit handle lifecycle
and invalid-handle behavior, allocator safety after SMP bring-up, and guest
contention tests on x86_64, AArch64, and RISC-V 64. The guest test must
exercise the Simple `AtomicI64` call route rather than only a C helper.
