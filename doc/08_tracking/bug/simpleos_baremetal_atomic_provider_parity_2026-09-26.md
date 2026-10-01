# SimpleOS bare-metal atomic providers lack three-architecture parity

**Status:** Open release blocker; three-architecture source providers are candidates.

The x86 `rt_extras.c` runtime previously represented `rt_atomic_int_*` as a
boxed `int64_t` with plain reads, writes, compare-and-set, and fetch operations
under a “single-core” comment. An SMP kernel cannot use those operations as
an atomic owner. The candidate x86 repair preserves the typed i64 ABI and uses
the same freestanding slot owner as AArch64/RV64, with sequentially consistent
hardware atomics. Its bool family decodes codegen's tagged true/false values
and includes CAS, fetch-and, fetch-or, and fetch-not.

The AArch64 boot runtime and canonical RISC-V 64 boot runtime now include one
freestanding `src/runtime/startup/baremetal/atomic_runtime.inc.c` provider for
the complete typed integer/bool family. It uses raw i64 arguments as declared
by the Simple atomic SFFI and accepts tagged bool literals. The separate
`examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c`
constructor is an example route, not the canonical RISC-V product provider.
All three wrappers now consume one static 4096-slot owner. Handles carry a slot
and generation, never an unchecked heap pointer. Free revokes new operations;
in-flight leases drain before a slot can be reused, and the generation check
refuses stale handles after reuse. Invalid and exhausted handles fail closed.
Concurrent construction no longer enters the unsynchronized boot bump
allocator. The 4096 limit is simultaneous live/draining cells rather than a
lifetime allocation limit; a selected capacity target is still needed. Host
contention, concurrent construction, invalid/stale handle, reuse/ABA,
capacity, and raw-8/tagged-bool fixtures passed. AArch64, RV64, and x86
target assembly emitted hardware atomic instructions. A previous AArch64 full
boot C file cross-compiled before this owner refactor; no source-matched full
boot/link receipt exists for the current source. Standalone compilation of the
canonical RV64 C file previously hit unrelated declarations before target
emission.

The repeatable current focused gate is
`sh scripts/check/check-simpleos-atomic-slot-owner-v2.shs`.

Completion still requires linked provider identity, a selected simultaneous
capacity target, whole-runtime allocator safety after SMP bring-up, and guest
contention tests on x86_64, AArch64, and RISC-V 64. The guest test must
exercise the Simple `AtomicI64` call route rather than only a C helper.
