# SimpleOS bare-metal atomic providers lack three-architecture parity

**Status:** Open release blocker; x86 source correction is a candidate.

The x86 `rt_extras.c` runtime previously represented `rt_atomic_int_*` as a
boxed `int64_t` with plain reads, writes, compare-and-set, and fetch operations
under a “single-core” comment. An SMP kernel cannot use those operations as
an atomic owner. The candidate x86 repair preserves the handle ABI and uses
freestanding `__atomic_*` operations with sequential consistency. A host
contention test and x86 cross-compile/disassembly cover the source primitive;
an SMP guest test is still required.

The AArch64 freestanding runtime currently defines atomic integer creation,
load, and compare-exchange in
`examples/09_embedded/simple_os/arch/aarch64/boot/freestanding_runtime.c`,
but this source inspection found no complete store/swap/fetch/bool family at
that location. The RISC-V 64 bare-metal runtime core defines
`rt_atomic_int_new` in
`examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c`;
the remaining operations were not found under the architecture boot tree.
These are source-route findings, not linked-binary evidence of which weak
fallbacks or other providers are selected.

Completion requires one typed atomic contract and native owner per required
architecture, explicit handle lifecycle and invalid-handle behavior, emitted
hardware atomic evidence, and guest contention tests on x86_64, AArch64, and
RISC-V 64. The same test must exercise the Simple `AtomicI64` call route rather
than only a C helper.
