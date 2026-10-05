# ARM/RVV bitmap provider execution

Scope: first real optional foreign-ISA implementation of SimpleVectorKernelsV1 bitmap AND/OR. Not full vector, compiler, DB, webserver, or hardware-performance qualification. Base release4f55e429c1d76119c5e028a50819267147482022; isolated branch work/item5-arm-rvv-20261005.

The canonical C header fixes the existing Simple draft's64-byte request/24-byte response layout, SIMDKER1 identifier, opcodes/statuses and span rules. Its ABI digest is SHA256 of the literal SIMPLE_VECTOR_ABI_DESCRIPTION without terminating NUL/newline: f16901349e16de8bb16f0769f492488fff27d0d0bd3b5f15c20b20b25f060600. Query metadata uses distinct provider-name SHA256 and implementation-source SHA256 prefixes, with full hashes retained beside artifacts; no fixture0x11 digest. Full artifact digests remain the loader's admission authority.

Baseline bitmap_provider.c validates query, requested capability ceiling, sizes/alignment/ranges/nonoverlap, then checks Linux runtime HWCAP before calling the separate ISA translation unit. Only capabilities1|2 are offered. Missing RVV produces FEATURE_UNAVAILABLE with zero output writes. NEON handles four words per vector iteration and scalar tails. RVV uses actual VL for each e32,m1 iteration. No target vector code is in the baseline query/guard TU; no LTO crosses that boundary.

## Actual evidence

Clang23.1.3 cross-compiled both shared objects and native C harnesses with installed GNU target libc/link dependencies; no GCC compilation and no Rust/Simple producer substitution. QEMU10.2.1 executed:

| Row | CPU | Assertions | Executed vector iterations | Peak RSS KiB | Result |
|---|---|---:|---:|---:|---|
| AArch64 NEON | max |70357|3592|8356|PASS|
| RVV128 | rva23u64,vlen=128,elen=64 |70357|3636|8520|PASS|
| RVV256 | rva23u64,vlen=256,elen=64 |70357|1832|8372|PASS|
| no V | max,v=false |70357|0|8192|PASS: unavailable, output unchanged|

Same RISC-V binaries were used for all three final rows. Each process had a60s watchdog,524288KiB enforced cap, exit0 and quiescent1. Constructor side effect was0 before dlopen and1 afterward through repeated query/calls. The script enables SIMPLE_VECTOR_TEST_OBSERVER: these retained DSOs intentionally depend on the harness-exported observer and are diagnostic artifacts, not deployable production packages. Normal provider builds omit this define. Observing the iteration counter does not load the DSO. The native harness closes the library; full Simple session pin/lifetime enforcement belongs to the separate loader integration and is not certified here.

The harness covers both opcodes for17 word lengths0..1025, two4-byte-aligned pointer offsets, independent scalar results, output canaries, high-bit/all-bit patterns, exact/partial overlap rejection, capacity/alignment/address failures, malformed size, unknown opcode and denied query/opcode capabilities. Positive vector counters plus retained actual ISA disassembly distinguish execution from scalar-only parity. NEON object contains vector ldr/and/orr/str; RVV object contains vsetvli/vle32/vand/vor/vse32. Emulation is not physical hardware speed evidence.

Durable WSL evidence: `/var/tmp/item5-arm-rvv-20261005-attempt2/`. Final logs/receipts: `neon.*`, `rvv128-rva23.*`, `rvv256-rva23.*`, `no-v-max.*`. Per-target directories retain provider.so, selfcheck, provider.o, kernel.o, kernel.disasm, guard.disasm, artifacts.sha256, provider.sha256, implementation.sha256. Root source inventory is source.sha256.

Provider artifact SHA256:

- AArch64:275ce6926c53c67b5c012b5b1a35873fc277de0f8a5f1dfbe60b2dd36e031de9
- RISC-V:d00772b211d6cc70ff9b6cc3ef124a65b2e6369c93f3dfc127f9bfcbe308796f

Initial prerequisite failures remain visible. Attempt1 stopped at missing target libc headers before tests; installed libc6-dev-arm64-cross/libc6-dev-riscv64-cross2.43-2ubuntu2cross1 plus target Linux headers. Attempt2 initially used default rv64 CPUs: all RV rows exited132 before harness output. Target CRT objects advertise RVA23 instructions; selecting compatible rva23u64/max CPUs corrected the environment without changing binaries. No-V successfully ran with max,v=false, so the earlier hypothesis that this sysroot necessarily prevented no-V testing was disproved. NEON was not rerun.

Reproduction entry: `sh scripts/check/check-vector-bitmap-targets.shs /var/tmp/NEW_FRESH_OUTPUT`. Script now records compiler commands in build.log, package versions, hashes and bounded receipts, and selects the successful CPU profiles. These orchestration-only logging/CPU-default edits were syntax-checked after the actual runs; unchanged native binaries were not rerun. Original continuation commands are retained under `D:/dev/simple/build/review/item5-rvv-rva23-continuation.shs`.

## Remaining acceptance

Review identified two bounded harness gaps: it does not snapshot and assert preservation of the left/right input buffers, and it does not assert the bitmap response's `scalar_result == -1` sentinel. Output parity and canaries do not independently prove either property. Add those assertions in a subsequent harness verification cycle before claiming complete request/response contract coverage.

The retained constructor-observer artifact hashes qualify these diagnostic kernel/guard executions only. They do not qualify a constructor-free production package, production demand-load behavior, or the Simple loader's session lifetime contract. The cross-target runner is a documented manual guard in `scripts/check/guard_wiring_optout.txt`; ordinary hosted CI lacks its cross-toolchain/sysroot/QEMU prerequisites.

Root-owned Simple wire/session draft must consume the canonical digest and pass actual Phase2 native loader tests. Production packaging needs complete artifact/source authority and a constructor-free test configuration; real Simple cross-target binaries must execute the providers. Auto-vectorization/compiler lowering, real DB/live HTTP selection, default image size/load policy, CUDA and hardware performance remain separate uncompleted rows. These four C/QEMU rows do not mark item5 or the full bootstrap goal complete.
