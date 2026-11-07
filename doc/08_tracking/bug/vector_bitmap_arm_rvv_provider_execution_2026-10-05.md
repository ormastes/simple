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

## Current provider identity rerun, 2026-11-07

Source `205e53cf6571b371fb66631dd59abcb422ee4b26`, merged as `41d9151614adbaadb098b871894537e90593a70f`. This additive evidence preserves all historical findings and remaining acceptance gaps above. The current provider implementation identity includes the directly consumed `text_kernel_private.h`; source implementation and target flags were unchanged.

The canonical bitmap source/build steps succeeded. The first target-launch phase failed with exit 89 and `root_pid=0`: private sparse materialization omitted `scripts/bootstrap/bootstrap-session-exec.c`, required by the watchdog. This was an orchestration dependency failure before any target ran. Original logs, receipts and results remain as `*.attempt1.*`. After adding the exact tracked source helper, only the canonical previously unexecuted run sections were replayed. All existing target object, DSO and harness hashes were sealed before continuation and verified unchanged afterward; successful compilation was not repeated.

All 4 rows below exited 0 with `quiescent=1` and no unexpected session PIDs. Each used the canonical 60-second/524288 KiB enforced watchdog. The continuation coordinator also terminated normally.

| Case | Checks | Vector iterations | Supported | Peak RSS KiB | Exit |
|---|---:|---:|---:|---:|---:|
| neon | 70357 | 3592 | 1 | 8784 | 0 |
| rvv128 | 70357 | 3636 | 1 | 8752 | 0 |
| rvv256 | 70357 | 1832 | 1 | 8896 | 0 |
| no_v | 70357 | 0 | 0 | 9048 | 0 |

Exact current target artifact SHA256 values:

| Artifact (relative to evidence root) | SHA256 |
|---|---|
| `bitmap/aarch64/provider.so` | `0f55655db33e92d5e58a3d84d0be4f841a1e79d909da86d5fc997bc2a63e1756` |
| `bitmap/aarch64/selfcheck` | `3da278a6874882b0acb012201cb438fdd3f2f76f205c5d5297f9228808d9ac13` |
| `bitmap/riscv64/provider.so` | `662e7db8cabf1cc473f9796501fa2f6e2c567b6b89223412c336656635dc8936` |
| `bitmap/riscv64/selfcheck` | `738001cb94343ef51debdbcd4c78e739a30bc4472919a535155aaa6bcfa5c97b` |

Provider ELF targets are AArch64 (machine 183) and RISC-V (machine 243). Bitmap constructor-observer DSOs remain diagnostic artifacts; their loader/lifetime evidence is not transferred to a production Simple application. HTTP rows exercise the canonical C guard-page, input-preservation, output and refusal oracles.

Tool identities (Clang/LLVM 23.1.3, QEMU 10.2.1 and GNU ld 2.46):

| Tool | SHA256 |
|---|---|
| `/usr/lib/llvm-23/bin/clang` | `c300fb439c33a9b2cbde6112a09681ce8278a5bb08bdea3ba0cc91e32d07120d` |
| `/usr/lib/llvm-23/bin/llvm-objdump` | `9671832fd326a5fd6f923e583b5f23b854984864d50c0b26a7647b976f9c4d0a` |
| `/usr/bin/qemu-aarch64` | `e1dc1eb07f2c205a22ac489240578d14d396d767a35bb3734a5ef12f1848ed20` |
| `/usr/bin/qemu-riscv64` | `7a61faa44933bd2d3830f32cd93b98663267ea4b8fe669daea871c398273b7ef` |
| `/usr/bin/aarch64-linux-gnu-ld` | `ef1f32f9d5f522ae9721fe0de846c10fa1ca04f859d491ab30541e9f925b9408` |
| `/usr/bin/riscv64-linux-gnu-ld` | `2bb1314b49f90406e558cfc9d4e28776601617c4c05bd9673117c663b79e3f18` |

Target runtime files (hosted target libc/loader, not a Simple runtime archive):

| File | SHA256 |
|---|---|
| `/usr/aarch64-linux-gnu/lib/ld-linux-aarch64.so.1` | `de9354274cf75ec36e280d3a1a072c4c5736bfb77299b1dba8a10c9ea6efbd3b` |
| `/usr/aarch64-linux-gnu/lib/libc.so.6` | `8f2c2a16a4ee3d5a6e37d1a793ad59f0dfd7dcd216063d230a23e58744dae7ea` |
| `/usr/riscv64-linux-gnu/lib/ld-linux-riscv64-lp64d.so.1` | `d6976785d56eafc476d2e8de278373e397641024c47b48206222dbf36be1da02` |
| `/usr/riscv64-linux-gnu/lib/libc.so.6` | `8d64ca7f710285795d072a9073451d949bff472903562897cfabee6aeaf06292` |

Source and evidence bindings:

- Complete tracked source inventory `source-identity.json`: `8dbbc60bf8325cc20199d1c85d70f5b0a84418bc6a488d74057b4db5785dfb11`.
- Canonical script `scripts/check/check-vector-bitmap-targets.shs`: `a0d07b4be09492a2f5a4daedaf72b6af1ed19159b16d45cc53f8e84f9e0d04eb`.
- ABI header: `a36697d78898a885daefa440b879207ba6e0dd8215b62eb2585bb10650f3578f`.
- Direct text header: `bd2760581182ac03e89bb351335a2743c1d0dab53f802f655af5501f9388757d`.
- Full result/artifact ledger `qualification-summary.json`: `9dc23c6d0d237a1f1ce221a8cde20eb9c6fd62a8c17d3aac81b00b5ecfe82910`.
- Tool/runtime ledger `tool-runtime-identities.json`: `61fc697348b7d0ac24c333af5b4d8dfee5e132fb827f266c10ff3cb67d693e9c`.
- Continuation receipt `bitmap-continuation-terminal.json`: `8461a68449e25473474ac10e2a9be00059e3f2f0aa90c49a974fd2fcc3849d27`.

Durable evidence root: `D:/dev/simple/build/review/item5-cross-canonical-205-20261107/` (WSL `/mnt/d/dev/simple/build/review/item5-cross-canonical-205-20261107/`). Exact row outputs and per-case watchdog receipts are under `bitmap/`; original prelaunch exit-89 records remain adjacent. The continuation terminal binds the replayed canonical run-section hash and unchanged target artifact hashes. No six-profile identity regression or already successful C build was rerun for this documentation.

**Scope:** real target C component execution and dynamic loading under QEMU. This does not qualify Simple DB/HTTP binaries, native hardware performance, full Phase3, aspects/log/profile/AOP, CUDA/device execution, or deployed production provider packaging. The SVE2-labeled build uses SVE kernels and does not establish execution of an SVE2-only opcode. Existing bitmap input-preservation/scalar-result-sentinel coverage limitations remain open.
