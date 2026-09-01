# SimpleOS QEMU host-GPU postponed work

Host-only work completed on 2026-07-15:

- A diagnostic pure-Simple Stage 2/3 bootstrap succeeded; final source-matched admission remains postponed under TODO548.
- The explicit `host-gpu` runtime lane and Vulkan/CUDA provider checks passed at source/static level; no live GPU receipt is claimed.
- Host-side passthrough preflight classified unavailable guest-direct passthrough; live passthrough remains postponed.
- Linux host-daemon linking reached the Engine2D provider-closure boundary.

## Linux daemon runtime-provider closure repair (2026-08-10)

Retained `daemon-build.log` evidence showed two direct unresolved owners:
`lib.common.crypto.sha256.sha256_text -> rt_tls13_sha256` and
`HostFrameClock.sleep_until -> rt_sleep_nanos`. The canonical QEMU wrapper had
a runtime rebuild function, but never called it, and its archive admission
checked only Cargo feature strings. A stale archive with the right feature
fingerprint could therefore reach native linking without those providers.

The wrapper now validates actual global archive definitions for the retained
crypto/clock owners and the Vulkan init, raw SPIR-V compile, and compute
pipeline owners plus the provider-only availability/device-count roots with
portable global-symbol output. It invokes the existing
default-target rebuild path once when that exact closure is absent, preserves
Cargo's target cache, revalidates the produced archive, and otherwise fails
closed with `runtime-provider-closure-missing`. Daemon native-build then passes
that exact admitted archive through `SIMPLE_LINK_OBJECTS`; `--runtime-path`
alone is not provider selection for the `core-c-bootstrap` bundle. The focused
`--self-test-runtime-provider` command proves that a complete archive admits and
links, while archive admission and consumer linking both reject an archive
missing `rt_sleep_nanos`. This repairs build admission only; it does not claim a
compiler, daemon execution, GPU submission, or live QEMU PASS.

Postponed until the required lane or hardware is available:

- **TODO658**: UNO Q native GPU board row is physically unavailable in this lane. Add this as the explicit remaining blocker before finalizing the request:
  - Physical ABX00162/ABX00173 board attached.
  - Runner command for proof handoff:
    - `SIMPLE_BIN=<pure-simple-admitted> SIMPLEOS_UNOQ_BOARD_ATTACHED=1 sh scripts/check/check-simpleos-native-board-gpu-2d.shs --board uno-q --strict`
  - Required retained evidence: board identity and boot/download hashes, native adapter capability, submission/fence path, device identity, DrawIR event/audio/font receipts, device-origin readback, and CPU-SIMD parity.

- Engine2D provider split for Linux Vulkan/CUDA without DirectX/OpenCL/SIMD/font closure dependencies.
- Native x86 GPU readback and ProcessingIR timing receipts.
- AArch64 and RISC-V guest compile/boot/render receipts.
- Native Metal (macOS), DirectX (Windows), and CUDA-device receipts.
- Hardware-board validation and guest passthrough claims.

This ledger does not replace the conflicted shared TODO database; merge it there only after the other work lane resolves its conflicts.
