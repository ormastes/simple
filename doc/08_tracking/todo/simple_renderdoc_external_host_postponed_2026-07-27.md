# Simple RenderDoc external-host qualification TODO

Status: postponed until local implementation and aggregate checks are green.

| Environment | Required evidence | Resume entrypoint |
|---|---|---|
| Fresh pure-Simple Stage-4 toolchain | Essential-tools admission, native SSpec compile, coverage/docgen identity | Rebuild Stage 4, then `scripts/check/check-bootstrap-essential-tools-smoke.shs` with that exact binary |
| Prepared Linux Vulkan + RenderDoc + display | `.rdc` replay-open, RDOC/device readback, exact pixels | `scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple` |
| Linux physical + software Vulkan ICDs | Separate NVIDIA/AMD/Intel and lavapipe records with distinct device classes | Run the provenance matrix once per selected ICD, then the intensive aggregate profile |
| Native AArch64 | NEON native hits with exact scalar parity | Native ARM64 host |
| Native RISC-V | RVV native hits with exact scalar parity; QEMU is not promotion evidence | Native RVV host |
| Windows | Native D3D11/D3D12 staging, capture, and exact readback | Native Windows host |
| macOS | Native Metal completion, capture, and exact readback | Native macOS host |
| Physical boards | Identity, firmware, boot, receipt, external capture, and oracle evidence | Board-specific lane |
| Chrome/Electron | Vulkan backing, interaction, RDC capture, and exact ARGB | Prepared browser host |

## Active fail-closed system rows

| Spec | Diagnostic result | Missing prerequisite |
|---|---:|---|
| `test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl` | 3/4 | Guest ordered-receipt emitter/parser and fresh Stage-4 QEMU capture |
| `test/03_system/os/simpleos_engine2d_guest_backend_equivalence_spec.spl` | 1/5 | Per-target live receipt and QMP identity correlation |
| `test/03_system/os/qemu/simpleos_engine2d_simd_matrix_spec.spl` | 2/6 | Complete per-operation guest SIMD receipts and exact QMP pixels |
| `test/03_system/os/simpleos_physical_board_render_evidence_spec.spl` | 3/4 | Real board identity, firmware, boot transcript, and capture |

Resume QEMU rows with the exact fresh Stage-4 binary and the canonical QEMU
harness under `test/03_system/os/qemu/os/common/qemu_os_harness.spl`. Resume the
board row through its board-specific lane. Retain serial logs, QMP PPM files,
firmware/image hashes, boot/frame IDs, and final oracle mismatch counts.
Owner: Simple RenderDoc lane. Final reviewer: highest available normal Codex.
Local producer/parser work is tracked in
`doc/08_tracking/bug/simpleos_backend_render_receipt_producer_parser_missing_2026-07-27.md`.
Build/boot identity injection is now local and honest: the runner supplies a
per-launch boot ID plus the SHA-256 of the exact ELF over `fw_cfg`. The x86
VirtIO guest receipt and COM2 hold/capture/ACK path are implemented. RV64 now
emits a matching receipt after its real display present and reads the scanout
with entry-owned dimensions. ARM64 now emits after its RAMFB visual-commit and
retained backend proof. Resume both with a fresh Stage-4 build/run; the
canonical ARM entry's unrelated stale macOS/HVF RAM-tail wrapper reversion must
still be reconciled by its owner before commit.

Current preparation: cross-ISA owner compilation and QEMU x86/NEON/RVV target
binaries pass. RenderDoc v1.44 source and rootless Linux dependencies are
prepared, but no external-host row is promoted.

Full-system QEMU remains postponed: guest-local `uname` cannot distinguish a
VM from physical hardware. Promotion from such guests needs an external native
producer attestation bound into the SIMD frame receipt. User-mode QEMU/binfmt
is already classified as `emulated` and cannot promote a host row.

The current diagnostic runner cannot replace the Stage-4 row: interpreter
execution stops at its stale `rt_is_interpreter_runtime` extern table, while
native SSpec mode delegates to the forbidden Rust seed and omits the source
argument. Do not rerun those modes until a newly admitted pure-Simple Stage-4
binary is installed. That fresh binary must also run
`test/01_unit/os/qemu_firmware_identity_spec.spl`: the diagnostic runner
reached the mandatory three-cycle cap at 1/2, after which its incorrect
postfix-optional presence assertion was corrected without another retry.

Resume only after
`doc/08_tracking/feature/simple_renderdoc_counterpart_completion_2026-07-27.md`
has no placeholders and its canonical aggregate check is green.

This standalone ledger avoids the concurrently modified shared TODO database.
