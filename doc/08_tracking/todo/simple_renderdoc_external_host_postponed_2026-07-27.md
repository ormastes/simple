# Simple RenderDoc external-host qualification TODO

Status: postponed until local implementation and aggregate checks are green.

Historical 4K/8K performance-regression baseline policy is tracked separately
in `doc/08_tracking/todo/rendering_performance_historical_regression_baseline_2026-07-27.md`.

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

The prepared-host Simple resume entrypoint now performs both halves of the
focused lane. It captures
`<GUI_WEB_2D_VULKAN_BUILD_DIR>/renderdoc/simple/evidence.env`, passes that exact
file to the strict replay/readback gate, and writes the canonical consumer row
to `build/renderdoc/simple-gate/evidence.env`. Capture or gate failure is
reported through typed setup status/reason rows and a nonzero exit. This closes
the local resume-path gap only; no external-host RenderDoc row is promoted.

Browser parity artifact-freshness follow-up: the pure host classifier now
requires producer-admitted source files, nonempty ARGB/diff paths, exact
viewport bindings, and zero-mismatch pairwise receipts. The setup producer does
not yet emit SHA-256 bindings for all three ARGB and diff artifacts, so
`test_host_env` cannot independently re-hash those current files as it does for
RenderDoc and live-WM captures. Add those hashes and regular/no-follow
revalidation before claiming cryptographic freshness; this does not weaken the
new scalar/provenance gate.

## Concrete external-host handoff

| Row | Owner | Prerequisites | Retained artifacts | Exact resume command |
|---|---|---|---|---|
| Windows Vulkan/PowerShell | prepared Windows Vulkan host operator | `pwsh`, Vulkan driver/ICD, admitted pure-Simple `simple.exe`, writable build directory | evidence env/log, strict/parity logs, backend/device identity, exact 256-pixel checksums | `pwsh -File scripts/check/check-vulkan-engine2d-readback.ps1 -SimpleBinary <admitted-simple.exe>` |
| ARM64 QEMU | `/root/arm_qemu_owner` | QEMU AArch64, firmware, admitted ELF/FAT disk/manifest | frozen manifest, ELF/FAT hashes, serial/QMP/RAMFB captures, VirtIO/NEON receipts, timing/RSS | `sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs && sh scripts/check/check-simpleos-arm64-qmp-input-evidence.shs` |
| RV64 QEMU | prepared RV64 host operator | QEMU RV64, admitted ELF, PCI VirtIO input, QMP, parity oracle | frozen manifest, ELF hash, serial/QMP/RAMFB captures, PCI/ISR/input receipts, parity, timing/RSS | `bin/simple os build --scenario=riscv64-display-smoke && scripts/check/check-rv64-display-smoke-qmp-evidence.shs --wm-font-input` |

## Active fail-closed system rows

| Spec | Diagnostic result | Missing prerequisite |
|---|---:|---|
| `test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl` | 3/4 | Guest ordered-receipt emitter/parser and fresh Stage-4 QEMU capture |
| Aggregate `simpleos_guest` external row | blocked | Strict x86 VirtIO plus per-target live receipt and QMP identity correlation |
| Aggregate `simpleos_simd` external row | blocked | Three-architecture, ten-boot fill/copy/alpha/scroll SIMD receipts and exact QMP pixels |
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
