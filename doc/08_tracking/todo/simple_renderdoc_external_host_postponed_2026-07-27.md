# Simple RenderDoc external-host qualification TODO

Authoritative acceptance ID: **TODO317**. The consolidated cross-host matrix,
immutable artifact contract, owners, and final acceptance rule are maintained
in `doc/08_tracking/feature/wm_gui_web_2d_host_environment_acceptance_evidence_2026-07-28.md`.
This file remains the stable detailed RenderDoc/QEMU handoff and the `todo_db`
source path; it does not define a second acceptance scope.

Status: postponed until local implementation and aggregate checks are green.

Local implementation lanes A/B/C, including compiler, backend, producer/parser,
and wrapper defects, remain with their existing owners; TODO317 consumes their
green outputs and does not turn them into external-host deferrals.
Only prepared native ISA, live display/GPU/RenderDoc/browser, platform/QEMU/
board, and qualified performance-host execution is postponed here.

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

The prepared Linux display handoff is additionally blocked while the canonical
wrapper contains `GLYPH_RGB_SHA256=pending`. Calibrate only from a reviewed
glyph crop captured by the real X11/Vulkan lane, then pin the lowercase SHA-256
and rerun the same wrapper. Fixtures, synthetic crops, CPU mirrors, fallback
pixels, and screenshots cannot satisfy this calibration.

The prepared-host Simple resume entrypoint now performs both halves of the
focused lane. It captures
`<GUI_WEB_2D_VULKAN_BUILD_DIR>/renderdoc/simple/evidence.env`, passes that exact
file to the strict replay/readback gate, and writes the canonical consumer row
to `build/renderdoc/simple-gate/evidence.env`. Capture or gate failure is
reported through typed setup status/reason rows and a nonzero exit. This closes
the local resume-path gap only; no external-host RenderDoc row is promoted.

Browser parity artifact-freshness follow-up is implemented locally: the setup
producer emits SHA-256 bindings for all three ARGB and all three diff artifacts,
the pure contract rejects missing, malformed, or duplicate bindings, and
`test_host_env` re-hashes six current regular/no-follow files before admitting
the Vulkan row. External-host qualification remains postponed and still needs
fresh browser/Vulkan evidence from the prepared host.

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

Current preparation: generic cross-ISA compilation and QEMU x86/NEON/RVV
target binaries pass. The local per-operation noalloc SIMD owners required by
blocker B remain absent; these target builds do not complete them. RenderDoc
v1.44 source and rootless Linux dependencies are prepared, but no external-host
row is promoted.

TODO317 owns only the prepared host's fresh retained coverage report and its
admitted executable/report hashes. Local admission logic is complete in
`scripts/check/check-wm-gui-web-2d-coverage-admission.shs`; promotion still
requires rerunning the instrumented owners with the fresh source-matched
pure-Simple executable on that host. Synthetic fixtures and annotations on
shell-only specs cannot satisfy this external row.

Full-system QEMU remains postponed: guest-local `uname` cannot distinguish a
VM from physical hardware. Promotion from such guests needs an external native
producer attestation bound into the SIMD frame receipt. User-mode QEMU/binfmt
is already classified as `emulated` and cannot promote a host row.

The current diagnostic runner cannot replace the Stage-4 row: interpreter
execution stops at its stale `rt_is_interpreter_runtime` extern table, while
native SSpec mode delegates to the forbidden Rust seed and omits the source
argument. Do not rerun those modes until a newly admitted pure-Simple Stage-4
binary is installed. That fresh binary must run the existing
`test/01_unit/lib/common/renderdoc/backend_render_receipt_wire_spec.spl` and
`test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl` identity
contracts once; the formerly cited `qemu_firmware_identity_spec.spl` path does
not exist and is not an acceptance artifact.

Resume only after
`doc/08_tracking/feature/simple_renderdoc_counterpart_completion_2026-07-27.md`
has no placeholders and its canonical aggregate check is green.

This stable ledger is registered as TODO317 in the shared TODO database; the
authoritative feature request above defines the single acceptance scope.
