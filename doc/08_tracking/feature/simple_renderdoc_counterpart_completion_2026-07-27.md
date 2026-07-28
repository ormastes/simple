# Simple RenderDoc counterpart completion

- ID: `FR-RENDERDOC-COUNTERPART-0001`
- Status: current
- Priority: P0

## Local implementation remaining

These are local blockers, not deferred host evidence. TODO317 cannot waive or
close them:

1. **Blocker A — strict RenderDoc join:** bind the capture producer, replay
   inspector, and host classifier to one artifact/device/owner identity and
   reject synthetic-magic-only admission.
2. **Blocker B — target receipt completion:** add the absent x86_64, AArch64,
   and RV64 no-allocation per-operation SIMD owners and feed their real
   fill/copy/alpha/scroll/PRESENT hashes and telemetry through the implemented
   BRR1 adapter and bounded host join.
3. **Blocker C — serialized record boundary (resolved locally):** both the
   native capture probe and translated probe now emit complete schema-v2
   command/pipeline/shader/resource/transition/synchronization records. The
   shared evidence helper extracts both records and invokes the production
   parser, validator, and equivalence policy instead of comparing fixtures or
   hashes alone.

Only after A/B/C land may TODO317 run glyph calibration and admitted
pure-Simple native/live-host qualification, including QEMU/board, coverage,
and retained 4K/8K evidence.

## Resolved locally

- The x86 `facade-draw-image-clip-mask-spec-failed` result was an unresolved
  `engine.spl` conflict, not a pixel mismatch. The six hunks now match the
  parent/origin implementation and the focused facade spec passes 8/8.
- Strict x86 SIMD evidence passes with AVX2 execution, scalar-oracle parity,
  zero mismatches, and positive fill/copy/alpha/blit/scroll hits.
- The scaled-image case now expands 2x2 input to a real 4x2 destination instead
  of taking the facade's equal-size `draw_image` shortcut.
- `scripts/check/check-simple-2d-renderdoc-backend-equivalence.shs` now
  orchestrates bounded profiles, Stage-4 admission, leaf logs, timing/RSS,
  blockers, external rows, and REQ traceability. Its shell self-test passes and
  its modern SSpec passes 2/2 diagnostically.
- The manual/workflow audit now performs real 14-spec/manual pairing across
  canonical and legacy mirrors, modern SSpec source checks, generated-tree
  layout validation, and cooperative-review ownership checks. It passes 4/4
  diagnostically and all generated manuals report zero stubs.
- `backend_render_record_capture.spl` now captures real facade readback,
  adapter/device/driver, request/translation, completion, handle, pixel hash,
  and fallback rejection into the canonical record. The DirectX-on-Vulkan and
  Metal-on-Vulkan constructors now retain their concrete Vulkan owner instead
  of hiding it behind the generic trait.
- The provenance matrix contains no pending helper. It classifies
  physical/software Vulkan, validates both translation labels, rejects native
  Linux D3D/Metal claims, and forces the real Vulkan host-fallback path.
- The production software surface matrix contains no pending helper and passes
  5/5: primitive/effect/state/resource anchors, invalid dimensions/resources,
  backend-proof rejection, exact replay, and 100 fresh deterministic frames.
- Strict `cpu_simd_x86`, `cpu_simd_arm`, and `cpu_simd_riscv` facade creation
  now requires matching architecture, real native hits, bit-exact output, all
  required operations, and zero fallback. The x86 integration spec passes 4/4
  against an independently rendered scalar facade.
- RenderDoc replay inspection passes 4/4: retained live capture classification,
  corrupt/truncated RDC rejection, replay-open failure, and owner/capture frame
  mismatch rejection.
- The SimpleOS target validator now binds serial boot/frame IDs to capture
  boot/frame IDs. The no-allocation guest receipt validator now rejects zero
  firmware and pixel hashes.
- The receipt wire now carries complete 256-bit firmware/pixel digests through
  a fixed-width allocation-free UART byte codec. Its bounded host parser
  rejects malformed, reordered, duplicated, truncated, and oversized records.
- Retained PPM artifact SHA-256 and decoded raw-pixel SHA-256 are separate
  fields; exact oracle and guest hashes must match the decoded pixel digest.
- VirtIO-GPU full and damage flushes now validate both transfer and
  resource-flush responses and surface cache-sync/range failures. The focused
  recovery/response spec passes 12/12.
- The four QEMU/board specs contain no `pending_*` helpers. Their
  host-independent production-validator scenarios pass diagnostically:
  protocol 3/4, guest 1/5, board 3/4, and SIMD 2/6. The remaining scenarios
  fail explicitly on missing live QEMU, guest receipt, SIMD, or board evidence.
- QEMU render capture now removes stale PPM output and keeps COM1 as the
  receipt log while deriving one bounded bidirectional COM2 ACK socket.
- The canonical WM executor resets and retains only the last validated
  presentation's fixed provenance scalars; CPU presentation does not invent a
  device handle or readback identity.
- Each supported QEMU launch now receives a positive `fw_cfg` boot ID and the
  host-computed SHA-256 of the exact ELF. Guest parsing is bounded, strict, and
  overflow-safe, avoiding both guest-clock IDs and impossible ELF self-hashes.
- The x86 VirtIO proof entry now hashes the full flushed ARGB scanout, emits a
  validated BRR1 receipt, waits on COM2 after `BRC1 W`, and emits correlated
  `BRC1 K` only after the host captures and sends the exact `BRC1 A`.
- The x86 live system spec shares one build identity across scenarios, removing
  its duplicate kernel build, and compares the guest digest with independently
  decoded QMP pixels before acknowledging the frame.
- The RV64 desktop now emits the same validated BRR1 receipt after its real
  VirtIO display present. Framebuffer readback takes the entry-owned width and
  height, avoiding unstable cross-module `FramebufferDriver` field layout.
- The ARM64 desktop now emits BRR1 only after the real RAMFB visual-commit
  checksum and retained backend commit both succeed. Its system contract checks
  render/present, identity, trusted-dimension readback, and UART receipt order.

## Current local blockers A/B/C

- The aggregate host classifier currently accepts only
  `rdoc_simple_gate_status=pass` plus four-byte `RDOC` magic, and the gate's
  nominal pass fixture is a synthetic magic-prefixed file. Before host
  promotion, retain and join the existing replay inspector's Vulkan driver,
  successful open/convert, capture-path identity, XML hash/size, relevant
  action, pipeline, shader, and resource counts with the producer's device,
  capture lifecycle, semantic/record/pixel hashes, and owner agreement.
  Duplicate, empty, malformed, mixed-case/all-zero hash, path-alias, and
  synthetic-only evidence must fail closed under REQ-009.
- The shared per-operation BRR1 adapter now maps four full operation hashes and
  telemetry groups plus PRESENT into 17 ordered events; its focused unit passes
  2/2 and its generated manual has zero stubs. The x86_64/AArch64/RV64 noalloc
  `engine2d_simd.spl` target owners are still absent. Only x86/ARM fill is
  honestly vectorized in current guest boot glue; copy/alpha/scroll are scalar
  or absent, RV64 V is disabled end-to-end, and the modern QEMU SIMD matrix
  therefore remains a fail-fast placeholder.
- The local producer path records the actual public Engine2D execution receipt:
  selected backend, RenderDoc device handle, completed present, exact readback,
  and the probe-owned canonical command sequence. It does not claim a
  backend-private driver snapshot. Adding and admitting that optional snapshot
  facade remains a TODO317 live-host feature request, because no such API is
  available in the current backend surface.
- The focused RV64/adapter diagnostic `check` produced no diagnostics but made
  no progress for three minutes and was stopped once without retry. ARM64 BRR1
  source diagnostics are unavailable for the same source-mode/native-build
  reason. The unrelated stale macOS/HVF RAM-tail wrapper reversion in the ARM
  entry remains preserved and must be reconciled by its owner before commit.
- The one-shot framebuffer receipt currently materializes pixel and canonical
  byte arrays. The bounded streaming-SHA upgrade trigger remains in the open
  backend-render receipt bug referenced below; no separate bug document exists.
- Host evidence validation now rejects non-Vulkan backends at the shared
  receipt boundary (11/11 focused unit scenarios pass). The CPU SIMD matrix no
  longer lets qemu-user C target helpers override failed or unavailable
  pure-Simple architecture rows. Current host-contract and architecture-matrix
  specs cover that resolved behavior; no separate bug document is required.

## Deferred acceptance evidence — TODO317

- Add an opt-in backend-owned snapshot facade and validate its private
  pipeline/resource/barrier receipts against the serialized public probe
  record; current local evidence deliberately makes no backend-private claim.
- Run and independently pin the Linux live glyph calibration, then rerun the
  normal live gate against the reviewed glyph hash.
- Deploy one admitted source-matched pure-Simple Stage-4/release CLI; reject
  the stale interpreter extern table and Rust-seed native delegation.
- Capture native x86/ARM NEON/RISC-V RVV, Linux X11/winit, Vulkan/device
  readback, external and repo-native RenderDoc, Chrome/Electron parity,
  retained 4K/8K, FreeBSD/QEMU, physical-board, macOS, and Windows evidence.
- Produce the admitted 98–100% owned-lane coverage artifact and run the current
  backend-receipt wire plus SimpleOS render-evidence protocol specs once on the
  admitted binary. These are evidence runs, not local A/B/C implementation
  substitutes.

## Existing proof

- Backend render record unit checks: 6/6.
- Backend equivalence integration checks: 5/5.
- Pure-Simple RDC XML inspector checks: 5/5.
- RenderDoc replay inspection: 4/4.
- Portable SimpleOS render/SIMD evidence validation: 14/14.
- Simple RenderDoc manual/contract audit: 4/4.
- Cross-ISA owner compilation and QEMU x86/NEON/RVV target binaries pass.
- `doc/06_spec` contains zero executable `.spl` specs.

## Acceptance

- No pending placeholders in the counterpart specs.
- The aggregate checker reports performance, artifacts, blockers, and REQ
  coverage.
- Current-host checks are green before external-host qualification resumes.
- External rows remain blocked until their real evidence exists.

## References

- `doc/02_requirements/feature/simple_2d_renderdoc_backend_equivalence.md`
- `doc/04_architecture/simple_2d_renderdoc_backend_equivalence.md`
- `doc/05_design/simple_2d_renderdoc_backend_equivalence.md`
- `doc/00_llm_process/feature_expert/simple_renderdoc/skill.md`
- `doc/08_tracking/bug/simpleos_backend_render_receipt_producer_parser_missing_2026-07-27.md`
- `doc/08_tracking/todo/simple_renderdoc_external_host_postponed_2026-07-27.md`
- `doc/08_tracking/feature/wm_gui_web_2d_host_environment_acceptance_evidence_2026-07-28.md`

This standalone request avoids the concurrently modified shared feature
database.
