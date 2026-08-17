## Triage 2026-08-17 — BLOCKED, skipped fast (not a compiler/runtime/tooling defect)

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

Blocker: needs the upstream `drivers/gpu/drm/imagination` `struct drm_pvr_job`
header text (not vendored in this tree) to confirm field offsets, plus PowerVR
hardware to validate against. No fetch route in this lane. Unblock = vendor the
UAPI header (or cite a pinned upstream revision) and re-derive
`img_bxe_job_field_offset`/`img_bxe_sync_op_offset` against it. Unchanged.
# IMG BXE-4-32 submit encoder: envelope-only, no verified kernel UAPI byte layout

**Date:** 2026-08-11
**Lane:** E2 (board_vulkan parallel SoC lanes, stage 3 "submit")
**Files:** `src/os/drivers/gpu/board_vulkan/encoder_img_bxe.spl`,
`test/01_unit/os/vulkan/img_bxe_encoder_layout_spec.spl`

## Finding

Imagination PowerVR Rogue/BXE's submission model is **firmware-mediated**,
not a freely-authored GPU packet stream. Unlike Adreno's CP packets or
Intel's MI_*/3DSTATE_* batch-buffer opcodes — both directly executed by the
GPU and encodable as a full command stream from public docs — PowerVR work
goes through a kernel ioctl envelope (`DRM_IOCTL_PVR_SUBMIT_JOBS` /
`struct drm_pvr_job` in the upstream `drivers/gpu/drm/imagination` UAPI)
that hands a job type, context/HWRT handles, sync-in/out fence ops, and a
pointer+length to a userspace-built control stream (CCB). The **firmware**,
not the GPU core, interprets that control stream's bytes; its internal
format (`pvr_rogue_fwif*`) is versioned per firmware release and is not a
stable, freely-encodable ISA the way the other two lanes' targets are.

## What was encoded vs. declared opaque

- **Encoded:** the submission envelope shape every PowerVR job structurally
  needs — job type, context handle, HWRT dataset handle, sync-op fences
  (handle/flags/value), and the control-stream's length — with a
  self-consistent, testable dword layout (`img_bxe_job_field_offset`,
  `img_bxe_sync_op_offset`, `img_bxe_job_payload_size`) and input
  validation (`img_bxe_job_is_valid`).
- **Declared opaque, never fabricated:** the control-stream (CCB) payload
  bytes themselves. The encoder carries only `stream_len` and a labelled
  `opaque_firmware_blob` field; it does not attempt to decompose or invent
  firmware-internal packet content.

## Why this is not byte-exact against the real kernel UAPI

This repo/session had no verified local copy of the actual
`struct drm_pvr_job` header text (no vendored kernel header under this
tree, no fetch route available in this task) to confirm exact field
offsets, so the encoder's dword layout is this file's **own** internal
convention, not asserted to match the real upstream struct byte-for-byte.
The spec's oracles (offset arithmetic, size-field-equals-payload,
validation rejection) are format-derived and pass, and a sabotage
(`IMG_BXE_HEADER_DWORDS` mutated 5→4) was proven to turn one assertion RED
naming the exact mismatch (`expected 5, got 4`), then restored — but this
only proves internal self-consistency, not conformance to the real kernel
ABI.

## Unblock condition

Obtain the actual `include/uapi/drm/pvr_drm.h` (or equivalent) text from
the upstream Linux kernel source that ships the `imagination`/`powervr`
DRM driver, diff its `struct drm_pvr_job` / `drm_pvr_sync_op` field order
and sizes against `encoder_img_bxe.spl`'s layout, and update the offset
constants to match exactly. Only then would a `byte_exact` comparison
against a real Mesa `powervr` capture (also currently unavailable — no
VisionFive 2 / IMG BXE-4-32 hardware or firmware build present) become
meaningful.

## Profile flags (unchanged, correctly false)

`img_bxe_board_profile()` in `backend_img_bxe.spl` still has
`spirv_implemented = false`, `submit_implemented = false`,
`readback_implemented = false`. Stage 3 ("submit") requires a `byte_exact`
comparison against Mesa `powervr`'s real
`vulkan.submit.command_stream@1` capture, which this lane cannot produce
(no verified kernel-UAPI layout, no board/firmware). `submit_implemented`
is not flipped. `soc_profile.spl` was not edited by this lane.
