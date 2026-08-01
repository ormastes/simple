# GPU WebScene Ports Architecture

**Date:** 2026-07-31  
**Status:** Frozen (C0)  
**Contract Owner:** C0 contract-freeze group  

## Related Documents
- `doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md` — full system plan with rationale
- `doc/03_plan/platform/structural_compute/README.md` — shared structural-compute rules
- `doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md` — MDSOC+ capsule model

## Overview

The GPU WebScene architecture partitions rendering, layout, event dispatch, and state mutation across two MDSOC+ capsules:

1. **HostPlatformCapsule** — CPU-owned: device input normalization, network/file/OS effects, error recovery
2. **GpuWebServiceCapsule** — GPU-owned: DOM, CSS, layout, event routing, DrawIR generation, raster, present

The two capsules communicate through nine stable, versioned ports carrying sealed packets. The CPU receives only compact receipts (epoch completion, host-effect requests, faults, overflow); no DOM/style/layout/pixels cross the boundary on the healthy path.

---

## MDSOC+ Capsule Model

```
HostPlatformCapsule
├─ InputPort (device event → normalized packet)
├─ NetworkPort (pinned HTTP)
├─ StoragePort (file I/O)
├─ Clipboard/IME/AccessibilityPort
└─ FaultRecoveryPort (device restart)

GpuWebServiceCapsule
├─ GpuIngressCapsule (tokenizer, parser)
├─ GpuDomCapsule (DOM pools, node generation)
├─ GpuStyleCapsule (selector match, cascade, var())
├─ GpuLayoutCapsule (formatting context, fragments)
├─ GpuEventCapsule (hit query, listener route, mutation journal)
├─ GpuScriptCapsule (GPU-safe event handlers)
├─ GpuMediaCapsule (image decode, video surface)
├─ GpuDrawIrCapsule (DrawIR v3 count/scan/emit)
├─ GpuRenderCapsule (raster, composition, present)
└─ GpuEvidenceCapsule (fault, fallback, telemetry)
```

---

## Stable Port List

| Port | Purpose | Source File | Trait | Packet Type |
|------|---------|-------------|-------|------------|
| GpuInputPacketPort | Normalized events to GPU | gpu_web_ports.spl | (trait TBD) | GpuInputEvent, GpuMutation |
| GpuResourcePacketPort | Compressed image/video bytes | gpu_web_ports.spl | (trait TBD) | GpuResourcePacket |
| GpuHostEffectRequestPort | GPU→CPU OS operation requests | gpu_web_ports.spl | (trait TBD) | GpuHostEffectRequest |
| GpuHostEffectCompletionPort | CPU→GPU effect results | gpu_web_ports.spl | (trait TBD) | GpuHostEffectCompletion |
| GpuSceneEpochPort | Frame completion and receipt | gpu_web_receipt_contract.spl | GpuFaultReceiptPort | GpuSceneEpochReceipt |
| GpuPackedDrawPort | DrawIR v3 command stream | draw_ir_v3_ports.spl | PackedDrawPort | DrawIrV3Command + side tables |
| GpuMediaSurfacePort | Decoded image/video resources | (TBD) | (trait TBD) | (TBD) |
| GpuFaultReceiptPort | Fault and overflow diagnostics | gpu_web_receipt_contract.spl | GpuFaultReceiptPort | GpuFaultReceipt, GpuOverflowReceipt |
| GpuDebugSnapshotPort | Telemetry and evidence (test/shadow) | (TBD) | (trait TBD) | (TBD) |

---

## Frozen Contract Files and Schema Versions

### gpu_web_ports.spl
**Purpose:** Input event packets, resource packets, and host-effect request/completion records.  
**Schema Version:** `GPU_WEB_PORTS_SCHEMA_VERSION = "simple-gpu-web-ports-v1"` (ID: 1)

**Packet Records:**
- `GpuInputEvent` — device event (kind, position, key, text offset) with scene-generation and sequence
- `GpuMutation` — state mutation record (node_id, field_id, operation, value) written by GPU event handlers
- `GpuHostEffectRequest` — CPU operation request (fetch, file, clipboard, IME, accessibility)
- `GpuHostEffectCompletion` — CPU effect result with status and optional payload
- `GpuResourcePacket` — compressed media bytes (width, height, media_kind, offset in shared arena)

All variable-length data (text, payloads, bytes) lives in fixed event/payload arenas and is referenced by (offset, length), never by host pointers.

### gpu_web_receipt_contract.spl
**Purpose:** Epoch completion, fallback levels, fault diagnostics, and capacity overflow reporting.  
**Schema Version:** `GPU_WEB_RECEIPT_SCHEMA_VERSION = "simple-gpu-web-receipt-v1"` (ID: 1)

**Receipt Records:**
- `GpuSceneEpochReceipt` — frame completion with mutation count, host-effect count, fallback level, deterministic hash
- `GpuFaultReceipt` — feature failure or device fault with capability bit, node ID, reason code
- `GpuOverflowReceipt` — capacity bound exceeded with bound ID, requested, and limit

**Fallback Hierarchy (L0–L5):**
- L0: GPU-native — no CPU fallback
- L1: Host effect — CPU performs only that OS operation, then resumes GPU scene
- L2: Stage service — CPU computes one bounded result (e.g., text shaping), returns as resource
- L3: Subtree compat — CPU renders frozen subtree artifact, GPU composes it
- L4: Document compat — entire document rendered by CPU path
- L5: Device recovery — device lost/OOM/fault, restart backend or full CPU renderer

**Pass Predicates:**
- `gpu_fallback_is_strict_pass(level)` — true if L0 or L1 only
- `gpu_fallback_is_compat_pass(level)` — true if L0–L3

**Route Constants:**
- `GPU_ROUTE_GPU` — GPU handled entire epoch
- `GPU_ROUTE_CPU_SELECTED` — CPU intentionally chosen by cost policy (NOT a fallback)
- `GPU_ROUTE_GPU_FALLBACK` — GPU failed and fell back to CPU

### draw_ir_v3.spl (or draw_ir_v3_ports.spl)
**Purpose:** Packed, no-reallocation display-list command stream and side tables.  
**Schema Version:** `DRAW_IR_V3_SCHEMA_VERSION = "simple-draw-ir-v3"` (ID: 3)

**Hard Invariant:** Render-hot structures contain no text keys and no nested dynamic arrays.

**Command Record:**
- `DrawIrV3Command` — command kind, flags, component/parent IDs, geometry/paint/text/image/path/clip/transform/hit-shape IDs

**Side Tables (struct-of-arrays, flat scalar columns):**
- `DrawIrV3GeometryTable` — xs, ys, widths, heights, corner_radii
- `DrawIrV3PaintTable` — fill_colors, stroke_colors, stroke_widths, opacities, blend_modes
- `DrawIrV3TextRunTable` — glyph runs (start, count), font IDs, sizes, baseline positions; flat glyph columns
- `DrawIrV3ResourceTable` — kinds, formats, dimensions, content hashes (no URI text)
- `DrawIrV3PathPointTable` — span columns (start, count) indexing flat point arrays
- `DrawIrV3ClipTable` — axis-aligned or rounded-rect clips by index

---

## Visibility Rules

| Item | Visibility |
|------|-----------|
| Event and mutation packet schemas | Shared public contract |
| Stable node/resource IDs and generations | Shared public contract |
| Scene generation and receipt schemas | Shared public contract |
| Packed DrawIR v3 command and table schemas | Shared public contract |
| Capacity-manifest structure and validation | Shared public contract (gpu_web_capacity_manifest.spl) |
| Cross-startup cache encoding | Shared versioned contract |
| DOM/style/layout/hit-index pools | Private to GpuWebServiceCapsule |
| GPU scheduler state and dependencies | Private |
| Vulkan/Metal/D3D/CUDA device handles | Backend-private |
| Compiler HIR/MIR internals | Compiler-private |
| CPU oracle reference implementation | Evidence/test capsule |
| Cache storage policy and I/O | Platform-private |

---

## CPU↔GPU Boundary Rules

### Healthy-Path Receipts Only

The CPU never receives:
- Full DOM tree, style tree, or layout tree
- Decoded pixel frame or framebuffer copy
- DrawIR v2 or intermediate processing state

The CPU receives only:
- Epoch completion with mutation count and deterministic hash
- Host-effect requests (fetch, file, clipboard, IME, accessibility)
- Capacity overflow with bound name and measurement
- Unsupported-feature fault with feature bit and scope
- Device fault with recovery recommendation

### No Pixel Readback in Production

Production presentation is GPU-local; composition and display are device-resident. CPU-side validation uses checksums and hashes, never full pixel copies. Pixel readback is permitted only in test/shadow mode and is explicitly marked as such in receipts.

### One Coalesced Packet Per Epoch

- Input: one sealed event batch per epoch (coalesced pointer moves where legal)
- Mutation: one transaction journal commit per epoch
- Host effects: bounded count (default max_host_effects_per_epoch = 4)
- Output: one DrawIR v3 scene generation per epoch

No per-widget GPU submissions. No intermediate host synchronization within an epoch. GPU stages form a deterministic pipeline with deferred mutation journal commit after all listeners complete.

---

## Implementation Notes

- **Isolation Rule 3 (C0 freeze):** After C0 merge, these files are read-only until an explicit schema-version change. No agent edits a frozen contract in place.
- **Reference Oracle:** Every accelerated operation has a CPU oracle. The cpu_oracle implementations (in draw_ir_v3/cpu_oracle/, gpu_event/) are the canonical implementations and are never deleted.
- **No Silent Fallback (Shared Rule 4):** Every fallback carries a reason receipt that names the feature, subtree scope, or fault code. Falling back silently is a defect.

