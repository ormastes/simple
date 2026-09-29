# Board Vulkan — IMG BXE-4-32 Submit/Readback System Proof (hardware-gated)

> The reader is an engineer asking: *is the board-Vulkan SUBMIT stage for the

<details>
<summary>Full Scenario Manual</summary>

# Board Vulkan — IMG BXE-4-32 Submit/Readback System Proof (hardware-gated)

The reader is an engineer asking: *is the board-Vulkan SUBMIT stage for the

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver / system |
| Status | Hardware-gated — SKIPS today, no code changes needed once hardware lands |
| Plan | doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md |
| Source | `test/03_system/os/vulkan/board_vulkan_img_bxe_submit_readback_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The reader is an engineer asking: *is the board-Vulkan SUBMIT stage for the
IMG BXE-4-32 backend proven against a real GPU, or only against the encoder's
own unit tests?* `spirv_implemented` is true for this backend;
`submit_implemented`/`readback_implemented` are false because no host in this
fleet has ever exposed a real IMG PowerVR GPU. This spec exists so that the
day a host WITH one runs this suite, the submit-stage proof appears
automatically — with zero code edits — instead of requiring a human to
remember to write it then.

## Scope and Preconditions

This is a SYSTEM spec, gated on real hardware presence (not a stub, not an
environment variable). When no IMG PowerVR GPU is present, the entire spec
SKIPS via `skip_if`, with the skip reason naming the exact filed gap. When a
GPU is present, the body drives the already-built and already-unit-tested
envelope encoder (`encoder_img_bxe.spl`, 6/6 unit-tested by
`img_bxe_encoder_layout_spec.spl`) and re-confirms envelope well-formedness
from a system-level, hardware-present context.

## Primary Workflow

1. Probe `/sys/class/drm/*/device/uevent` for a device bound to the
   `powervr` driver. If none, `skip_if` fires before any assertion runs.
2. If present: build a well-formed job description, validate it, encode it,
   and confirm the encoded packet's dword length matches the declared
   payload size — the same oracle style `img_bxe_encoder_layout_spec.spl`
   already uses, now proven reachable with real hardware attached.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Real presence probe | `DRIVER=powervr` line in `/sys/class/drm/*/device/uevent`, never fabricated |
| Envelope vs firmware stream | Only the kernel-ioctl ENVELOPE is encoded/verified; the firmware-consumed control-stream content is a labelled opaque blob, deliberately not fabricated — see `encoder_img_bxe.spl`'s architectural note |
| Hardware presence is NOT sufficient alone | Two things gate this stage closed: (a) a real board, AND (b) verifying the envelope's field layout against the actual kernel UAPI (`struct drm_pvr_job`) — today the layout is this repo's own convention, unverified against any kernel header |

## Related Specifications

- [Envelope encoder layout (synthetic, unit-level, always runs)](../../../01_unit/os/vulkan/img_bxe_encoder_layout_spec.spl)
- [Intel Gen12 counterpart (also hardware-gated)](board_vulkan_intel_gen12_submit_readback_system_spec.spl)

## Evidence and Provenance

The presence probe is a genuine shell command run via
`process_run_bounded` (`src/lib/nogc_sync_mut/io/process_ops.spl:76`) against
`/sys/class/drm`, not an environment variable or a hardcoded flag. A probe
command that itself fails to run is treated as "not present" (fail-closed
toward skipping), never as license to run the hardware-only body anyway.

This spec deliberately does NOT use `skip(hardware: [...])` —
`matches_hardware()` in `src/lib/nogc_sync_mut/spec/condition.spl` has
backwards semantics (skips when hardware IS present, the opposite of
intent), a known, filed bug
(`test/01_unit/lib/std/spec/condition_hardware_missing_semantics_spec.spl`).
`skip_if` is used instead, with a condition this file defines and controls
directly.

## Recovery and Troubleshooting

A red in the reused encoder once hardware is present means
`encoder_img_bxe.spl` regressed since `img_bxe_encoder_layout_spec.spl` last
proved it green — check that spec first. Passing this spec on real hardware
does NOT by itself close
doc/08_tracking/bug/img_bxe_submit_encoder_envelope_only_no_kernel_uapi_verification_2026-08-11.md
— the kernel-UAPI layout verification (task (b) above) is a separate,
tracked manual step; see the `TODO(hw-gated)` comment below.

## Compatibility and Limitations

This spec cannot and does not fabricate GPU presence or a real kernel-UAPI
comparison. Until a host with a genuine IMG PowerVR GPU runs this suite, it
SKIPS — that is the correct, honest state, not a defect.

## Scenarios

### board Vulkan IMG BXE-4-32 submit/readback (hardware-gated)


## Related Documentation

- **Plan:** `doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-BOARD-VULKAN-SUBMIT-IMGBXE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `26f82861d09d1bfc4b5ff81c7bf280dbdcd9605312b5e0e1f4fbfc8e6f4632fc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `26f82861d09d1bfc4b5ff81c7bf280dbdcd9605312b5e0e1f4fbfc8e6f4632fc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `26f82861d09d1bfc4b5ff81c7bf280dbdcd9605312b5e0e1f4fbfc8e6f4632fc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/os/vulkan/board_vulkan_img_bxe_submit_readback_system_spec.spl
mirror: doc/06_spec/03_system/os/vulkan/board_vulkan_img_bxe_submit_readback_system_spec.md (current)
findings: 2 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
test/03_system/os/vulkan/board_vulkan_img_bxe_submit_readback_system_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/os/vulkan/board_vulkan_img_bxe_submit_readback_system_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->
