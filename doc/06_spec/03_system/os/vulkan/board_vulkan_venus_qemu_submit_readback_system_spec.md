# Board Vulkan — Venus/virtio-gpu QEMU Submit/Readback System Proof (build-gated)

> The reader is an engineer asking: *is the board-Vulkan SUBMIT stage for the

<details>
<summary>Full Scenario Manual</summary>

# Board Vulkan — Venus/virtio-gpu QEMU Submit/Readback System Proof (build-gated)

The reader is an engineer asking: *is the board-Vulkan SUBMIT stage for the

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver / system |
| Status | Build-gated — SKIPS today, no code changes needed once QEMU supports virtio-gpu-gl |
| Plan | doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md |
| Source | `test/03_system/os/vulkan/board_vulkan_venus_qemu_submit_readback_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The reader is an engineer asking: *is the board-Vulkan SUBMIT stage for the
Venus/virtio-gpu backend proven against a real QEMU virtio-gpu-gl device, or
is it blocked?* Unlike the IMG BXE and Intel Gen12 backends, this gate is
**not** a hardware-presence check — Venus runs inside a QEMU guest against a
host-side `virtio-gpu-gl` device, so what's missing is a working QEMU BUILD,
not a physical GPU. This host's `qemu-system-x86_64` 8.2.2 cannot even load
`virtio-gpu-gl` (`undefined symbol: qemu_egl_display`), so `venus=on` is
never evaluated at all. This spec exists so that the day a `qemu-system-x86_64`
build that can load `virtio-gpu-gl` is available, the submit-stage proof
appears automatically — with zero code edits.

## Scope and Preconditions

This is a SYSTEM spec, gated on a real, live capability probe of the actual
`qemu-system-x86_64` binary on this host (not a stub, not an environment
variable, not a version-string check). When `qemu-system-x86_64` is missing,
or present but unable to load `virtio-gpu-gl`, the entire spec SKIPS via
`skip_if`, naming the exact filed gap. When a working build is present, the
body's job is to prove that `_venus_device_available()` in
`vulkan_icd_virtio.spl` — currently hardcoded to `false`, by design, per that
file's own fail-closed docstring — is the single wire-in point still needing
real detection logic; this spec does NOT modify that file.

## Primary Workflow

1. Confirm `qemu-system-x86_64` exists at all (`command -v`). Absence fails
   closed toward "not present".
2. If present, run `qemu-system-x86_64 -M none -device virtio-gpu-gl,help`
   and inspect combined stdout+stderr for the two known failure strings:
   `"opengl is not available"` and `"undefined symbol"`. Either one present
   means virtio-gpu-gl cannot load, and `skip_if` fires.
3. If neither failure string appears, the QEMU build genuinely supports
   virtio-gpu-gl. The body then exercises the public Venus ICD surface
   (`venus_icd_connect` / `venus_icd_create_instance`) and asserts the
   CURRENTLY DOCUMENTED contract still holds — every call still reports
   `Unavailable`, because `_venus_device_available()` has not yet been wired
   to real detection — proving nothing has silently changed underneath
   while this stage remains genuinely blocked on that wiring.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Build gate, not hardware gate | The blocker is a host QEMU binary capability, not a physical device — stated explicitly so this spec is never confused with the hardware-presence gates used by the IMG BXE / Intel Gen12 counterparts |
| Two-stage capability check | `command -v qemu-system-x86_64` (existence) then a real `-device virtio-gpu-gl,help` invocation (capability), never a version-number heuristic |
| Fail-closed Venus ICD | `_venus_device_available()` in `vulkan_icd_virtio.spl` always returns false today, by design (see that file's docstring); this spec proves that contract, never fabricates around it |

## Related Specifications

- [IMG BXE counterpart (hardware-gated, not build-gated)](board_vulkan_img_bxe_submit_readback_system_spec.spl)
- [Intel Gen12 counterpart (hardware-gated, not build-gated)](board_vulkan_intel_gen12_submit_readback_system_spec.spl)

## Evidence and Provenance

The capability probe is a genuine subprocess run via `process_run_bounded`
(`src/lib/nogc_sync_mut/io/process_ops.spl:76`) invoking the real
`qemu-system-x86_64` binary on this host, not an environment variable or a
hardcoded flag. A probe that itself fails to run (binary missing, exec
error) is treated as "not present" (fail-closed toward skipping), never as
license to run the capability-only body anyway. The measured fact motivating
this gate: `qemu-system-x86_64` 8.2.2 on this host cannot load
`virtio-gpu-gl` at all — see
doc/08_tracking/bug/host_qemu_virtio_gpu_gl_missing_egl_symbol_2026-08-11.md.

## Recovery and Troubleshooting

A red in the "contract still holds" assertion once a working QEMU build is
present means `_venus_device_available()` was changed without this spec's
knowledge — re-read `vulkan_icd_virtio.spl`'s docstring and reconcile. That
assertion going red is actually GOOD NEWS if the change was deliberate wiring
of real detection: at that point this spec's remaining job (proving the
still-blocked contract) is complete, and the `TODO(hw-gated)` below should be
resolved by rewriting the body to assert real device detection instead.

## Compatibility and Limitations

This spec cannot and does not fabricate a working `virtio-gpu-gl` QEMU build
or a real Venus device. Until a host with such a QEMU build runs this suite,
it SKIPS — that is the correct, honest state, not a defect. This file never
modifies `vulkan_icd_virtio.spl` — it is read-only for this lane.

## Scenarios

### board Vulkan Venus/virtio-gpu QEMU submit/readback (build-gated)


## Related Documentation

- **Plan:** `doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-BOARD-VULKAN-SUBMIT-VENUS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8415fe0d867864e2e6eb3d942b6e2e6752d3bdf53208e77897830b4f8192ef14`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8415fe0d867864e2e6eb3d942b6e2e6752d3bdf53208e77897830b4f8192ef14`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8415fe0d867864e2e6eb3d942b6e2e6752d3bdf53208e77897830b4f8192ef14`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/os/vulkan/board_vulkan_venus_qemu_submit_readback_system_spec.spl
mirror: doc/06_spec/03_system/os/vulkan/board_vulkan_venus_qemu_submit_readback_system_spec.md (current)
findings: 3 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=83; blocker cap makes effective=49
doc/06_spec/03_system/os/vulkan/board_vulkan_venus_qemu_submit_readback_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/03_system/os/vulkan/board_vulkan_venus_qemu_submit_readback_system_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/os/vulkan/board_vulkan_venus_qemu_submit_readback_system_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->
