# Board Vulkan — Intel Gen12 Submit/Readback System Proof (hardware-gated)

> The reader is an engineer asking: *is the board-Vulkan SUBMIT stage for the

<details>
<summary>Full Scenario Manual</summary>

# Board Vulkan — Intel Gen12 Submit/Readback System Proof (hardware-gated)

The reader is an engineer asking: *is the board-Vulkan SUBMIT stage for the

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver / system |
| Status | Hardware-gated — SKIPS today, no code changes needed once hardware lands |
| Plan | doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md |
| Source | `test/03_system/os/vulkan/board_vulkan_intel_gen12_submit_readback_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The reader is an engineer asking: *is the board-Vulkan SUBMIT stage for the
Intel Gen12 backend proven against a real GPU, or only against a synthetic
self-comparison?* `spirv_implemented` is true and proven for this backend;
`submit_implemented`/`readback_implemented` are false because no host in this
fleet has ever exposed a real Intel i915 GPU to capture a genuine anv
command-stream from. This spec exists so that the day a host WITH an Intel
GPU runs this suite, the submit-stage proof appears automatically — with zero
code edits — instead of requiring a human to remember to write it then.

## Scope and Preconditions

This is a SYSTEM spec, gated on real hardware presence (not a stub, not an
environment variable). When no Intel i915 GPU is present, the entire spec
SKIPS via `skip_if`, with the skip reason naming the exact filed gap. When a
GPU is present, the body drives the already-built and already-proven
Gen12 encoder -> adapter -> canonicalizer pipeline
(`encoder_intel_gen12.spl` + `cmdstream_adapter_gen12.spl` +
`boundary_cmdstream_canonicalize.spl`, the same pipeline
`cmdstream_encoder_roundtrip_spec.spl` already exercises synthetically) and
additionally attempts to capture a REAL anv command-stream via
`INTEL_DEBUG=bat`/`aubinator`/`intel_error_decode`, so Simple's encoder output
can be compared against genuine hardware output instead of a second
independent encode of the same synthetic batch.

## Primary Workflow

1. Probe `/sys/class/drm/*/device/uevent` for a device bound to the `i915`
   driver. If none, `skip_if` fires before any assertion runs.
2. If present: encode the minimal Gen12 batch, adapt it through
   `cmdstream_adapter_gen12.spl` into `CmdPacket`s, and confirm the
   comparator accepts the round trip — this is the baseline sanity check
   that must hold before a real-hardware comparison means anything.
3. Probe for `intel_gpu_top`, `aubinator`, and `intel_error_decode` (the
   capture/decode tools an earlier lane found absent on this fleet's
   GPU-less hosts) via `process_run_bounded("sh", ["-c", "command -v ..."])`.
   If still absent even with a GPU present, report that as a DISTINCT,
   more specific finding — do not fabricate a capture path around it.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Real presence probe | `DRIVER=i915` line in `/sys/class/drm/*/device/uevent`, never fabricated |
| Reused pipeline | encoder -> adapter -> comparator, unmodified, read-only for this file |
| Two-stage hardware gate | GPU presence unblocks this spec; capture-tool presence is a second, independently-reported gate |

## Related Specifications

- [Encoder <-> canonicalizer round trip (synthetic, unit-level, always runs)](../../../01_unit/os/vulkan/cmdstream_encoder_roundtrip_spec.spl)
- [Adreno counterpart (also hardware-gated)](board_vulkan_adreno_submit_readback_system_spec.spl)

## Evidence and Provenance

The presence probe is a genuine shell command run via
`process_run_bounded` (`src/lib/nogc_sync_mut/io/process_ops.spl:76`) against
`/sys/class/drm`, not an environment variable or a hardcoded flag. A probe
command that itself fails to run is treated as "not present" (fail-closed
toward skipping), never as license to run the hardware-only body anyway.

## Recovery and Troubleshooting

A red in the reused pipeline once hardware is present means the encoder or
adapter regressed since `cmdstream_encoder_roundtrip_spec.spl` last proved it
green — check that spec first. A red/finding in the capture-tool probe step
means the anv debug tooling is still missing even with real hardware; file
that as its own, more specific gap rather than treating it as this spec's
failure to be written correctly.

## Compatibility and Limitations

This spec cannot and does not fabricate GPU presence, capture tooling, or a
real anv reference stream. Until a host with a genuine Intel i915 GPU runs
this suite, it SKIPS — that is the correct, honest state, not a defect.

## Scenarios

### board Vulkan Intel Gen12 submit/readback (hardware-gated)


## Related Documentation

- **Plan:** `doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-BOARD-VULKAN-SUBMIT-INTEL`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f2e5ac6640c42f78854e971dc9a79fa3508286a3637a68bcfd2856e9eee78d12`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f2e5ac6640c42f78854e971dc9a79fa3508286a3637a68bcfd2856e9eee78d12`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f2e5ac6640c42f78854e971dc9a79fa3508286a3637a68bcfd2856e9eee78d12`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/os/vulkan/board_vulkan_intel_gen12_submit_readback_system_spec.spl
mirror: doc/06_spec/03_system/os/vulkan/board_vulkan_intel_gen12_submit_readback_system_spec.md (current)
findings: 3 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=83; blocker cap makes effective=49
doc/06_spec/03_system/os/vulkan/board_vulkan_intel_gen12_submit_readback_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/03_system/os/vulkan/board_vulkan_intel_gen12_submit_readback_system_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/os/vulkan/board_vulkan_intel_gen12_submit_readback_system_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->
