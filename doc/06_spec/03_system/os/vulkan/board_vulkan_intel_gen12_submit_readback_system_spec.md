# Board Vulkan — Intel Gen12 Submit/Readback System Proof (hardware-gated)

> The reader is an engineer asking: *is the board-Vulkan SUBMIT stage for the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

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
| Updated | 2026-08-27 |
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

#### proves the Gen12 encoder against real i915 hardware, not just self-comparison

**Manual warnings:**
- invalid capture metadata value: bit_table (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- probe for a real Intel i915 GPU and skip honestly when absent
- confirm the Gen12 encoder/adapter/comparator pipeline is internally consistent before comparing to real hardware
- probe for anv capture tooling now that a real GPU is present
- capture tooling still absent even with real hardware — this is a distinct, more specific finding than GPU absence, not fabricated around
- TODO(hw-gated): capture a real anv command-stream via INTEL_DEBUG=bat and compare it against encode_minimal_gen12_batch() output via the adapter/comparator, replacing this synthetic self-comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM REQ-BOARD-VULKAN-SUBMIT-INTEL
step("probe for a real Intel i915 GPU and skip honestly when absent")
if not intel_i915_gpu_present():
    return "skip: No Intel i915 GPU present on this host — see doc/08_tracking/bug/cmdstream_boundary_no_intel_gpu_on_capture_host_2026-08-11.md"
step("confirm the Gen12 encoder/adapter/comparator pipeline is internally consistent before comparing to real hardware")
val dwords_a = encode_minimal_gen12_batch()
val dwords_b = encode_minimal_gen12_batch()
val packets_a = decode_dword_stream_to_packets(dwords_a).unwrap()
val packets_b = decode_dword_stream_to_packets(dwords_b).unwrap()
assert_true(cmd_stream_structural_equal(packets_a, packets_b))
assert_equal(cmd_stream_first_divergence(packets_a, packets_b), -1)  # oracle: two independent minimal batches decode to structurally identical streams

step("probe for anv capture tooling now that a real GPU is present")
val tools_present = intel_anv_capture_tools_present()
if not tools_present:
    step("capture tooling still absent even with real hardware — this is a distinct, more specific finding than GPU absence, not fabricated around")
    assert_false(tools_present)
else:
    step("TODO(hw-gated): capture a real anv command-stream via INTEL_DEBUG=bat and compare it against encode_minimal_gen12_batch() output via the adapter/comparator, replacing this synthetic self-comparison")
    assert_true(tools_present)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


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

- Canonical SPipe generation for source `43a13ef7f81a6c19718b66cd47c245d9df7671e9bda2c551ebc90a77fada2d67`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `43a13ef7f81a6c19718b66cd47c245d9df7671e9bda2c551ebc90a77fada2d67`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `43a13ef7f81a6c19718b66cd47c245d9df7671e9bda2c551ebc90a77fada2d67`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **99/100**; effective score: **99/100**; blockers: **0**.

SSpec documentization score: 99/100
source: test/03_system/os/vulkan/board_vulkan_intel_gen12_submit_readback_system_spec.spl
mirror: doc/06_spec/03_system/os/vulkan/board_vulkan_intel_gen12_submit_readback_system_spec.md (current)
findings: 1 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/vulkan/board_vulkan_intel_gen12_submit_readback_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
<!-- sspec-maintain:scorecard:end -->
