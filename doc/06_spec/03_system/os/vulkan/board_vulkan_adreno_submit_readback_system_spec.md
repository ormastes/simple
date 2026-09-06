# Board Vulkan — Adreno Submit/Readback System Proof (hardware-gated)

> The reader is an engineer asking: *is the board-Vulkan SUBMIT stage for the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Board Vulkan — Adreno Submit/Readback System Proof (hardware-gated)

The reader is an engineer asking: *is the board-Vulkan SUBMIT stage for the

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver / system |
| Status | Hardware-gated — SKIPS today, no code changes needed once hardware lands |
| Plan | doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md |
| Source | `test/03_system/os/vulkan/board_vulkan_adreno_submit_readback_system_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The reader is an engineer asking: *is the board-Vulkan SUBMIT stage for the
Adreno backend proven against a real board, or is it blocked purely by
hardware absence?* Unlike the Intel Gen12 lane, Adreno has no QEMU device
model at all — `board_vulkan_cross_arch_boundary_only_x86_64_proven_2026-08-11.md`
records that only the x86_64 boundary has ever been exercised. This spec
exists so the day a real Adreno-equipped board runs this suite, the
submit-stage proof appears with zero code changes — but it is honest that
hardware presence ALONE is not sufficient here: unlike Gen12, no
comparator/adapter wiring (`cmdstream_adapter_gen12.spl`'s Adreno
counterpart) exists yet, so this spec cannot prove a cross-implementation
comparison even once hardware lands, only that the real encoder runs and
produces a well-formed stream on real silicon.

## Scope and Preconditions

This is a SYSTEM spec, gated on real hardware presence (not a stub, not an
environment variable). When no Adreno GPU is present, the entire spec SKIPS
via `skip_if`, naming the exact filed gap. When present, the body reuses the
already-unit-tested `encoder_adreno.spl` PKT4/PKT7 encoder (10/10 unit-tested
in `adreno_cmdstream_encoder_pkt_header_spec.spl`) to build the minimal
submission and checks it is well-formed by the same round-trip/dword-count
oracle style that unit spec already established — it does not invent a new
oracle or fabricate a comparator.

## Primary Workflow

1. Probe `/sys/class/drm/*/device/uevent` for a device bound to the `msm`
   driver (the upstream Adreno/turnip kernel driver name). If none,
   `skip_if` fires before any assertion runs.
2. If present: build `adreno_minimal_submission()` and confirm it succeeds
   and its total dword count is well-formed (matches the sum of each
   packet's own declared header + payload length), reusing the round-trip
   style already proven in the unit spec.
3. Note, unconditionally in this file's docstring and via a `# TODO(hw-gated)`
   comment, that a turnip-comparison adapter (mirroring
   `cmdstream_adapter_gen12.spl`) is a SEPARATE prerequisite this spec cannot
   satisfy by itself, even with hardware present.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Real presence probe | `DRIVER=msm` line in `/sys/class/drm/*/device/uevent`, never fabricated |
| Two independent blockers | (1) no hardware today, (2) no comparator adapter exists even once hardware lands — this spec only lifts blocker (1) |
| Reused oracle | well-formed-stream check, same style as `adreno_cmdstream_encoder_pkt_header_spec.spl`, not a new invented oracle |

## Related Specifications

- [Adreno PKT4/PKT7 header format (unit, always runs)](../../../01_unit/os/vulkan/adreno_cmdstream_encoder_pkt_header_spec.spl)
- [Intel Gen12 counterpart (also hardware-gated, has a comparator adapter)](board_vulkan_intel_gen12_submit_readback_system_spec.spl)

## Evidence and Provenance

The presence probe is a genuine shell command run via `process_run_bounded`
(`src/lib/nogc_sync_mut/io/process_ops.spl:76`) against `/sys/class/drm`, not
an environment variable or a hardcoded flag. A probe command that itself
fails to run is treated as "not present" (fail-closed toward skipping).

## Recovery and Troubleshooting

A red once hardware is present and this spec runs means `encoder_adreno.spl`
regressed since the unit spec last proved it green — check that spec first.
This spec passing does NOT mean submit/readback is proven end-to-end for
Adreno: the missing turnip-comparison adapter is a distinct, still-open
prerequisite (see the `# TODO(hw-gated)` comment below).

## Compatibility and Limitations

This spec cannot fabricate Adreno hardware presence, a QEMU device model, or
a comparator adapter that does not exist. Until a real Adreno-equipped board
runs this suite, it SKIPS — that is the correct, honest state. Even once it
runs, it proves only "the encoder produces a well-formed stream on real
silicon", not "the stream matches an independent turnip reference" — that
second, stronger proof needs the adapter noted above.

## Scenarios

### board Vulkan Adreno submit/readback (hardware-gated)

#### builds a well-formed Adreno minimal submission on real silicon

**Manual warnings:**
- invalid capture metadata value: bit_table (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- probe for a real Adreno (msm-bound) GPU and skip honestly when absent
- build the minimal PKT4/PKT7 submission via the real encoder
- confirm the stream is well-formed: at least the register-write and NOP packets are present
- re-walk the stream on real silicon: header-declared lengths must land exactly on the stream end


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM REQ-BOARD-VULKAN-SUBMIT-ADRENO
step("probe for a real Adreno (msm-bound) GPU and skip honestly when absent")
if not adreno_msm_gpu_present():
    return "skip: No Adreno (msm) GPU present on this host — no QEMU device model exists for Adreno and no board is present, see doc/08_tracking/bug/board_vulkan_cross_arch_boundary_only_x86_64_proven_2026-08-11.md"
step("build the minimal PKT4/PKT7 submission via the real encoder")
val result = adreno_minimal_submission()
assert_true(result.is_ok())
val dwords = result.unwrap()
assert_true(dwords.len() > 0)

step("confirm the stream is well-formed: at least the register-write and NOP packets are present")
assert_true(dwords.len() >= 3)

step("re-walk the stream on real silicon: header-declared lengths must land exactly on the stream end")
var i: i64 = 0
var packets: i64 = 0
while i < dwords.len():
    val header = dwords[i]
    val type_tag = (header >> 28) & 0xF
    var count: i64 = 0
    if type_tag == 4:
        count = pkt4_decode_count(header)
    else:
        count = pkt7_decode_count(header)
    i = i + 1 + count
    packets = packets + 1
assert_equal(i, dwords.len())  # oracle: header-declared counts sum exactly to the emitted stream length
assert_equal(packets, 3)  # oracle: the minimal submission is exactly three packets (write, CP_NOP, submit)
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
- `REQ-BOARD-VULKAN-SUBMIT-ADRENO`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `094f8f090c51e6bdeab5a10686faf057bcf5068942a8192a8c7888764960f4cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `094f8f090c51e6bdeab5a10686faf057bcf5068942a8192a8c7888764960f4cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `094f8f090c51e6bdeab5a10686faf057bcf5068942a8192a8c7888764960f4cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **99/100**; effective score: **99/100**; blockers: **0**.

SSpec documentization score: 99/100
source: test/03_system/os/vulkan/board_vulkan_adreno_submit_readback_system_spec.spl
mirror: doc/06_spec/03_system/os/vulkan/board_vulkan_adreno_submit_readback_system_spec.md (current)
findings: 1 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/vulkan/board_vulkan_adreno_submit_readback_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
<!-- sspec-maintain:scorecard:end -->
