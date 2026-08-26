# Board Vulkan — Adreno Submit/Readback System Proof (hardware-gated)

> The reader is an engineer asking: *is the board-Vulkan SUBMIT stage for the

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
| Updated | 2026-08-26 |
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

- Canonical SPipe generation for source `831d8c3a9d89f296ef9542d888fb1531a83417e88f44e83e65ccd55dec4e2755`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `831d8c3a9d89f296ef9542d888fb1531a83417e88f44e83e65ccd55dec4e2755`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `831d8c3a9d89f296ef9542d888fb1531a83417e88f44e83e65ccd55dec4e2755`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/os/vulkan/board_vulkan_adreno_submit_readback_system_spec.spl
mirror: doc/06_spec/03_system/os/vulkan/board_vulkan_adreno_submit_readback_system_spec.md (current)
findings: 3 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=83; blocker cap makes effective=49
doc/06_spec/03_system/os/vulkan/board_vulkan_adreno_submit_readback_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/03_system/os/vulkan/board_vulkan_adreno_submit_readback_system_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/os/vulkan/board_vulkan_adreno_submit_readback_system_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
<!-- sspec-maintain:scorecard:end -->
