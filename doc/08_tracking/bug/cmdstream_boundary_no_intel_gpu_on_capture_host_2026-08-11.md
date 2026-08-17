# Command-stream boundary (`vulkan.submit.command_stream@1`, lane R4/B3): no Intel GPU on capture host, and no candidate encoder anywhere

**Date:** 2026-08-11
**Status:** SOURCE FIXED (2026-08-17); LIVE INTEL ANV EVIDENCE PENDING
**Lane:** R4 / SoC lane B3 (Intel Gen12 / Xe-LP, counterpart Mesa `anv`)
**Architecture:** doc/04_architecture/os/vulkan/simpleos_board_vulkan_driver_architecture_2026-08-10.md
**Plan:** doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md

## Finding

This boundary cannot be exercised with a real Mesa `anv` capture on this
host, for two independent reasons:

1. **No candidate.** `src/os/drivers/gpu/board_vulkan/backend_intel_gen12.spl`
   declares `spirv_implemented/submit_implemented/readback_implemented` all
   `false`. `board_profile_false_claim` in `soc_profile.spl` rejects any
   profile claiming `submit` without `spirv`. There is no command-stream
   encoder anywhere under `src/os/drivers/gpu/board_vulkan/`.
2. **No reference-capture hardware.** `lspci -nn` on this host lists exactly
   two VGA controllers, both NVIDIA: `0a:00.0 ... GA102GL [RTX A6000]
   [10de:2230]` and `42:00.0 ... TU102 [TITAN RTX] [10de:1e02]`. There is no
   Intel display/GPU device at all. `/dev/dri/card1` and `card2` are both
   vendor `0x10de`. Running `vulkaninfo` against
   `/usr/share/vulkan/icd.d/intel_icd.json` fails with `ERROR:
   setup_loader_term_phys_devs: Failed to detect any valid GPUs in the
   current config` — this is hardware absence, not a permissions problem
   (the user is also not in the `render`(993)/`video`(44) groups, but that is
   moot: there is no Intel device node to open regardless).
   `intel_error_decode`, `aubinator`, `intel_dump_gpu` are not installed;
   `mesa-utils` is not installed. Only `mesa-vulkan-drivers` 25.2.8 is present
   (ships `libvulkan_intel.so` + the ICD json), and it cannot attach to a
   device that does not exist on this machine. `INTEL_DEBUG=bat` decodes
   batches Mesa itself submits to a live device — with no device, there is
   nothing to intercept.

Both facts hold independently: even with root and a `render` group
membership, there is no Intel silicon to decode a batch from; even with
Intel silicon, there is no encoder in this repo to produce a candidate
stream to compare.

## What was done instead

`src/os/drivers/gpu/board_vulkan/boundary_cmdstream_canonicalize.spl` defines
the canonical packet schema (opcode + dword length + ordered payload fields)
and the comparator (`cmd_stream_structural_equal`,
`cmd_stream_first_divergence`) the future encoder must satisfy, with four
explicitly named dropped dimensions (GPU virtual address, BO handle,
timestamp, zero-valued MBZ/pad) — never a reachability or "unreferenced"
heuristic, per the SPIR-V boundary's own postmortem
(`spirv_boundary_canonicalizer_reachability_filter_dropped_live_instructions_2026-08-10.md`).
A synthetic (explicitly labelled, never claimed as captured) five-packet
Gen12 fixture exercises the comparator in
`test/01_unit/os/vulkan/cmdstream_boundary_intel_gen12_spec.spl`, including
three sabotage cases (mutated operand, reordered packets, dropped packet)
that must go RED and name the diverging packet index.

## Relation

The plan declares `byte_exact` for this boundary. That is preserved, not
weakened: `structural_equal` is applied to the CANONICAL packet sequence
(same two-step discipline the SPIR-V boundary already uses — normalize named
per-run dimensions, then require exact agreement on everything else,
including packet order and count). No tolerance was introduced.

## Status

Candidate side: `ProviderStatus.unavailable` (no encoder). A real
counterpart run against this boundary is correctly rejected today. This
finding and the schema exist so the future encoder has a true oracle,
not so the boundary is falsely marked exercised.

## Recommended next step

Either (a) get Intel Gen12 silicon reachable to this project (a physical UP
Squared/UP 4000-class board, or a host with an Intel iGPU/dGPU), and capture
a real `anv` batch via `INTEL_DEBUG=bat` once such a host exists, or (b) if a
board arrives before host access does, capture directly on the board per
`.claude/rules/board-runnable.md`. Do not substitute a hand-authored stream
for a real capture in either case — extend the synthetic fixture's role only
as a schema exemplar.

---

## Triage classification 2026-08-17 — DEFERRED: requires hardware (Intel GPU) not present

Reviewed in the second-pass backlog sweep. Not actionable from this session:
the record's own title states the capture host has no Intel GPU; the evidence this bug needs cannot be produced here by any code change. No code change is possible without that, so no
speculative fix was attempted. Classification recorded here so future sweeps
skip it in O(1) instead of re-deriving the blocker. Status remains OPEN.

## 2026-08-17 re-verification — still BLOCKED, host unchanged

`lspci -nn | grep -i vga` on this host still lists exactly two NVIDIA VGA
controllers and no Intel display/GPU device:

```
0a:00.0 ... NVIDIA GA102GL [RTX A6000] [10de:2230]
42:00.0 ... NVIDIA TU102 [TITAN RTX] [10de:1e02]
```

Both stated blockers hold: no Mesa `anv` reference-capture hardware, and no
command-stream encoder in `src/os/drivers/gpu/board_vulkan/`. Unblock requires
an Intel Gen12/Xe-LP capture host; nothing in this lane can move it.

---

## 2026-08-17 — scope question answered: the capture path IS genuinely Intel-specific

Asked explicitly whether this boundary merely needs *a* GPU (this host has two
real NVIDIA GPUs: RTX A6000 and TITAN RTX, driver 580.126.16, both enumerating
under `VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/nvidia_icd.json vulkaninfo` with
`vendorID = 0x10de`). Answer: **no — a non-Intel GPU does not unblock it.**

Both halves of the reference-capture path are Intel-only by construction:

- `INTEL_DEBUG=bat` is a debug knob of Mesa's `anv` driver; it decodes batches
  `anv` itself submits. NVIDIA's proprietary driver is not Mesa and submits no
  `anv` batch. `nouveau` is Mesa but is a different driver with no Gen12
  command-stream encoding.
- `aubinator` / `intel_error_decode` / `intel_dump_gpu` ship in `intel-gpu-tools`
  and decode Intel GPU command streams specifically; there is no vendor-neutral
  equivalent, and the canonical packet schema in
  `boundary_cmdstream_canonicalize.spl` is a Gen12 opcode/dword-length schema.

So the hardware claim in this doc is accurate and remains accurate on a real-GPU
host. Note the second, hardware-independent blocker is unchanged and is the one
that could be worked without any silicon: there is still no command-stream
encoder under `src/os/drivers/gpu/board_vulkan/`, so even with Intel hardware the
candidate side stays `ProviderStatus.unavailable`. Status: OPEN, correctly
hardware-gated on the counterpart side, encoder-gated on the candidate side.

---

## 2026-08-17 — source half complete; live counterpart remains hardware-gated

The hardware-independent statement above is now stale. Current source contains
the canonical pure-Simple Gen12/Xe-LP encoder and boundary adapter:

- `encoder_intel_gen12.spl` owns checked MI/GFXPIPE header construction,
  Intel's `total_dwords - 2` length convention, and little-endian byte layout;
- `cmdstream_adapter_gen12.spl` decodes only confirmed fields, carries unknown
  GFXPIPE identities opaquely, and refuses unknown MI opcodes, truncated
  packets, or unconfirmed named mappings;
- `boundary_cmdstream_canonicalize.spl` remains the byte-exact canonical
  packet/order comparator and never treats its synthetic fixture as capture.

The source landed in `ab609ab9e5` and was hardened in `5942069084`. The five
owned source/unit specifications were also migrated from the unsupported
`describe("...")`/`it("...")` form to canonical SSpec syntax so the deployed
pure-Simple runner executes the evidence rather than failing in parsing:

```text
intel_gen12_encoder_header_spec.spl:      10 passed
intel_gen12_encoder_bytes_spec.spl:        4 passed
intel_gen12_encoder_hardening_spec.spl:   12 passed
cmdstream_encoder_roundtrip_spec.spl:      8 passed
cmdstream_boundary_intel_gen12_spec.spl:   7 passed
```

This closes only the host-fixable candidate/source half. `submit_implemented`
and hardware-verification flags remain false. A real Mesa `anv` batch captured
from Intel Gen12/Xe hardware and compared against the candidate is still
required; NVIDIA, a hand-authored stream, or the synthetic schema fixture is
not acceptable substitute evidence.
