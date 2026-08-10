# Board Vulkan — Parallel SoC Lanes

**Date:** 2026-08-10
**Architecture:** `doc/04_architecture/os/vulkan/simpleos_board_vulkan_driver_architecture_2026-08-10.md`
**Reuses:** `doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md` (Wave 4 V1–V9)
**Rule:** `.claude/rules/board-runnable.md`

Wave 4 of the counterpart plan already owns the Vulkan *comparison* lanes (SPIR-V
providers, layer capture, software ICDs, venus bridge, QEMU guest bridge, receipts,
CTS). What it does not own is a **real GPU driver on real silicon**. That is what
these lanes are.

## Lanes (parallel, disjoint paths)

| Lane | GPU / board | Owns | Counterpart |
|---|---|---|---|
| B0 | venus / QEMU | `backend_virtio_venus.spl`, existing virtio-gpu entry | virglrenderer/vtest |
| B1 | Adreno A650 / RB5 | `backend_adreno.spl` | Mesa turnip |
| B2 | IMG BXE-4-32 / VisionFive 2 | `backend_img_bxe.spl` | Mesa powervr |
| B3 | Intel Gen12 / UP 4000 | `backend_intel_gen12.spl` | Mesa anv |
| B4 | shared | `soc_profile.spl`, `counterpart_plan.spl`, the core | — |

B4 freezes the profile struct and the three boundary IDs; B0–B3 then never edit a
shared file. A lane that needs a shared change files it against B4.

**Start B3 first.** It is x86-64, so the board shares the host toolchain and the
same GPU class exists on ordinary dev hosts — the cmdstream boundary is comparable
against anv with no board in the loop. B1 and B2 inherit whatever the B3 lane
proves about the core/backend split before spending on cross-compiled bring-up.

## Per-lane stage ladder

Each stage flips exactly one flag in the lane's profile, and no flag may be flipped
without its counterpart comparison green at that boundary.

1. **probe** — device detected over the lane's DRM UAPI. No flag; detection is not a
   driver claim.
2. **spirv** — module emitted for the target. Compare `vulkan.shader.spirv_binary@1`
   `byte_exact` against the counterpart. → `spirv_implemented`
3. **submit** — command stream encoded, submitted, fence signalled. Compare
   `vulkan.submit.command_stream@1` `byte_exact`. → `submit_implemented`
4. **readback** — device-origin frame. Compare `vulkan.present.readback_image@1`
   `image_exact`, with a GPU receipt required (submission, fence, device-origin
   readback, no fallback, no dropped events). → `readback_implemented`

Only when all three are true does `board_profile_is_board_runnable` return true for
that lane. The count is asserted in
`test/01_unit/os/vulkan/board_vulkan_counterpart_plan_spec.spl`, so no lane can
quietly claim board coverage.

## Lane obligations

Inherited verbatim from the counterpart plan's agent execution rules, with the two
that bite hardest restated:

- **A sabotage per lane.** Mutate the lane's encoder by one byte and prove the
  counterpart comparison goes red. A lane that only proves "the adapter ran" is
  rejected.
- **Unavailable is never pass.** No board, no Mesa build, no firmware → the source
  reports `unavailable` and the run is rejected. `counterpart_run_vacuity_failures`
  already enforces this; do not add a lane-local bypass.

## Blocked, and filed as such

- **B1/B2 hardware not present in this environment.** Both lanes can complete stages
  2 and 3 on a host cross-compile against Mesa; stage 4 needs the board. Stated here
  rather than implied, per the board-runnable rule.
- **B0 QEMU side unproven** — `virtio-gpu-gl` reportedly fails to load on the host
  in `doc/01_research/os/vulkan/venus_virtio_gpu_protocol_facts.md`. B0 stage 4 is
  blocked on that, independently of any board.
- **Encoders not written.** Stages 2–4 for all three board lanes are unimplemented;
  the profile flags say so and the spec asserts the zero.
