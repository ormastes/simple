# SimpleOS Board Vulkan Driver — Architecture

**Date:** 2026-08-10
**Answers:** `doc/08_tracking/bug/simpleos_vulkan_board_gap_venus_is_qemu_only_2026-08-06.md`
**Rule:** `.claude/rules/board-runnable.md`
**Test infra reused:** `doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md` (Wave 4)

## The correction

The prior plan (`simpleos_vulkan_render_backend_plan.md`) made virtio-gpu + venus
*the* architecture. venus is a VM device interface, so that plan can never reach a
board. This architecture inverts the relationship: a **SoC-neutral board Vulkan
core** with **one thin backend per GPU**, and venus is demoted to one of those
backends, flagged `qemu_only`.

```
                 SPIR-V module + draw/dispatch description
                                  |
                    SoC-neutral board Vulkan core
       (pipeline state, descriptor layout, memory plan, sync plan)
                                  |
     +-------------+--------------+--------------+--------------+
     | virtio/venus|  Intel Gen12 |    Adreno    |  IMG BXE-4-32|
     |  (QEMU only)|    i915      |   drm-msm    |  drm-powervr |
     +-------------+--------------+--------------+--------------+
       counterpart:   counterpart:   counterpart:   counterpart:
       virglrenderer  Mesa anv       Mesa turnip    Mesa powervr
```

Backends are one file each under `src/os/drivers/gpu/board_vulkan/` precisely so
the three board lanes proceed in parallel without touching one another.

## Honesty gate, not a note

`soc_profile.spl` makes the board gap a measurement instead of prose.
`board_profile_false_claim` rejects a profile that claims a later pipeline stage
without the stage under it, or that claims physical hardware while being a VM
interface. `board_profile_is_board_runnable` requires real silicon **and**
`spirv + submit + readback` all implemented.

Today all four backends declare every stage `false`, so the board-runnable count
is legitimately **0** — asserted in
`test/01_unit/os/vulkan/board_vulkan_counterpart_plan_spec.spl`. When a lane
lands a stage it flips one flag, and the count moves for a reason.

## Comparison against the open-source counterpart

No new comparison machinery. The counterpart conformance framework already
exists (`src/lib/*/spec/evidence/counterpart/`) with an N-way matrix engine,
relation engine, independence grouping, converter loss enforcement and a GPU
receipt gate. This architecture only adds **plan descriptors**
(`counterpart_plan.spl`), per plan rule 9 ("add a descriptor rather than editing
central registries").

Three boundaries, chosen so correctness does not depend on hardware:

| Boundary | Relation | Needs board? | Compared against |
|---|---|---|---|
| `vulkan.shader.spirv_binary@1` | `byte_exact` | no | SPIRV-Tools + Mesa's compiler front |
| `vulkan.submit.command_stream@1` | `byte_exact` | no (ISA encoder only) | turnip / anv / powervr encoder |
| `vulkan.present.readback_image@1` | `image_exact` | **yes** | same driver on the same silicon |

Only readback requires a device-origin GPU receipt. Gating the SPIR-V boundary on
hardware would make the portable correctness lane depend on a board, which the
counterpart CI matrix forbids (tiers 0–4 carry correctness; 5–7 prove real
execution).

**Independence groups matter here.** turnip, anv and powervr are all Mesa, so they
are group `mesa` — three Mesa drivers are *one* independent reference, not three.
venus's counterpart is virglrenderer, a separate group. Any run whose executed
sources collapse into one group is rejected as vacuous by
`counterpart_run_vacuity_failures`.

## Migration of existing Vulkan work

| Existing | Disposition |
|---|---|
| `src/os/drivers/gpu/virtio_gpu_entry.spl`, `src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl` | Reclassified as the `qemu-virtio` backend (`backend_virtio_venus.spl`). Kept, not deleted — QEMU is still the dev harness. |
| `doc/0{1,4,5}/os/vulkan/*venus*` | Still valid as venus-backend documents; no longer the board architecture. |
| `src/compiler/70.backend/backend/vulkan/spirv_builder.spl` | Reused unchanged. It is the SoC-neutral SPIR-V producer, and it is the candidate side of the SPIR-V boundary. |
| `src/os/drivers/gpu/gpu_vendor_probe.spl` | Probe stubs stay as device *detection*; they are not driver claims. `board_vulkan_backends()` is the driver-capability table. |
| Existing host Vulkan engine2d/engine3d backends | Untouched. They are host-side render lanes, not SimpleOS drivers. |

## What is deliberately not built yet

Register-level command encoding for three GPUs is the bulk of the work and is
scoped per lane in the plan document. This change lands the frame that makes each
lane independently verifiable and makes over-claiming fail — not the encoders.
