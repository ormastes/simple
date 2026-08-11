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
| B0 | venus / QEMU | `backend_virtio_venus.spl`, existing virtio-gpu entry | Mesa venus guest ICD (group `mesa`, corrected 2026-08-11) |
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
- **B0 QEMU side: venus is DEFINITIVELY UNAVAILABLE on this host** (measured
  2026-08-11, lane V1 — previously recorded here as "reportedly fails", which is
  what let it stay ambiguous for days). `qemu-system-x86_64` 8.2.2 cannot load
  `virtio-gpu-gl` at all: `hw-display-virtio-gpu-gl.so: undefined symbol:
  qemu_egl_display`. That symbol should be defined in the main binary when built
  `--enable-opengl`; `nm -D` finds it in neither the binary nor any of the six
  `.so` files in the installed `qemu-system-modules-opengl`. QEMU's own diagnosis
  is `-device virtio-gpu-gl: opengl is not available`. `venus=on` never even gets
  evaluated — the failure is one layer BELOW virgl/venus negotiation.
  `libvirglrenderer1` 1.0.0-1ubuntu2 *is* installed (correcting an earlier "not
  found" note), but it is moot. Root cause is host QEMU packaging, fixable only by
  a rebuilt or different QEMU package — no flag or device property helps. Filed:
  `doc/08_tracking/bug/host_qemu_virtio_gpu_gl_missing_egl_symbol_2026-08-11.md`.

  **Consequence for the whole plan:** this was the last route to a `submit` stage
  that did not require absent silicon. With it closed, stages 3 and 4 are
  unreachable on this host for all four backends — three for want of a GPU or a
  QEMU model, and B0 for want of a working OpenGL build. What remains achievable
  here is stage 2 (done, earned via Khronos validation) and hardening of code that
  executes as pure computation.

- **Directory fan-out now FAILS partly because of this effort** (measured
  2026-08-11): `sh scripts/check/check-directory-fanout.shs` reports 7 directories
  over the 10-file limit, and three are ours —
  `src/os/drivers/gpu/board_vulkan` (~20 files), `test/01_unit/os/vulkan`, and
  `doc/08_tracking/bug`. `structure.md` sets the limit; these lanes blew past it
  without noticing. Not reorganised here because a rename mid-flight across several
  active lanes is riskier than the violation, but it is a real debt this effort
  created, not an inherited one.
- **Encoders not written.** Stages 2–4 for all three board lanes are unimplemented;
  the profile flags say so and the spec asserts the zero.

## Provider inventory (lane L4)

Measured on the development host 2026-08-10/11. `artifact_hash` is a real
sha256 of the pinned library/binary; `version` and `license_spdx` are read from
the package, never invented. Descriptor:
`src/os/drivers/gpu/board_vulkan/provider_inventory.spl`. Spec:
`test/01_unit/os/vulkan/provider_inventory_spec.spl`.

| Provider | Version | `independence_group` | Usable for |
|---|---|---|---|
| host-mesa-anv (Intel) | 25.2.8-0ubuntu0.24.04.2 | `mesa` | B3 (Intel Gen12) counterpart |
| host-mesa-lavapipe | 25.2.8-0ubuntu0.24.04.2 | `mesa` | CPU-reference oracle for any lane, Wave-4 software-ICD lane |
| host-mesa-radv (AMD) | 25.2.8-0ubuntu0.24.04.2 | `mesa` | Differential peer only — no AMD board lane exists |
| host-mesa-nouveau | 25.2.8-0ubuntu0.24.04.2 | `mesa` | Differential peer only |
| host-mesa-asahi | 25.2.8-0ubuntu0.24.04.2 | `mesa` | Differential peer only — no Apple-silicon board lane exists |
| host-mesa-venus-guest (virtio) | 25.2.8-0ubuntu0.24.04.2 | `mesa` | B0 (venus/QEMU) guest-side driver |
| host-khronos-glslang | 15.1.0 | `khronos-glslang` | SPIR-V compilation reference for every lane's stage-2 comparison |
| host-nvidia-proprietary | 580.126.16 (driver, confirmed live via `nvidia-smi`) | `nvidia-proprietary` | The only genuinely independent second reference on this host |

**Independence finding.** All six Mesa-built drivers above share one upstream
tree (shader compiler, WSI, common infrastructure — confirmed by `dpkg -S` on
every pinned `.so`: all six resolve to package `mesa-vulkan-drivers`), so
selecting any subset of them — even all six — counts as exactly **one**
independent reference (`provider_inventory_independent_reference_count`
returns 1 for an all-Mesa selection, proven in the spec). glslang is a
separate upstream (`khronos-glslang`, package `glslang-tools`). NVIDIA's
proprietary ICD is closed-source and built from neither Mesa nor glslang
(`nvidia-proprietary`) — it is the **only** genuinely independent second
reference available on this host. A plan that wants two independent oracles
for the same boundary on this host has exactly one non-Mesa option: NVIDIA
proprietary (or glslang, for the SPIR-V-compilation boundary specifically,
which is a different stage from ICD execution).

**Not found on this host:** virglrenderer/vtest (the host-side venus
transport) — no `libvirglrenderer`/`vtest` binary was located. Recorded as
unavailable, not guessed, and excluded from `provider_inventory_all()`.

**Sabotage proofs run (see spec for the exact `Results:` lines):**
1. Empty `artifact_hash` → genuinely rejected by `provider_manifest_rejections`.
2. Wrong `abi_version` → genuinely rejected by `provider_manifest_rejections`.
3. Lavapipe's `independence_group` relabelled away from `mesa` → **not
   caught**. `independence_group` is a hand-authored declaration with no check
   against the host; the relabel silently inflates the independent-reference
   count for an all-Mesa selection from the honest 1 to 2, and nothing in
   `provider_inventory.spl` or `provider_manifest_rejections` notices. This is
   the failure `independence_group` exists to prevent, demonstrated as an open
   gap rather than a caught sabotage. Filed:
   `doc/08_tracking/bug/board_vulkan_independence_group_is_unverified_declaration_2026-08-11.md`,
   with a concrete unblock condition (derive the group from `dpkg -S` on the
   pinned artifact and assert it matches the declaration — every value in the
   table above was cross-checked that way by hand at authoring time, but
   nothing enforces it for a future edit).

## Per-architecture status (lane L6)

The three board-Vulkan targets map onto SimpleOS's three architectures:
Intel Gen12 (x86_64), Adreno (aarch64), IMG BXE-4-32 (riscv64). Lane L6 makes
the boundary record architecture-tagged (`environment_profile`, already on
`CounterpartPlan`/`ProvenanceReceipt`/`CounterpartRun` in
`src/lib/common/spec/evidence/counterpart/model.spl`) and adds the guard that
rejects comparing a capture from one architecture against another unless the
boundary is declared architecture-invariant. Ground truth measured directly
against this repo on 2026-08-10/11, not assumed:

| Arch | Compiler targets it today | QEMU real-firmware boot path (this repo) | Vulkan device path in-guest | What is missing |
|---|---|---|---|---|
| x86_64 | Yes — `platform_match.spl`/`codegen.spl` list x86_64 targets; this is the actively-driven host arch | Yes — OVMF pflash path documented and gated (`scripts/check/check-simpleos-x86-64-wm-qemu-readiness.shs`, `check-simpleos-wm-aqua-glyph-ovmf-evidence.shs`); real-firmware, not `-kernel` | virtio-gpu/venus guest path exists (`backend_virtio_venus.spl`), explicitly marked QEMU-only in the counterpart plan — **not** Intel Gen12 bare-metal | Intel Gen12 native (non-virtio) board driver: not present. Only the QEMU-only venus path is proven |
| aarch64 | Partial — aarch64 appears in type/codegen tables, but no board-Vulkan backend file (`backend_adreno.spl`) has been verified to build+run end to end on this arch | **No** — no OVMF/EDK2-AAVMF real-firmware doc or gate was found under `doc/03_plan/os/simpleos/hw_qemu/`; only a Limine-framebuffer check (`check-simpleos-aarch64-limine-framebuffer.shs`) and an ARM QEMU fs/toolchain verification doc exist, neither is an EDK2-AAVMF real-firmware boot record. The board-runnable rule's claim that aarch64 lacks an EFI-stub could not be disproven by this search — treated as **still true** until a lane produces the missing record | None found — `backend_adreno.spl` exists as a source file (soc profile / capability description) but no in-guest device enumeration evidence was located | EDK2/AAVMF real-firmware boot path (rule-mandated), and any in-guest Vulkan device path for Adreno. Both are open blockers, not silently assumed |
| riscv64 | Yes for general codegen; board-Vulkan-specific riscv64 code exists only as `backend_img_bxe.spl` (soc profile), unverified end to end | Partial — OpenSBI-related scripts exist (`scripts/os/build_opensbi_rv64_soc.shs`) and a hosted-QEMU riscv64 plan doc (`simpleos_rv64_hosted_qemu.md`), but no evidence was located in this pass that the OpenSBI path has been run as the REAL-firmware proxy (vs. `-kernel`) specifically for a Vulkan-capable guest | None found — no IMG BXE-4-32 in-guest device path evidence located | Confirmation that the existing OpenSBI script boots via real-firmware semantics (not `-kernel`) for a Vulkan-relevant guest, plus any IMG BXE device path |

**Conclusion, stated plainly:** only x86_64 has both a real-firmware QEMU
boot path AND an in-guest GPU device path proven in this repo today, and even
that device path is virtio-gpu/venus (QEMU-only), not native Intel Gen12 —
so x86_64 itself is not yet board-runnable for Vulkan, per
`.claude/rules/board-runnable.md`. aarch64 and riscv64 lack a verified
real-firmware boot path entirely for this purpose. **A boundary capture that
executes only on x86_64 today reports arch coverage of 1, not 3** — this is
exactly what `boundary_arch.arch_coverage_count` in
`src/os/drivers/gpu/board_vulkan/boundary_arch.spl` enforces, and exactly
what the sabotage proof in
`test/01_unit/os/vulkan/cross_arch_boundary_substitution_spec.spl` demonstrates
going red when a caller claims otherwise. This gap (no aarch64 EDK2-AAVMF
real-firmware path, no riscv64 real-firmware-confirmed Vulkan guest) is filed
as a blocker rather than implied as done.
