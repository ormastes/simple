# Feature Expert — Board Vulkan (boundary-comparison harness)

## Role

Own process knowledge for the SimpleOS board-Vulkan work: a boundary-comparison
harness that checks candidate SimpleOS Vulkan-adjacent boundaries (device
enumeration, SPIR-V, command-stream, readback) against genuinely executed
counterpart references (lavapipe `vulkaninfo`, glslang, real hardware ICDs) on
x86_64/aarch64/riscv64. It is **not** a Vulkan driver — see the load-bearing
fact below before writing anything that assumes one exists.

This feature is a consumer of the
[counterpart_conformance](../counterpart_conformance/skill.md) methodology
(differential comparison against upstream references, independence groups,
real executed counterparts) applied to the GPU/board domain. Read that skill
first for the shared vocabulary (`independence_group`, "unavailable is never
PASS", real-execution-vs-literal-substitution) before touching this feature.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Feature Links

- Architecture: `doc/04_architecture/os/vulkan/simpleos_board_vulkan_driver_architecture_2026-08-10.md`
- Related architecture: `doc/04_architecture/os/vulkan/simpleos_pure_simple_venus_driver.md`,
  `simpleos_pure_simple_venus_driver_tldr.md`, `simpleos_vulkan_render_backend_plan.md`
- Plan (parallel SoC lanes): `doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md`
- Source: `src/os/drivers/gpu/board_vulkan/`
  - Backends (all non-functional, see facts below): `backend_adreno.spl`,
    `backend_img_bxe.spl`, `backend_intel_gen12.spl`, `backend_virtio_venus.spl`
  - Boundary comparators: `boundary_enumeration_model.spl` +
    `boundary_enumeration_provider.spl`, `boundary_spirv_canonicalize.spl` +
    `boundary_spirv_provider.spl`, `boundary_cmdstream_canonicalize.spl`,
    `boundary_readback_gate.spl` + `boundary_readback_lavapipe_provider.spl`
  - Independence/inventory: `provider_inventory.spl`, `provider_nvidia.spl`,
    `soc_profile.spl`
  - Plan/ledger: `counterpart_plan.spl`, `corpus_cases.spl`, `corpus_ledger.spl`,
    `corpus_runner.spl`
- Specs: `test/01_unit/os/vulkan/` — `board_vulkan_counterpart_plan_spec.spl`,
  `cmdstream_boundary_intel_gen12_spec.spl`,
  `cross_arch_boundary_substitution_spec.spl`, `cts_corpus_spirv_binary_spec.spl`,
  `device_enumeration_boundary_spec.spl`,
  `headless_readback_capture_lavapipe_spec.spl`,
  `nvidia_independent_reference_gate_spec.spl`, `provider_inventory_spec.spl`,
  `readback_boundary_gate_spec.spl`, `spirv_boundary_glslang_spec.spl`

## Load-bearing facts (2026-08-10)

1. **There is NO SimpleOS Vulkan driver, on any architecture.** Every backend
   in `backend_*.spl` declares `spirv/submit/readback = false`, and
   `board_runnable_count()` is asserted to be **0**. Nothing in this feature
   proves a driver — it proves that a *comparison harness* around a
   not-yet-written driver is itself trustworthy (rejects wrong answers, uses
   real counterparts, doesn't fabricate independence).
2. **venus/virtio-gpu is ONE backend flagged `qemu_only`, not "the"
   architecture.** Do not treat venus as the SimpleOS Vulkan strategy — it is
   one candidate path among several SoC backends (Adreno, IMG BXE, Intel
   Gen12).
3. **Mesa's venus GUEST ICD is independence group `mesa`, NOT
   `virglrenderer`.** virglrenderer is the HOST-side transport for
   virtio-gpu/venus and is not installed on this host at all. Tagging the
   venus guest ICD as `virglrenderer` double-counts references that are
   actually all-Mesa. Check `provider_inventory.spl` / `provider_nvidia.spl`
   for the current group assignment before adding a new provider.
4. **All six Mesa ICDs on this host resolve to ONE package**
   (`mesa-vulkan-drivers`, verified by `dpkg -S`), so any all-Mesa provider
   selection is exactly one independent reference, never six. **NVIDIA
   proprietary (580.126.16) is the only genuinely independent ICD reference on
   this host.** `khronos-glslang` (the `glslang` package) is independent only
   for the SPIR-V-compilation boundary, not for enumeration/cmdstream/readback.
5. **Canonicalize by EXPLICIT rule, never by heuristic reachability
   filtering.** A reachability/unreferenced-id filter in an earlier draft
   deleted `OpLabel` and `OpExtInstImport`, which let a candidate emitting no
   basic-block label still pass a `byte_exact` SPIR-V comparison. The same bug
   class recurred independently in the cmdstream lane as an address-mask wide
   enough to erase the operand actually under test. When adding or reviewing a
   canonicalizer in `boundary_spirv_canonicalize.spl` /
   `boundary_cmdstream_canonicalize.spl`, require it to state which fields it
   normalizes and prove — via a spec that mutates the field under test — that
   the mutation is still caught.
6. **`process_run_bounded`
   (`src/lib/nogc_sync_mut/io/process_ops.spl:76`) DOES work from a spec
   lane.** Three separate lanes in this feature's history wrongly concluded it
   was unavailable and substituted hand-authored literal output for what the
   counterpart tool actually printed — silently turning a real-execution gate
   into a fabricated one. Before adding a new counterpart call, confirm you
   are invoking `process_run_bounded` (or an equivalent real subprocess call)
   and not hand-typing the expected counterpart output.
7. **A red verdict with `executed=0` is a parse error; one with `timeout=1`
   is a harness-budget kill.** Neither is evidence in either direction for the
   thing being tested. The test daemon caps a worker at 120s
   (`src/app/test_daemon/daemon.spl:395`); use
   `--no-session-daemon --timeout <secs>` to bypass it for longer real-tool
   invocations (e.g. `vulkaninfo`, `dpkg -S` scans).
8. **Absence-claims from a single-directory scan are not absence.** An
   aarch64 real-firmware boot record already existed under
   `doc/08_tracking/bug/`; a lane that searched only
   `doc/03_plan/os/simpleos/hw_qemu/` reported it missing, and that wrong
   claim was repeated downstream. Before asserting "no evidence of X", grep
   `doc/08_tracking/` (not only the plan tree) and say which directories were
   actually searched.
9. **Real-firmware boot gates for all three arches are proven** (riscv64 via
   OpenSBI `-bios`, never `-kernel`; x86_64/aarch64 similarly via their
   real-firmware proxies) — per this feature's board-runnable requirement
   (`.claude/rules/board-runnable.md`). This is boot-gate evidence only; it
   does not imply any Vulkan capability on the board (see fact 1).

## No dedicated layer expert exists for this feature

There is no `layer_expert/` entry for GPU/board-driver work — the closest
existing layers (`os_kernel_exec`, `os_compositor`) do not claim this scope,
and this feature's own harness code owns its layer boundaries directly (the
`boundary_*.spl` files in the source list above ARE the contract). Do not fold
this into `os_kernel_exec` or `os_compositor` without an explicit decision —
neither currently references board_vulkan and this entry does not add such a
link, to avoid asserting an ownership relationship nobody has reviewed.

## Verification commands

```bash
bin/simple run test/01_unit/os/vulkan/<spec>.spl
# Real-counterpart specs invoke external tools (vulkaninfo, dpkg, glslang) —
# use --no-session-daemon --timeout <secs> if a run risks the 120s daemon cap.
```

Every boundary comparator must ship a sabotage spec that mutates the exact
field under test and proves the comparator still goes red (fact 5).

## Update Rule

Update this file in the same change as any board_vulkan work: new backends,
new independence-group findings, new canonicalizer rules, and corrections to
the facts above. If a fact above is later found wrong, replace it in place and
say so — do not leave a stale claim standing next to its correction.
