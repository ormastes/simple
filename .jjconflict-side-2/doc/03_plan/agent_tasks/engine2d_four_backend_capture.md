# Engine2D Four-Backend Capture Agent Tasks

Related WM/Web material plan:
`doc/03_plan/agent_tasks/wm_glass_theme_host_simpleos.md`, with architecture
and detail design in `doc/04_architecture/wm_glass_theme_host_simpleos.md` and
`doc/05_design/wm_glass_theme_host_simpleos.md`. That plan produces semantic
material input; this plan alone owns backend/device/capture admission.

Base revision: `a6497a60` working-copy snapshot on 2026-07-25. The shared
checkout also contains unrelated MCP, theme, parser, and wrapper work owned by
other sessions; none of those files belong to this plan.

| Lane | Agent | Owned range | Deliverable |
|---|---|---|---|
| Vulkan | `/root/vulkan_backend` | Vulkan backend/session/font and Vulkan-only wrappers/specs/evidence | Device-readback Vulkan capture + target-side events |
| Metal | `/root/metal_backend` | Metal backend/session/font and Metal-only wrappers/specs/evidence | Device-readback Metal capture + target-side events |
| QEMU ARM64 SIMD | `/root/qemu_arm_simd` | ARM64 SimpleOS compositor/runtime and ARM-only QEMU wrappers/specs/evidence | ARM SIMD capture, counters, scalar parity, guest events |
| Host SIMD + QEMU x86 + merge | `/root` | shared Engine2D, host SIMD, x86 QEMU, `wm_compare`, comparison, docs | Host/x86 captures and integrated comparison |

Shared files (`engine.spl`, `backend.spl`, Draw IR schema, and `wm_compare`) are
owned only by the merge lane. Backend agents report required common changes.

No lane may commit, rebase, move bookmarks, or push independently. The merge
owner reviews every lane, runs the aggregate comparison once, commits only the
path-limited accepted changes, then performs the file-count-guarded `jj` sync.

Lower-model sidecars: `N/A`; the available agents are normal-capability agents
with narrow platform ownership. Merge owner and final highest-capability
reviewer: `/root`.

Frozen types, helpers, and manual steps are defined in the detail design.
Unsupported live behavior must use an explicit failing assertion or rejection
status until implemented.

## Execution status

- [x] Requirements, architecture, detail design, system-test plan, and frozen
  interfaces exist.
- [x] Four active worker lanes assigned with non-overlapping ownership.
- [x] Vulkan inspected: provider PASS; native driver/capture FAIL before receipt.
- [x] Metal inspected: source contract PASS; admissible native executable absent.
- [x] Host SIMD inspected: NEON hits/parity PASS; facade timeout and no durable
  scene/event capture.
- [x] QEMU x86_64 attempted once: native build timed out before ELF/QEMU.
- [x] QEMU ARM64 inspected: readiness/preflight PASS; target build and live
  capture FAIL. Runtime parity and guest receipt implementation added.
- [x] Cross-backend comparison attempted and rejected because no pair has two
  admissible live capture records.
- [ ] Focused contract verification is blocked by the full data volume and
  unrelated active compiler/parser changes; do not push as verified.
- [x] GitHub fetched on 2026-07-25 (`main`/`main@origin` at `debc189e0047`).
  Rebase/commit/push intentionally deferred until the focused gate passes.
