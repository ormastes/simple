# Engine2D Four-Backend Capture Agent Tasks

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

## Refresh 2026-09-05

The focused contract this plan was waiting on now exists:
`test/03_system/gui/wm_compare/engine2d_four_backend_capture_spec.spl` (8 `it`s,
0 `fail(` placeholders) over `src/app/wm_compare/backend_2d_capture_evidence.spl`
(`backend_2d_validate_capture`, `backend_2d_compare_capture`). A green run of it
is not recorded on this host, so the open box above stays open; the lane
directories `/root/vulkan_backend` etc. named in the table were paths on the
authoring host and do not exist on this one (`ls -d /root/vulkan_backend
/root/metal_backend` → No such file or directory, 2026-09-05).

## Acceptance

Runnable oracles for the remaining open boxes: `test/03_system/plan_acceptance/engine2d_four_backend_capture_spec.spl`
(tagged `@tag:in-development`; one `it` per open box — see
`doc/03_plan/agent_tasks/plan_remains_acceptance_2026-09-05.md`).
