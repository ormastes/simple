# Feature: gpu-full-render-offload

## Raw Request
spipe dev skill, complete gpu full...md and carefull crash

## Task Type
feature

## Refined Goal
Complete the GPU Full Render Offload MDSOC+ plan into an actionable SPipe lane with testable acceptance criteria, current artifact mapping, and crash-safe verification boundaries for GUI, Web, and Simple 2D GPU rendering.

## Acceptance Criteria
- AC-1: `doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md` identifies the current phase status, owned deliverables, evidence gates, and remaining blockers without leaving the lane as only `proposed`.
- AC-2: The lane records authoritative artifact paths for architecture, design, system specs, generated spec docs, implementation owners, evidence reports, and process guides.
- AC-3: The plan distinguishes CPU-owned UI semantics from GPU-owned rendering/readback and requires strict failure for requested GPU backends when unavailable.
- AC-4: The plan includes crash-safe verification rules that prevent repeated runaway checks, broad dirty-worktree commits, and silent fallback evidence.
- AC-5: Existing or new SPipe/SSpec evidence for GUI, Web, and Simple 2D GPU boundary behavior is linked from the plan, or missing evidence is explicitly listed as required work.
- AC-6: Before handoff, targeted guards confirm no executable `*_spec.spl` files live under `doc/06_spec`, and any verification command run in this session is not repeated after a pass.
- AC-7: Windows Vulkan setup state records runtime, SDK-tool, Chrome, Electron, and DirectX readiness separately, and does not treat browser install or DirectX availability as Vulkan-backed browser proof.

## Scope Exclusions
- Completing every Vulkan, Metal, D3D, WebGPU, CUDA, HIP, SYCL, and OpenCL backend implementation is outside this dev-refinement step.
- Bulk committing the current dirty worktree is outside this lane unless explicitly requested after the owned file set is reviewed.
- Re-running broad full-tree test suites after a pass is excluded to avoid the prior crash/runaway failure mode.

## Phase
dev-done

## Log
- dev: Created state file with 6 acceptance criteria (type: feature).
- dev: Updated `doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md`
  with active lane status, artifact map, crash-safe verification rules, and
  current evidence gaps.
- dev: Verified generated spec layout guard reports `0` executable
  `*_spec.spl` files under `doc/06_spec`.
- dev: Fixed and verified Windows `/sp_dev` wiring check:
  `powershell -ExecutionPolicy Bypass -File scripts\setup\install-spipe-dev-command.ps1 --check`
  reports `STATUS: PASS spipe-dev-command wiring`.
- dev: Crash safety note: the workspace still has a growing exact-match
  runaway process tree for `"bin/simple" src/app/repl/main.spl`; avoid broad
  Simple checks until that external process state is cleaned up.
- dev: Completed the planning-lane handoff in
  `doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md` by adding
  `Plan Completion Contract`, `Implementation Task Queue`, and
  `Done-Marking Rules`.
- dev: Verified the new plan sections with a scoped `Select-String` check.
  Did not rerun the previously passing `doc/06_spec` layout guard in this
  session.
- dev: Recorded Windows setup evidence: `vulkaninfo --summary` passes,
  Chrome and Electron are installed, `glslangValidator`, `spirv-as`, and `dxc`
  are missing from `PATH`, and the Vulkan SDK winget installer was canceled at
  the administrator prompt.
