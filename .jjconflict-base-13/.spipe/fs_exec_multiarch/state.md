# Feature: fs_exec_multiarch

## Raw Request
with spipe dev skill, harden simple os file-system-based file execution on x86, riscv, aarch64; small model-rated tasks, parallel agents, higher-model review after.

## Task Type
code-quality

## Refined Goal
FS-loaded execution proof contracts are fail-closed and arch-uniform (x86_64, riscv32/64, arm64), and the kernel loader rejects malformed images with bounds-checked parsing.

## Acceptance Criteria
- AC-1: A written gap map exists of fs-exec proof/marker coverage per arch (x86_64, riscv64, riscv32, arm64) derived from qemu_runner*.spl and contracts.
- AC-2: Resident-manifest fallback is rejected as completion evidence on riscv and arm lanes with the same fail-closed semantics as x86_64, via shared contract logic (no per-arch copy drift); specs prove rejection per arch.
- AC-3: Kernel loader SMF/image load path bounds-checks sizes/offsets and rejects truncated images with an error; unit specs in test/01_unit/os/kernel/loader/.
- AC-4: All touched contract specs pass in interpreter mode; no QEMU live lane is newly required.

## Scope Exclusions
No changes to src/os/apps/** or src/lib/**. No new QEMU scenarios; contract/loader level only. desktop_qemu_contract.spl marker strings must not diverge.

## Phase
implement-done

## Gap Map (AC-1)
Derived from qemu_runner_part5.spl and x86_64_fs_loaded_launch_proof.spl:

| Arch   | Required-marker source                     | Fallback rejection before this change |
|--------|--------------------------------------------|---------------------------------------|
| x86_64 | x86_64_fs_loaded_marker_contract / has_resident_manifest_fallback | YES — inline in launch_proof.spl |
| riscv64 | _catalog_lane_for_scenario → required_serial_markers | NO — _scenario_serial_accepts_completion only checks markers |
| riscv32 | reuses arm fn / catalog lane               | NO — same gap                         |
| arm64  | arm64_wm_ramfb_required_marker_fragments / catalog lane | NO — same gap              |
| arm32  | arm_fs_exec_required_marker_fragments / catalog lane | NO — same gap              |

Gap: _scenario_serial_accepts_completion (line 649) only loops over required markers; no arch lane calls has_resident_manifest_fallback. The shared contract introduced in this change provides the fix; arm/riscv lanes must wire fs_exec_serial_rejects_fallback into their serial-acceptance path.
RESOLVED (orchestrator follow-up, same day): qemu_runner_part5.spl now wires fs_exec_serial_has_fallback into both _scenario_serial_accepts_completion and qemu_scenario_serial_acceptance_reason ("resident-fallback-rejected" reason) for all fs-exec lane names via pub fs_exec_lane_name_rejects_resident_fallback; spec test/01_unit/os/qemu_runner_fs_exec_fallback_acceptance_spec.spl (9 pass). Catalog-lane scenario constructors crash in interpreter mode (pre-existing) — filed doc/08_tracking/bug/interp_simpleos_lane_contract_crash_2026-06-13.md; lane coverage is name-based + arm64-wm-ramfb end-to-end.

## Log
- dev: Created state file with 4 acceptance criteria (type: code-quality)
- implement-done (Track C): Gap map recorded (AC-1). Shared arch-neutral fallback contract created (src/os/fs_exec_fallback_contract.spl). x86_64_fs_loaded_launch_proof.spl delegated to shared contract (no drift, AC-2). _smf_copy_range in smf.spl now guards with in_range before loop; byte_utils.spl in_range promoted to pub (AC-3). New specs: smf_bounds_spec.spl (13 pass), fs_exec_fallback_contract_spec.spl (24 pass, covers all 5 arch lanes). Existing x86_64_fs_loaded_launch_proof_spec.spl: 2 pass. All touched files check-clean. Pre-existing smf_spec.spl failures (2) are unrelated to this change (confirmed via baseline run). AC-4 satisfied — no QEMU lanes required.
