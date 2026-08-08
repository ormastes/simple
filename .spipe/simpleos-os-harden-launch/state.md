# Feature: simpleos-os-harden-launch

## Raw Request
$sp_dev simple os harden for aarch(mac), x86 launch and sshd and wm launch.

## Task Type
feature

## Refined Goal
Harden SimpleOS launch evidence so x86_64 shell PATH execution reaches the real ring-3 loader, ARM64/macOS launch status is explicit instead of placeholder success, and SSHD plus window-manager launch are proven by executable SPipe/QEMU evidence.

## Acceptance Criteria
- AC-1: x86_64 shell execution resolves a PATH entry and dispatches through `fs_exec_spawn_ring3` into `x86_64_fs_exec_spawn`, with no seeded static pid or registry allowlist path.
- AC-2: x86_64 fs exec reads the exact resolved filesystem path into a nonzero identity-mapped raw blob before handoff, and fails closed when the blob is absent, stale, or not ELF.
- AC-3: x86_64 ring-3 handoff builds a real SysV AMD64 `argc/argv/envp/AT_NULL` initial stack frame before entering CPL3.
- AC-4: ARM64/macOS launch status is not reported as real user-mode execution unless an EL0 handoff exists; absent that handoff, ring-3 shell dispatch fails closed with a visible `arm64:no-ring3-handoff` marker.
- AC-5: SSHD launch and window-manager launch each have QEMU or physical-board evidence with serial/SSH markers showing the service started from the SimpleOS filesystem and did not use host-side fixed-command stubs.
- AC-6: Final verification runs the focused fs-exec checks plus `scripts/check/check-simpleos-hardening-evidence-matrix.shs`, and any changed `doc/06_spec`, `doc/07_guide`, skills, agents, or command docs are refreshed before a PASS claim.

## Scope Exclusions
Dynamic ELF interpreter/relocation support is out of scope for this pass; unsupported ELF forms must fail closed. Full ARM64 EL0 handoff may remain a blocker if recorded explicitly and not claimed as complete.

## Cooperative Review
N/A for this turn: active repo already has other agents and a concrete owner plan; this pass is a narrow x86 fs-exec implementation slice with ARM64 fail-closed status only.

## Phase
verified

## Log
- dev: Created state file with 6 acceptance criteria (type: feature).
- impl: Landed x86_64 shell PATH dispatch to ring3 fs-exec, exact-path raw FAT stream handoff, seeded-placeholder removal, SysV stack frame construction, and ARM64 ring3 fail-closed marker.
- verify: Focused source checks and `test/01_unit/os/kernel/loader/x86_64_fs_exec_spawn_spec.spl --mode=interpreter` pass for this slice.
- verify: Hardening matrix after the resolver fix reports `24/26`; x86 fs launch, SSHD exec/SMF, shared WM, QEMU MDI, and virtio GPU rows pass. Remaining rows were `formal_riscv_dual_track,byl_sby_artifact_audit`.
- verify: Targeted follow-up gates now pass: `sh scripts/check/check-riscv-formal-dual-track.shs` and `sh scripts/check/check-simpleos-byl-sby-artifacts.shs`.
- verify: Final aggregate `sh scripts/check/check-simpleos-hardening-evidence-matrix.shs` passes: `matrix_passed=26/26`, `mission_critical_release_status=pass`, `mission_critical_release_blockers=none`, `mission_critical_prereqs_status=ready`, `stale_reports=none`.
- docs: Refreshed `test/03_system/gui/simpleos_hardening_evidence_matrix_spec.spl` and `doc/06_spec/03_system/gui/simpleos_hardening_evidence_matrix_spec.md` for the stronger SSHD and QEMU MDI row contract.
- verify: `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` pass; `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.
