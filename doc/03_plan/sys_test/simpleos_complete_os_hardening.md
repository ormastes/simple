# System Test Plan: SimpleOS Complete OS Hardening

## Purpose

Prove REQ-001–REQ-020 and NFR-001–NFR-014 through live, fail-closed, nonce-bound evidence. A missing prerequisite produces a `BLOCKED` row with a resume plan and fails the umbrella; no scenario calls `skip()` or converts staging/source presence into PASS.

## Executable specifications

| Spec | Scope |
|---|---|
| `test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl` | Extend the canonical live umbrella across all selected rows; do not create a `test/system` compatibility copy |
| `test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.spl` | boot, three filesystems, durability/corruption, authenticated execution, invalidation |
| `test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.spl` | Simple/LLVM roles, expanded tools, lifecycle, web/DB/SSH profiles and confinement |
| `test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl` | WM interactions/readback, performance, fuzz, 24-hour soak, 1,000-cycle lifecycle |
| `test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl` | REQ-017 production-owner host behavior plus fail-closed canonical QEMU visual capture binding |
| `test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.spl` | ledger, ownership/duplication, freshness, traceability, manual-quality gates |

Mirrors live under `doc/06_spec/03_system/os/...` after removing the leading `test/`. No executable `.spl` belongs under `doc/06_spec`.

## Frozen scenario vocabulary

Visible helpers:

- `step_boot_target`
- `step_mount_filesystem`
- `step_launch_from_filesystem`
- `step_probe_protocol`
- `step_compile_and_run_hello`
- `step_exercise_window_manager`
- `step_measure_resource_budget`

Setup/checkers:

- `setup_simpleos_arch_fixture`
- `check_simpleos_capability_matrix`
- `check_simpleos_filesystem_conformance`
- `check_simpleos_filesystem_exec`
- `check_simpleos_server_protocols`
- `check_simpleos_toolchain_fs`
- `check_simpleos_wm`
- `check_simpleos_perf_duplication`

Every unresolved helper resolves the REQ/NFR to one executable acceptance owner,
constructs a complete `SimpleOsCapabilityStatus.Blocked` candidate with an exact
expected receipt path and resume command, and validates that candidate through
`simpleos_capability_candidate_validate`. It then emits `BLOCKED[<ID>:<case>]`,
so traceability can never count as acceptance. No no-op, fabricated fixture,
fixed responder, tautological assertion, or todo-pass helper is allowed.

### Acceptance-owner bindings

The binding source of truth is
`test/helpers/simpleos_complete_os_hardening_steps.spl`. Expected evidence is
always the exact file
`build/test-artifacts/simpleos_complete_os_hardening/<ID>/<case>.receipt.sdn`;
`<case>` is `happy`, `boundary`, or `rejection`.

| IDs | Executable acceptance owner |
|---|---|
| REQ-001, NFR-007, NFR-012 | `test/01_unit/os/services/evidence/capability_ledger_spec.spl` |
| REQ-002, NFR-001 | `test/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.spl` |
| REQ-003 | `test/03_system/os/filesystem_system_spec.spl` |
| REQ-004 | `test/02_integration/os/port/make_os_disk_fat32_integrity_spec.spl` |
| REQ-005, NFR-011 | `test/02_integration/storage/dbfs/dbfs_durable_commit_spec.spl` |
| REQ-006 | `test/01_unit/os/services/nvfs/nvfs_durable_roundtrip_spec.spl` |
| REQ-007, NFR-006 | `test/01_unit/lib/common/contracts/execution/simpleos_executable_admission_v1_spec.spl` |
| REQ-008, REQ-010, REQ-020, NFR-013 | `test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl` |
| REQ-009 | `test/03_system/os/simpleos_deploy_image_simple_toolchain_spec.spl` |
| REQ-011 | `test/03_system/os/os_shell_userland_tools_spec.spl` |
| REQ-012, REQ-013, REQ-014, REQ-016, NFR-010 | `test/03_system/os/server/simpleos_server_execution_matrix_spec.spl` |
| REQ-015 | `test/03_system/os/os_ssh_spec.spl` |
| REQ-017 | `test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl` |
| REQ-018, NFR-002, NFR-003 | `test/03_system/os/wm/simple_wm_performance_spec.spl` |
| REQ-019, NFR-008 | `test/03_system/app/cli/duplicate_check_contract_spec.spl` |
| NFR-004, NFR-005, NFR-009 | `test/03_system/quality/code_quality/os_harden_runtime_evidence_spec.spl` |
| NFR-014 | `test/02_integration/app/spipe_docgen_regeneration_live_spec.spl` |

## Traceability

Abbreviations: `AF` = `simpleos_complete_os_hardening_arch_fs_exec_spec.spl`; `ST` = `simpleos_complete_os_hardening_servers_tools_spec.spl`; `WP` = `simpleos_complete_os_hardening_wm_perf_campaign_spec.spl`; `EM` = `simpleos_complete_os_hardening_evidence_manual_spec.spl`. Executable prefix is `test/03_system/os/simpleos/feature/`; manual prefix is `doc/06_spec/03_system/os/simpleos/feature/`. Every row has happy, edge/boundary, and fail-closed rejection scenarios (3 each). The exact command is `bin/simple test <executable-path> --mode=interpreter`; release evidence additionally uses the canonical umbrella and whole suite. All listed pairs now have production-validator-backed `BLOCKED-TRACEABILITY`; they remain non-coverage until the bound acceptance owner produces and the evidence service admits every exact receipt, and an admitted pure-Simple SPipe runtime regenerates zero-stub manuals.

| ID | Spec/manual | Cases | Coverage/status |
|---|---|---:|---|
| REQ-001 | EM / EM | 3 | ledger complete, blank row, unbound owner; BLOCKED-TRACEABILITY |
| REQ-002 | AF / AF | 3 | three-target identity, boundary classification, mismatch; BLOCKED-TRACEABILITY |
| REQ-003 | AF / AF | 3 | portable core, extension boundary, unsupported capability; BLOCKED-TRACEABILITY |
| REQ-004 | AF / AF | 3 | FAT32 interoperability, limit edge, malformed/cyclic media; BLOCKED-TRACEABILITY |
| REQ-005 | AF / AF | 3 | DBFS commit/reboot, replay bound, corrupt WAL; BLOCKED-TRACEABILITY |
| REQ-006 | AF / AF | 3 | NVFS persistence, offset/capacity edge, mirror/no-op rejection; BLOCKED-TRACEABILITY |
| REQ-007 | AF / AF | 3 | authenticated open handle, revocation race, unsigned/wrong ISA; BLOCKED-TRACEABILITY |
| REQ-008 | AF / AF | 3 | three-backend exec, nonzero/cancel edge, invalidation/fallback rejection; BLOCKED-TRACEABILITY |
| REQ-009 | ST / ST | 3 | separate Simple roles, alias boundary, host/seed/fixed-command rejection; BLOCKED-TRACEABILITY |
| REQ-010 | ST / ST | 3 | guest C/C++, runtime boundary, staged/host fallback rejection; BLOCKED-TRACEABILITY |
| REQ-011 | ST / ST | 3 | supported tool operation, partial status, placeholder/error rejection; BLOCKED-TRACEABILITY |
| REQ-012 | ST / ST | 3 | lifecycle start/drain, quota boundary, stale/replayed result; BLOCKED-TRACEABILITY |
| REQ-013 | ST / ST | 3 | H1/H2/H3 live probe, negotiated extension, helper-only rejection; BLOCKED-TRACEABILITY |
| REQ-014 | ST / ST | 3 | DB/RESP operation, mandatory extension, malformed/downgrade rejection; BLOCKED-TRACEABILITY |
| REQ-015 | ST / ST | 3 | SSH auth/session/exec, rekey/channel bound, hardcoded/downgrade rejection; BLOCKED-TRACEABILITY |
| REQ-016 | ST / ST | 3 | capability confinement, configured limit, secret/exhaustion/traversal rejection; BLOCKED-TRACEABILITY |
| REQ-017 | `os/wm/simpleos_wm_behavior_evidence_spec.spl` / mirrored manual | 6 | host-fixture focus/stack, close fallback, bounded damage, input routing, composited pixels, recovery plus live-guest capture binding; live row remains BLOCKED unless the canonical wrapper returns a correlated fresh bundle |
| REQ-018 | WP / WP | 3 | hot-path counters, cache edge, scan/spawn/stale-cache rejection; BLOCKED-TRACEABILITY |
| REQ-019 | EM / EM | 3 | owner map, transfer classification, duplicate/raw-pointer rejection; BLOCKED-TRACEABILITY |
| REQ-020 | EM / EM | 3 | traceability/manual flow, blocked-row detail, stale/fabricated evidence rejection; BLOCKED-TRACEABILITY |
| NFR-001 | EM / EM | 3 | QEMU/native-host/physical rows, identity edge, substitution rejection; BLOCKED-TRACEABILITY |
| NFR-002 | WP / WP | 3 | absolute budgets, boundary equality, >5% regression; BLOCKED-TRACEABILITY |
| NFR-003 | WP / WP | 3 | ten samples, CV boundary, noisy/non-comparable rejection; BLOCKED-TRACEABILITY |
| NFR-004 | WP / WP | 3 | fuzz/soak success, exact count/time edge, crash/high defect rejection; BLOCKED-TRACEABILITY |
| NFR-005 | WP / WP | 3 | static/dynamic bounds, 1,000-cycle edge, leak/>5% rejection; BLOCKED-TRACEABILITY |
| NFR-006 | AF / AF | 3 | signed trust, revocation/recovery, hash-only/TOCTOU rejection; BLOCKED-TRACEABILITY |
| NFR-007 | EM / EM | 3 | deterministic owner commit, generation boundary, invalid move/raw transport; BLOCKED-TRACEABILITY |
| NFR-008 | EM / EM | 3 | no duplicates, five-line edge, unexplained owner rejection; BLOCKED-TRACEABILITY |
| NFR-009 | EM / EM | 3 | branch/stub gate, 80% boundary, placeholder/fabrication rejection; BLOCKED-TRACEABILITY |
| NFR-010 | ST / ST | 3 | versioned policy, rotation edge, secret/hardcoded downgrade rejection; BLOCKED-TRACEABILITY |
| NFR-011 | AF / AF | 3 | commit/recovery, declared loss boundary, fabricated/lost data rejection; BLOCKED-TRACEABILITY |
| NFR-012 | EM / EM | 3 | fresh receipt, last-change boundary, stale/skip/source-only rejection; BLOCKED-TRACEABILITY |
| NFR-013 | EM / EM | 3 | once-per-state convergence, third-cycle edge, repeated-command/release-gap rejection; BLOCKED-TRACEABILITY |
| NFR-014 | EM / EM | 3 | manual quality, folded detail boundary, unreachable/stale guide rejection; BLOCKED-TRACEABILITY |

## Matrix

Required rows are:

`{x86_64, aarch64, riscv64} × {qemu-system, native-host, physical-board} × required capability × applicable filesystem/protocol`.

Each row records prerequisite, exact command/argv, image/binary/config hashes, nonce, firmware/board/accelerator classification, ordered artifacts, outcome, owner, reviewer, and blocker/resume data.

QEMU visual evidence uses QMP screenshot/readback only in the `qemu-system` class. Physical-board visual evidence identifies the board/CPU/display output and HDMI/DP capture device or framebuffer/JTAG readback path, flashed image hash, boot/download command, serial/SSH markers, frame/revision IDs, artifact hashes, and reviewer. Native-host evidence uses the production host compositor/readback path and cannot promote a physical row.

## Typed captures

- `artifact`: images, manifests, receipts, hash indexes;
- `binary`: ELF/ISA/ABI/linker identity;
- `exec`: argv, stdout, stderr, exit/reap;
- `protocol`: negotiation and wire/error traces;
- `log`: serial/SSH/lifecycle/fuzz/soak output;
- `gui`: structured scene/frame/readback plus screenshots;
- `api`/`text`: ledger, counters, diagnostics, TUI.

## Campaign gates

- >=1,000,000 deterministic fuzz/property cases per parser/media family, zero crash/hang/bypass.
- >=24-hour filesystem/server/WM lifecycle soak.
- 1,000 start/stop/cancel/restart cycles with no leaks and resources/RSS within 5%.
- Native performance: warmup + >=10 samples, p50/p95/p99/max/RSS, CV <=5%, selected absolute budgets, <=5% comparable regression.
- QEMU TCG is correctness/tendency evidence only.

## Manual layout

Purpose/audience → claim boundaries → prerequisites → architecture/evidence matrix → seven-step operator workflow → scenario narratives → REQ/NFR scorecard → captures/provenance → blocked rows/resume commands → troubleshooting → compatibility/limitations → folded executable source.

Use `@inline`, `@prev`, and `@include` to keep setup/checker mechanics out of the primary narrative. The generated manual must report zero stubs only after every oracle is real.

## Verification discipline

Run each acceptance command once after its final relevant change. Use three cycles only: contract/static, behavioral/QEMU, production/physical+campaigns. The final reviewer reports FAIL while any row is blocked.
