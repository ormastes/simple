# System Test Plan: SimpleOS Complete OS Hardening

## Purpose

Prove REQ-001–REQ-020 and NFR-001–NFR-014 through live, fail-closed, nonce-bound evidence. A missing prerequisite produces a `BLOCKED` row with a resume plan and fails the umbrella; no scenario calls `skip()` or converts staging/source presence into PASS.

## Implementation status and linked subplans

This is the umbrella owner, not a replacement for the implementation plans
below.  A source change or static contract is **not** acceptance evidence; all
rows stay blocked until their named QEMU/native producer publishes a fresh,
target-bound receipt.

| Subplan | Owns |
|---|---|
| [Boot service authority](simpleos_boot_service_authority_v1.md) | signed admission, finite root capability pouch, scheduler/IPC publication, and launch lease |
| [Filesystem toolchain and servers](simpleos_filesystem_toolchain_servers.md) | filesystem-launched Simple/LLVM tools and web/database services |
| [Server capability manifest](simpleos_server_capability_manifest.md) | exact server child grants, protected data, and parent-only spawn authority |
| [Server execution matrix](simpleos_server_execution_matrix.md) | HTTP, database, lifecycle, and confinement evidence |
| [Three-architecture QEMU evidence](simpleos_three_arch_qemu_evidence_admission.md) | x86_64, ARM64, and RV64 target-bound receipt admission |
| [QEMU system tests](../os/simpleos/qemu_system_tests_multiarch_2026-06-13.md) | canonical multi-architecture guest execution workflow |
| [Window-manager evidence](simpleos_qemu_wm_real_screen.md) | production WM screen/readback evidence |

### Completed implementation slices (unverified)

- The loader has a sealed boot-service receipt/root-publication transaction,
  and server recipe policy gives the parent the required parent-only
  `ProcessSpawn` authority while keeping child grants finite.
- DBFS boot now has a validated root-mount transaction with staged publication
  and rollback.
- NVFS now has a three-architecture receipt-shape campaign and a production
  root-mount transaction; the latest corrective implementation keeps staging
  private, rejects corrupt/conflicting NVFS metadata instead of falling back to
  DBFS, and tears down by exact sealed identity on failure.  It still requires
  independent review and live evidence.
- Simple web transport preserves zero-progress writes and rejects truncated
  sendfile bodies; SSHD rejects malformed version lines.
- FAT32/NVFS read-only hydration and mount-handle isolation fixes are present.

### Remaining implementation and evidence

1. Accept the repaired boot receipt after independent review, compose the
   canonical `/SERVERS.ELF` catalog record into boot media, and wire the shared
   transaction into x86_64, ARM64, and RV64 entries with canonical arguments.
2. Finish the shared positioned-filesystem OFD route, then use it for managed
   DBFS/NVFS syscalls.  It must preserve generation pins, shared offsets,
   dup/fork last-alias close, rollback, and backend-selected dispatch; do not
   add an ad-hoc `FD_TYPE_NVFS`/raw DBFS descriptor.
3. Add a backend-owned FAT32 executable-identity receipt under the FAT mutation
   owner.  Current loader observations are insufficient for TOCTOU-safe
   dirent/LFN identity validation.
4. Supply a current admitted Pure-Simple compiler or all three verified
   architecture auth-contract producers, then run the canonical x86_64/ARM64/
   RV64 QEMU rows.  The historical admitted compiler embeds a removed runtime
   C source and must not be used as current-source evidence.
5. Produce the required live receipts for filesystem toolchain/Clang hello,
   primary tools, server protocols, SSHD, DBFS/NVFS persistence, WM behavior,
   performance, and duplication.  CI/PR checks do not replace these receipts.

## Current implementation blocker: boot capability handoff

The x86_64, ARM64, and RV64 authenticated media fixtures now require a real,
caller-owned `CapabilitySet`; their legacy cap-less routes revoke admission and
fail closed. The architecture boot entries currently have only scalar root
identity (`caller=0`), not a root TCB with finite, concrete capabilities.
Scheduler snapshot leases intentionally reject task zero and ambient/unpledged
sets. Do not repair this by calling `CapabilitySet.full()`,
`spawn_recipe_seed_parent_caps`, or an architecture-local synthetic issuer.

The missing production owner is a signed-manifest-bound boot-capability service
that creates a nonzero root/service TCB, retains provenance-bearing finite
tokens, and hands a one-shot pinned capability set (or equivalent scheduler
lease) to the authenticated x86_64/ARM64/RV64 media launch entrypoints. Until
that interface exists, all corresponding live filesystem-launch rows remain
`BLOCKED`; source presence and legacy compatibility wrappers are not evidence.

The server/DBFS path has a separate prerequisite: scheduler adoption and the
DBD startup syscall reference `server_data_launch_grant_registry`, but that
owner is absent. Its historical design requires a sealed executable image to
carry canonical source path and protected server role; the current
`ExecutableImageHandleV1` intentionally carries neither field. Recreating the
registry from pathname input or a second DBD token would split authority. The
required implementation is one atomic contract migration: bind canonical path
and server role to the execute-open image handle at admission, restore the
bounded scheduler registry over those sealed coordinates, then pass only its
one-shot task/lifecycle/exec-generation grant to the namespace/DBD owner.

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
