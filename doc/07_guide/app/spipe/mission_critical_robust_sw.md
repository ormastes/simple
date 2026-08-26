# SPipe Mission-Critical Robust Software Guide

Operator guide for SPipe lanes that claim flight-level or mission-critical
robustness across the Simple compiler, SimpleOS baremetal, NVMe firmware
examples, and thread/process/coroutine runtime behavior.

## Contract & Evidence Scope

The lane must say which evidence tier it has: host simulation, QEMU/emulator,
real hardware, generated formal artifact, durable manual proof checked after
regeneration, or mission-critical release gate. Do not promote a weaker tier
into a stronger claim.

A host-only NVMe simulation is not real hardware evidence. A generated
Lean/BYL/RTL file is not a proof claim unless the durable theorem or hardware
proof gate also passed. A single interleaving test is not starvation, fairness,
race, scheduler, channel, lock, or resource-lifecycle proof.

## Required Gates

For SimpleOS mission-critical release readiness:

```bash
sh scripts/check/check-simpleos-mission-critical-release.shs
```

Completion requires the release gate to report `matrix_status=pass`,
`release_status=pass`, `release_blockers=none`, and `prereq_status=ready`.
The completion target remains `simpleos_hardening_matrix_passed=26/26`; a
lower latest snapshot is current blocker evidence, not acceptance.

The hardening matrix is subordinate evidence consumed by the release gate. For
the matrix handoff:

```bash
sh scripts/check/check-simpleos-hardening-evidence-matrix.shs
```

Latest observed matrix-output snapshot for this lane (2026-07-05; rerun the
release gate for current evidence):

- `simpleos_hardening_matrix_passed=26/26`
- `simpleos_hardening_mission_critical_release_status=pass`
- `simpleos_hardening_mission_critical_release_blockers=none`
- `simpleos_hardening_matrix_reason=pass`
- `simpleos_hardening_matrix_blocked_rows=`
- `simpleos_hardening_qemu_guest_perf_release_blocker=none`
- `simpleos_hardening_stale_reports=none`
- `simpleos_hardening_stale_report_names=none`
- `simpleos_hardening_riscv_rtl_sby_proof_status=pass`
- `simpleos_hardening_riscv_rtl_sby_proof_blocker=none`
- `simpleos_hardening_mission_critical_prereqs_status=ready`
- `simpleos_hardening_mission_critical_prereqs_missing=none`
- `simpleos_hardening_nvme_baremetal_wrapper_coverage_status=pass`
- `simpleos_hardening_nvme_baremetal_wrapper_coverage_blockers=none`
- `simpleos_hardening_async_library_hardening_status=pass`
- `simpleos_hardening_async_library_hardening_total=19`

To verify NVMe baremetal wrapper coverage:

```bash
sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs --strict
```

Both RV32 and RV64 wrappers must keep fail-closed `--self-test` evidence before
the coverage audit can support release.

If prerequisites are missing:

```bash
sh scripts/check/check-simpleos-mission-critical-prereqs.shs
sh scripts/setup/setup-simpleos-formal-env.shs --print-install
```

Missing `sby`, `yosys`, or an SMT solver is a blocker, not a proof pass. If
sudo is unavailable, download OSS CAD Suite, source its `environment`, and
rerun the prereq and mission-critical release gates. When changing the prereq
wrapper, also run
`sh scripts/check/check-simpleos-mission-critical-prereqs.shs --self-test`;
missing tool probes must fail closed and remain `prereq_status` blockers.

## Thread, Process, Coroutine Hardening

Use `doc/07_guide/lib/misc/stdlib.md` as the API map. Keep `thread_spawn`
variants, `cooperative_green_*`, `multicore_green_*`, `task_spawn`,
`app.io.mod.process_spawn_async`, and coroutine behavior separate in evidence.

New or changed lifecycle behavior must expose failure visibility and cleanup:
resume/join idempotence for coroutines; `process_wait`,
`process_is_running`/`process_is_alive`, or `process_kill` evidence for child
processes; and `used_runtime_pool()` plus counter evidence for M:N CPU-parallel
claims through `multicore_green_spawn`.

Process/signal hardening must also prove every kill or wait path rejects
`pid <= 0` before signaling or reaping. This is release-blocking for
mission-critical lanes because `kill(-1)` can terminate every user-owned
process. Use `doc/07_guide/runtime/process_kill_safety.md` as the rule and
remember that Rust/C seed-runtime guard changes require
`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy` before
they affect deployed binaries.

For an async-library hardening handoff, use:

```bash
sh scripts/check/check-async-library-hardening-evidence.shs
```

This is representative regression evidence for the current async surfaces, not
a formal starvation/fairness/race proof.

## Formal Proof Gates

Use the narrow command that matches the claim:

- `sh scripts/check/check-simpleos-formal-coverage.shs`
- `sh scripts/check/check-simpleos-critical-formal-proofs.shs`
- `sh scripts/check/check-simpleos-memory-safety-formal-proofs.shs`
- `sh scripts/check/check-simpleos-storage-formal-proofs.shs`
- `sh scripts/check/check-simpleos-boundary-formal-proofs.shs`
- `sh scripts/check/check-riscv-formal-dual-track.shs`
- `sh scripts/check/check-riscv-rtl-sby-proof.shs`

When changing formal or release wrappers, also run the wrapper self-test form
where available, for example
`sh scripts/check/check-simpleos-storage-formal-proofs.shs --self-test` or
`sh scripts/check/check-riscv-rtl-sby-proof.shs --self-test`. For the final
release gate, run
`sh scripts/check/check-simpleos-mission-critical-release.shs --self-test`.
That self-test must fail closed when `matrix_status`, `release_blockers`, or
`prereq_*` fields are absent, and when the matrix exits without status output.
`check-riscv-rtl-sby-proof.shs` must require strict RVFI readiness before
claiming an RTL/SBY proof pass.

For focused matrix negative tests, `MISSION_CRITICAL_PREREQS_LOG` may point the
matrix at a captured prereq evidence log. A prereq log that claims
`status=ready` while `missing != none` or `next_action != none` must be
downgraded to `blocked`, so mission-critical release evidence stays fail
closed.

Dated static reports are release freshness evidence, not permanent proof. When
`simpleos_hardening_stale_reports` is not `none`, the matrix keeps the counted
row total visible but reports `matrix_status=blocked` with
`reason=stale-static-reports` and emits `simpleos_hardening_stale_report_names`
so the stale source gates are visible.

Missing `sby`, `yosys`, or an SMT solver is readiness/blocker evidence, not an
RTL proof pass.

`check-simpleos-formal-coverage.shs` also asserts a text contract: each formal
row must have an executable wrapper gate, process/coroutine/resource
theorem-wrapper self-tests must strip at least one row-backed theorem, and
`setup-simpleos-formal-env.shs` must keep the canonical install command
(`sudo apt-get install yosys symbiyosys boolector z3`). Editing that setup
script without preserving the literal install line fails the coverage audit and
blocks the whole release gate even when every individual proof passes —
aggregate coverage cannot pass by status-only derivation.

## Baremetal Firmware Wrappers

For RV32/RV64 baremetal compiler/firmware lanes, keep runtime-value ABI fixes at
the compiler/runtime owner boundary: do not paper over `rv_type` width bugs with
firmware-local `rt_*` shims or broad all-`i64` predeclares. Add the smallest IR
regression that proves the failing scalar shape (for example RV32 call-result
`!=` literal emits `icmp`, not `rt_native_neq`) and verify both the wrapper
result marker and any subsystem serial `FAIL` lines separately.

For the RV32 NVMe firmware boot wrapper, run
`sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/boot.shs --self-test` after
changing marker handling so a fake QEMU proves missing PASS and serial `FAIL`
paths fail closed.

Use `sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs` to audit the
RV32/RV64 NVMe wrapper set. Completion or release claims must run the same
command with `--strict`. After changing wrapper coverage classification, run
`sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs --self-test` so
fake missing RV32/RV64 wrapper and spec fixtures prove the audit fails closed.
