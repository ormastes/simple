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

The hardening matrix is subordinate evidence consumed by the release gate. For
the matrix handoff:

```bash
sh scripts/check/check-simpleos-hardening-evidence-matrix.shs
```

Latest observed matrix-output snapshot for this lane (2026-07-05; rerun the
release gate for current evidence):

- `simpleos_hardening_matrix_passed=25/25`
- `simpleos_hardening_mission_critical_release_status=pass`
- `simpleos_hardening_mission_critical_release_blockers=none`

If prerequisites are missing:

```bash
sh scripts/check/check-simpleos-mission-critical-prereqs.shs
sh scripts/setup/setup-simpleos-formal-env.shs --print-install
```

Missing `sby`, `yosys`, or an SMT solver is a blocker, not a proof pass. If
sudo is unavailable, download OSS CAD Suite, source its `environment`, and
rerun the prereq and mission-critical release gates.

## Thread, Process, Coroutine Hardening

Use `doc/07_guide/lib/misc/stdlib.md` as the API map. Keep `thread_spawn`
variants, `cooperative_green_*`, `multicore_green_*`, `task_spawn`,
`app.io.mod.process_spawn_async`, and coroutine behavior separate in evidence.

New or changed lifecycle behavior must expose failure visibility and cleanup:
resume/join idempotence for coroutines; `process_wait`,
`process_is_running`/`process_is_alive`, or `process_kill` evidence for child
processes; and `used_runtime_pool()` plus counter evidence for M:N CPU-parallel
claims through `multicore_green_spawn`.

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

Missing `sby`, `yosys`, or an SMT solver is readiness/blocker evidence, not an
RTL proof pass.

`check-simpleos-formal-coverage.shs` also asserts a text contract: each formal
row must have an executable wrapper gate, and `setup-simpleos-formal-env.shs`
must keep the canonical install command (`sudo apt-get install yosys symbiyosys
boolector z3`). Editing that setup script without preserving the literal install
line fails the coverage audit and blocks the whole release gate even when every
individual proof passes — aggregate coverage cannot pass by status-only
derivation.
