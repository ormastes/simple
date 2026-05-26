# Crash-Safe 24-Hour Remaining Work Plan - 2026-05-26

## Goal

Finish the next 24 hours of recovery work without repeating the May 25 host
hard-lockup failure mode. Treat QEMU, USB/JTAG board probes, native builds, and
parallel agents as bounded resources, not background fire-and-forget jobs.

## Crash Prevention Guardrails

- Run at most one QEMU/KVM guest at a time.
- Run at most one physical-board serial/JTAG probe at a time.
- Do not run QEMU while a USB/JTAG device is reconnecting or while board flash
  scripts are active.
- Prefer `timeout` on every QEMU, OpenOCD, serial capture, native-build smoke,
  and benchmark command.
- Keep long-running runs in a named log directory under `build/test-artifacts/`
  with a short summary file.
- Before launching a heavy command, record:
  - `df -h /`
  - `free -h`
  - `ps -eo pid,comm,%cpu,%mem,args --sort=-%cpu | head -30`
  - `journalctl -k -n 80 --no-pager`
- Stop and investigate before continuing if any appear:
  - `watchdog: Watchdog detected hard LOCKUP`
  - `blocked for more than`
  - `Out of memory`
  - NVMe I/O errors
  - repeated USB disconnect/reconnect loops

## Resource Limits

- Disk: require at least 250 GiB free before multiarch/native/QEMU work.
- Memory: require at least 32 GiB available before native-build or QEMU work.
- Swap: do not treat swap as capacity for compiler or QEMU parallelism.
- CPU: keep heavy jobs below half of logical CPUs unless a task explicitly
  measures scaling.
- QEMU memory: use the smallest scenario memory declared by the lane catalog;
  do not increase memory to mask failures without recording why.

## Agent Spawn Rules

- Main agent owns git state, commits, pushes, and any command that launches QEMU
  or touches physical hardware.
- Spawned agents may edit only disjoint documentation or source scopes.
- Spawned agents must not run QEMU, OpenOCD, board flashing, full bootstrap, or
  unbounded benchmarks.
- Spawned agents must not repair `jj` metadata, submodules, or git refs.
- Use at most three spawned agents at once:
  - Agent A: SimpleOS/QEMU/board plan and tests.
  - Agent B: FAT/NVFS/DBFS benchmark plan and pure DB follow-up.
  - Agent C: optimization plugin and MCP/LSP startup/perf guard review.
- Each spawned agent must return changed paths and verification commands.

## 24-Hour Work Queue

1. Stabilize repo control plane:
   - Keep `main` clean with git.
   - Leave `jj` repair for a separate task unless git becomes blocked.
   - Commit small, reviewable slices before running heavy checks.
2. SimpleOS evidence:
   - Keep raw-image scans diagnostic-only.
   - Run focused qemu runner specs before any live QEMU.
   - Run only one live QEMU smoke after specs pass.
3. Board evidence:
   - Unplug or isolate flapping USB/JTAG devices before non-board work.
   - For board work, run build-only first, then one serial-capture lane.
4. Filesystem/database performance:
   - Create or refresh benchmark harnesses without live QEMU.
   - Run one representative benchmark set only after disk/memory preflight.
5. Optimization plugin/MCP:
   - Work from unit/integration specs and native smoke checks.
   - Do not start perf sweeps in parallel with QEMU or board captures.

## Verification Gates

- `git status --short --branch` shows a clean `main` before push.
- Focused specs pass for touched areas.
- Heavy command log includes preflight resource snapshot and timeout value.
- Any QEMU or board pass includes a real guest/serial marker, not host-only
  success.
- If a hard-lockup signature reappears, stop all heavy work and write a new
  crash note before resuming.
