# Remote Interpreter Recovery Plan

**Date:** 2026-03-12

## Goal

Make both remote interpreter lanes usable:

1. TRACE32 remote interpreter
2. QEMU RISC-V remote interpreter

Success means:

- Pure Simple path works
- Rust-shared path works
- system specs/documentation describe the real state
- failures are classified as repo bugs vs host blockers, not mixed together

## Current State

### TRACE32

- `t32rem ... PING` fails with `error initializing TRACE32`
- PowerView does not start cleanly on this host
- no live interpreter session exists yet

### QEMU RISC-V

- Pure Simple attach/read path works end-to-end
- shared GDB MI client path works for both runtimes
- remote memory write is still backend-limited on this host

## Plan

### Phase 1. Stabilize QEMU RISC-V read path

Status:

- mostly done

Tasks:

- keep the shared GDB MI client in
  `src/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi.spl` as the single
  attach/read implementation
- preserve the Pure Simple system spec in
  `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl`
- keep the spec host-aware so missing tools and host backend failures are
  reported as `skip:` or `blocked:`

Exit criteria:

- the Pure Simple remote baremetal spec passes on this host
- attach, symbol lookup, and memory read are verified through the shared client

### Phase 2. Restore QEMU RISC-V write support

Tasks:

1. Install a target-aware debugger on the host:
   - preferred: `riscv64-unknown-elf-gdb`
   - fallback: `gdb-multiarch`
2. Update the client preference order only if needed after host install
3. Replace the current write probe with a known writable RAM probe
4. If writes still fail, add a QEMU gdbstub physical-memory-mode path using
   `maintenance packet Qqemu.PhyMemMode:1`
5. Add one spec that requires write support only when the host debugger is
   target-aware

Repo work:

- extend `GdbMiClient` with an optional helper for console command execution
- add a `qemu_writeable_memory_status()` helper beside the current read smoke
- document the host dependency explicitly in generated spec docs

Exit criteria:

- remote memory write passes in at least one supported host configuration
- the spec distinguishes:
  - repo bug
  - missing debugger capability
  - target/backend write rejection

### Phase 3. Recover TRACE32 host startup

Tasks:

1. Verify the Linux TRACE32 installation is complete:
   - required screen/GUI shared libraries present
   - no partial vendor unpack
2. Repair X/display startup:
   - remove stale `/tmp/.X99-lock` if needed
   - launch a healthy `Xvfb`
   - verify with `xdpyinfo`
3. Start TRACE32 PowerView directly:
   - `t32marm -c config/t32/t32_stm_headless.t32`
4. Confirm Remote API readiness:
   - `t32rem localhost port=20000 PING`
5. Only after `PING` works, run repo-side TRACE32 interpreter smoke

Host work:

- may require reinstalling TRACE32 Linux package from Lauterbach
- may require fixing fonts/display packages expected by TRACE32
- may require proper udev and device-node recovery even though current USB
  communication already partially works

Exit criteria:

- live PowerView instance starts
- `t32rem ... PING` succeeds
- native TRACE32 remote interpreter can run at least one no-op/smoke command

### Phase 4. Enable TRACE32 remote interpreter tests

Tasks:

1. Add a minimal native TRACE32 interpreter smoke spec:
   - connect
   - ping
   - execute one safe command
   - disconnect
2. Add a second host-aware TRACE32 GDB bridge smoke spec:
   - enable GDB back-end inside TRACE32
   - attach external GDB
   - verify one register or memory read
3. Keep these specs non-hanging by design:
   - explicit readiness checks first
   - `blocked:` on host startup failure

Repo work:

- align all TRACE32 specs with the actual config files that exist
- remove references to nonexistent helper scripts from older docs
- update stale checklist docs after the new lane is real

Exit criteria:

- one `t32_native` smoke path passes
- one `t32_gdb` smoke path passes

### Phase 5. Unify runtime expectations

Tasks:

1. Keep shared remote-debug behavior in the common client layer where possible
2. Add notes for Pure Simple constraints when mutability/parser behavior differs
3. Add a short matrix doc section:
   - Pure Simple + QEMU
   - Rust-shared + QEMU
   - Pure Simple + TRACE32
   - Rust-shared + TRACE32

Exit criteria:

- no separate ad hoc implementations drift apart unnecessarily
- failures are attributable to either:
  - shared protocol code
  - Pure Simple runtime limitation
  - Rust-side runtime limitation
  - host/debugger/tooling limitation

## Immediate Next Actions

### Repo

1. Add a console-command helper to `GdbMiClient` for QEMU maintenance packets.
2. Add a writable-memory QEMU spec variant gated on debugger capability.
3. Update stale TRACE32 docs that still mention nonexistent helper scripts.

### Host

1. Install a RISC-V aware GDB or `gdb-multiarch`.
2. Reinstall or repair the TRACE32 Linux runtime so the screen libraries are
   present.
3. Bring up a clean Xvfb session and verify `xdpyinfo`.
4. Re-test `t32marm` and then `t32rem ... PING`.

## Risks

- TRACE32 recovery may require host-admin intervention outside this repo.
- QEMU write support may still differ by machine model, ELF layout, and GDB
  build.
- relying on generic host `gdb` will keep the RISC-V lane in a degraded state.

## Definition Of Done

This work is done when all of the following are true:

- QEMU RISC-V remote interpreter supports attach, symbol lookup, memory read,
  and memory write in a supported host configuration
- TRACE32 remote interpreter can start and answer a live `t32rem` smoke
- system specs for both lanes are checked in and documented
- docs describe the real host prerequisites and failure modes
