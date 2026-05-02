# Remote Interpreter Failures Research

**Date:** 2026-03-12

## Summary

Two different remote-interpreter problems were investigated:

1. TRACE32 remote interpreter does not currently start on this host.
2. QEMU RISC-V remote interpreter now supports attach, symbol lookup, and memory
   read through Pure Simple and Rust-shared code, but remote memory write is
   still blocked by the current host debugger/backend combination.

These are different failure classes:

- TRACE32 is blocked by host installation/runtime prerequisites.
- QEMU RISC-V was mostly blocked by Simple-side GDB MI transport bugs, which are
  now fixed, and still has one backend/debugger limitation for writes.

## Scope

This research is based on:

- local repo/runtime checks on 2026-03-12
- the current Simple-side implementation in
  `src/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi.spl`
- the current host-aware system spec in
  `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl`
- official documentation from Lauterbach, QEMU, and GDB

## Local Evidence

### TRACE32

Local checks on this host show:

- `config/t32/t32_stm_headless.t32` exists and already enables:
  - `USB`
  - `SCREEN=INVISIBLE`
  - `RCL=NETASSIST`
  - `PORT=20000`
- `/opt/t32/bin/pc_linux64/t32rem localhost port=20000 PING` returns:
  - `error initializing TRACE32`
- `/opt/t32/bin/pc_linux64/t32usbchecker` can see the probe node and basic USB
  communication succeeds, so this is not a simple "probe absent" failure
- starting `/opt/t32/bin/pc_linux64/t32marm -c config/t32/t32_stm_headless.t32`
  still fails with:
  - `Error: Can't open display: :99`
- attempts to provide `Xvfb :99` were not yet healthy on this host because the
  X server state was stale and not actually usable
- `/opt/t32/bin/pc_linux64/` appears incomplete for Linux GUI support:
  - `t32screenqt5.so` is missing

Conclusion:

- TRACE32 is failing before the repo can use the remote interpreter.
- The current blocker is host/runtime startup, not the interpreter protocol code
  inside this repo.

### QEMU RISC-V

Local checks on this host show:

- `qemu-system-riscv32` is installed and usable
- `clang` can build a temporary RV32 ELF
- the Pure Simple spec
  `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl`
  now passes
- the shared GDB MI client in
  `src/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi.spl`
  now successfully:
  - starts GDB via FIFOs
  - attaches to the QEMU gdbstub
  - resolves `&marker`
  - reads target memory

During debugging, the following Simple-side problems were identified and fixed:

- GDB background PID capture used a different shell from the launch shell
- FIFO startup could deadlock because both ends were not pre-opened
- mutable methods were incorrectly declared immutable in Pure Simple
- GDB MI result parsing relied on enum-pattern behavior that was unreliable in
  this path
- addresses were sent as `0x{decimal}` instead of real hexadecimal strings,
  which broke memory reads

Current remaining QEMU limitation on this host:

- `-data-read-memory-bytes` succeeds
- `-data-write-memory-bytes` at the loaded image address fails with:
  - `Cannot access memory at address 0x80001004`

Conclusion:

- the remote interpreter path itself is now working
- the remaining write issue is backend/debugger behavior on this host, not the
  Pure Simple transport layer

## Official References

### TRACE32 on Linux

Lauterbach documents that Linux TRACE32 uses screen/GUI shared libraries and
has platform-specific GUI runtime requirements even when running in hidden or
automation-oriented modes.

Sources:

- TRACE32 screen libraries and Linux runtime notes:
  <https://repo.lauterbach.com/help_t32screen.html>
- TRACE32 remote-control overview and Remote API direction:
  <https://repo.lauterbach.com/app_fdx.html>

Implication:

- `SCREEN=INVISIBLE` does not mean "no GUI/display/runtime dependencies"
- if the Linux package is incomplete or display startup is broken, `t32rem`
  cannot succeed because there is no live PowerView instance behind it

### GDB MI memory commands

GDB documents `-data-read-memory-bytes` and `-data-write-memory-bytes` as the
correct MI commands for raw memory access.

Source:

- GDB MI data manipulation:
  <https://sourceware.org/gdb/current/onlinedocs/gdb.html/GDB_002fMI-Data-Manipulation.html>

Implication:

- the repo is using the right MI commands
- a write failure here points to target/backend/debugger state, not to choosing
  the wrong MI primitive

### QEMU gdbstub memory mode

QEMU documents gdbstub maintenance packets including physical-memory mode.

Source:

- QEMU system emulation gdbstub:
  <https://www.qemu.org/docs/master/system/gdb.html>

Relevant implication:

- the debugger can view memory through different addressing modes
- if virtual-mode writes fail on a given target/launch shape, a physical-memory
  mode transition may be required for reliable write support

## Root Cause Analysis

### 1. Why TRACE32 remote interpreter fails

Primary cause:

- the host cannot currently launch a usable TRACE32 PowerView instance

Supporting causes:

- missing or incomplete Linux GUI/screen runtime components in
  `/opt/t32/bin/pc_linux64`
- broken X display provisioning on the host during testing
- therefore no PowerView session is alive to serve `t32rem` or the repo's
  remote interpreter path

Why this matters:

- `t32rem` is only a client for a running TRACE32 instance
- if TRACE32 itself never becomes healthy, the interpreter cannot work

### 2. Why QEMU RISC-V remote interpreter write support fails

Primary cause:

- the host is using generic native `gdb`, not a RISC-V aware debugger

Observed behavior:

- remote attach returns `Truncated register 22 in remote 'g' packet`
- despite that degraded session, symbol lookup and memory read still work
- memory write fails at the tested image address

Secondary cause:

- the spec currently probes a symbol address in the loaded image region
- that is a poor writeability probe for this backend/launch shape

Why this matters:

- the remote interpreter is now functional enough for read/inspect operations
- full read-write support needs a target-aware debugger and a deliberate
  writable-memory probe

## What Is Already Fixed In Repo Code

The following repo-side issues were fixed in the shared client path:

- robust GDB startup in `src/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi.spl`
- correct FIFO handling
- Pure Simple-compatible mutable method declarations
- more robust MI result parsing
- correct hexadecimal address formatting

Result:

- Pure Simple and Rust-shared remote-debug code now successfully exercise the
  QEMU RISC-V attach and memory-read path through the same GDB MI client

## What Still Requires Work

### TRACE32

- repair the Linux TRACE32 host installation
- provide a working X/display path or Lauterbach-supported hidden launch path
- verify a real `t32rem ... PING`
- only then proceed to native/GDB remote interpreter smoke/e2e tests

### QEMU RISC-V

- install `riscv64-unknown-elf-gdb`, `riscv32-unknown-elf-gdb`, or
  `gdb-multiarch`
- add a target-aware writable-memory test path
- optionally teach the client to enable QEMU physical-memory mode when needed

## Recommended Direction

The repo should treat the two lanes differently:

- TRACE32 lane:
  host-recovery first, repo e2e second
- QEMU lane:
  repo/runtime improvements first, then host debugger quality upgrade

This avoids wasting implementation effort on TRACE32 protocol code while the
host cannot even start PowerView, and it keeps the QEMU lane moving because the
remaining issue there is much narrower.
