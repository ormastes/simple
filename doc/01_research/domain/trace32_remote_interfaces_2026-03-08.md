# TRACE32 Remote Interfaces Research

**Date:** 2026-03-08

## Summary

Lauterbach documents three remote-control paths for TRACE32 PowerView:

1. TRACE32 Remote API
2. GDB Remote Serial Protocol (RSP) via TRACE32's GDB back-end
3. Target Communication Framework (TCF)

For this repo, only the first two matter.

TRACE32 therefore exposes two different remote-control paths that matter for this repo:

1. `t32rem` / Remote API / RCL
2. GDB Remote Serial Protocol (RSP) via TRACE32's GDB back-end

They are not the same interface and they need different TRACE32 setup.

## 1. Native TRACE32 Remote API

This is Lauterbach's own control API for PowerView.

- Official manual: `API for Remote Control and JTAG Access in C`
  Source: https://www2.lauterbach.com/pdf/api_remote_c.pdf
- Official KB: `How to remotely control TRACE32 PowerView?`
  Source: https://support.lauterbach.com/kb/articles/how-to-remotely-control-trace32-powerview
- Official KB: `How to use the t32rem tool?`
  Source: https://support.lauterbach.com/kb/articles/how-to-use-the-t32rem-tool

What the docs say:

- Lauterbach's `How to remotely control TRACE32 PowerView?` KB lists the Remote API as the first of three supported remote-control mechanisms.
- Lauterbach's `How to use the t32rem tool?` KB says `t32rem` "uses the Remote API to send commands directly to TRACE32 PowerView."

- TRACE32 must expose an RCL section such as:

```text
; T32 API Access (TCP)
RCL=NETTCP
PORT=20000
```

- `api_remote_c.pdf` states that `RCL=NETTCP` enables the Remote API TCP port and that external applications can control TRACE32 through it.
- `t32rem` is just a shell tool on top of that same Remote API.
- Lauterbach's KB also says the Remote API must be enabled with `SETUP.API.RCL.Enable`.
- `t32rem` usage from the KB:

```text
t32rem <host> [port=<n>] [protocol=NETASSIST | NETTCP] [timeout=<s>] [wait=<ms>] <command>
```

Implication for this repo:

- `t32_native` should use the RCL interface, not GDB.
- `t32rem` commands like `PING`, `SYStem.Up`, `Register.Get PC`, and `System.Option GDBSERVER ON` are all PowerView commands sent over RCL.

## 2. TRACE32 GDB Back-End

This is TRACE32 acting as a GDB stub/server for an external GDB client.

- Official manual: `TRACE32 as GDB Back-End`
  Source: https://www2.lauterbach.com/pdf/backend_gdb.pdf
- Related KB: `Does TRACE32 support the GDB Remote Serial Protocol RSP?`
  Source: https://support.lauterbach.com/kb/articles/does-trace32-support-the-gdb-remote-serial-protocol-rsp

What the docs say:

- TRACE32 PowerView implements a GDB server/stub over TCP.
- Lauterbach's RSP KB explicitly distinguishes `TRACE32 as GDB Front-End` from `TRACE32 as GDB Back-End`.
- The same KB says the Remote API is the recommended way to control TRACE32 PowerView from an external application.
- The GDB server is enabled inside a running TRACE32 session with:

```text
SETUP.API.GDB.Enable
SETUP.API.GDB.Enable /PORT 12345
```

- Default GDB back-end port is `30000` if no port is specified.
- Example client side:

```text
(gdb) target extended-remote 127.0.0.1:30000
```

Implication for this repo:

- `t32_gdb` is a two-layer flow:
  - use RCL / `t32rem` to configure TRACE32 itself
  - then use GDB RSP to talk to TRACE32's GDB stub
- This is why the `t32_gdb` env still needs `t32rem` to enable and configure the GDB server inside PowerView before GDB can attach.

## 3. Config File Details From Lauterbach

- Official manual: `TRACE32 Installation Guide`
  Source: https://www2.lauterbach.com/pdf/installation.pdf
- Official KB: `How do I start a hidden instance of TRACE32?`
  Source: https://support.lauterbach.com/kb/articles/how-do-i-start-a-hidden-instance-of-trace32

Relevant points:

- Config sections are separated by blank lines.
- `PBI=USB` selects the PODBUS USB connection to Lauterbach hardware.
- If several Lauterbach probes are connected, `NODE=<name>` is required. The manual says the manufacturing default node name is the serial number of the debug module.
- `RCL=NETTCP` opens the Remote API TCP port.
- `SCREEN=OFF` starts TRACE32 as a hidden instance suitable for automation.
- Newer TRACE32 versions also support command-line API enabling:

```text
--t32-api-rcl=TCP:20000
--t32-screen=off
```

Important distinction:

- `PBI=USB` is about how PowerView talks to Lauterbach hardware.
- `RCL=NETTCP` is about how external tools talk to PowerView.
- `SETUP.API.GDB.Enable /PORT ...` is about how external GDB talks to PowerView.
- TCF is a third remote interface, but it is Eclipse-oriented and not part of the current Simple test-runner model.

## 4. Local Machine Findings

Observed locally in this workspace:

- TRACE32 is installed under `/opt/t32`
- The 64-bit native remote tool exists:

```text
/opt/t32/bin/pc_linux64/t32rem
```

- A Lauterbach USB device is attached:

```text
0897:0002 Lauterbach Power Debug/Power Debug II
```

- TRACE32 also ships board-specific configs and startup scripts already present on disk:
  - `/opt/t32/config_stm32wb.t32`
  - `/opt/t32/stm32wb_startup.cmm`
  - `/opt/t32/config_stm32h7.t32`
  - `/opt/t32/stm32h7_startup.cmm`
- the repo now ships its own automation-oriented overlay files:
  - `config/t32_stm_linux_hidden.t32`
  - `config/t32/stm32wb_native_start.cmm`
  - `config/t32/stm32h7_native_start.cmm`
  - `config/t32/stm32wb_gdb_start.cmm`
  - `config/t32/stm32h7_gdb_start.cmm`
  - `scripts/t32_start_stm.shs`
  - `scripts/t32_check_ready.shs`
  - `scripts/t32_enable_gdb.shs`
  - `test/fixtures/baremetal/stm_semihost_smoke.s`
  - `test/fixtures/baremetal/stm_semihost_smoke.ld`
- The shipped board configs currently contain only the hardware-side connection basics:

```text
PBI=
USB

SCREEN=
FONT=SMALL
```

- They do not currently enable `RCL=NETTCP` or assign a Remote API `PORT`.

Current practical blockers on this machine:

- Raw `t32rem localhost port=20000 PING` returns `error initializing TRACE32`
- `t32usbchecker` reports no usable TRACE32 devices
- `strace` shows `t32usbchecker` probes `/dev/lauterbach` and legacy `/proc/bus/usb`, not `/dev/bus/usb`
- the vendor-shipped Linux udev rule under `/opt/t32/bin/pc_linux64/udev.conf/kernel_starting_2.6.32/10-lauterbach.rules` is not what is effectively active on this host
- that shipped rule is supposed to create `/dev/lauterbach/trace32/%k` with mode `0666`
- on this host there is no `/dev/lauterbach/trace32` path and the raw device node remains `664 root:plugdev`
- after fixing config syntax, `t32marm` now gets past parsing and fails later with:

```text
FATAL ERROR from PODBUS-driver: TRACE32 not connected or not accessible
```
- a privileged Docker workaround that creates `/dev/lauterbach/trace32/3-3` proves the probe is reachable:
  - `t32usbchecker` reports `Basic communication...CONNECT request OK`
  - `USB communication OK`
- inside the container, the non-Qt front-end can be kept alive longer under `Xvfb` with `SCREEN=INVISIBLE`, which narrows the remaining failure to the PowerView runtime/API layer rather than USB detection alone
- but a real PowerView launch still fails even with `Xvfb`:

```text
Error: XtCreatePopupShell requires non-NULL parent
```
- the account cannot install missing host packages with `sudo`
- there is no available X server helper like `xvfb-run`
- the non-Qt binary still wants a display in our local startup attempts
- the Qt binary requires old Qt runtime libraries not currently available on the host

Inference:

- The repo-side config and test-runner work is in the right direction.
- The remaining T32 blocker is host/runtime setup for a real PowerView session, not the Simple test runner itself.
- More specifically, the shipped local `.t32` configs are not yet sufficient for `t32rem` automation because they do not expose the Remote API port, and the host USB access path still does not satisfy TRACE32's own Linux requirements.
- Even after working around the USB path in Docker, the installed TRACE32 Linux build still does not reach a stable hidden PowerView session in this environment.

Repo readiness conclusion:

- The repo now has a stable T32 automation baseline:
  - a Linux config accepted by `t32marm`
  - board-specific startup wrappers for native and GDB-backed lanes
  - shell helpers for bring-up, readiness checks, and GDB enablement
  - a shared STM Cortex-M smoke fixture intended for both OpenOCD and TRACE32 lanes
- That means the remaining work is operational, not architectural.
- Once a host TRACE32 session becomes usable, the next step is execution, not more repo plumbing.

## 5. Recommended Repo Model

For this repo, the clean split should stay:

- `t32_native`
  - uses `t32rem`
  - requires RCL enabled in PowerView
  - does not involve GDB

- `t32_gdb`
  - uses `t32rem` first to configure PowerView
  - then uses external GDB against TRACE32's GDB back-end port

That matches Lauterbach's own documentation and avoids mixing the two interfaces conceptually.

It also matches Lauterbach's recommendation that external applications should prefer the Remote API over GDB when the goal is to control PowerView itself.

## 6. Recommended Next Host Steps

To complete real hardware validation for the T32 lanes on this machine:

1. Fix Linux device visibility for TRACE32 itself:
   - apply Lauterbach's shipped `10-lauterbach.rules`
   - reconnect the probe or reload udev
   - verify `/dev/lauterbach/trace32/*`
   - verify `t32usbchecker`
2. Start a real TRACE32 PowerView instance with:
   - `PBI=USB`
   - `SCREEN=OFF`
   - `RCL=NETASSIST` or `RCL=NETTCP`
   - `PORT=20000`
3. Verify `t32rem localhost port=20000 PING`
4. Start a repo-managed STM lane:

```text
./scripts/t32_start_stm.shs stm32wb native
./scripts/t32_start_stm.shs stm32h7 native
```

5. For the GDB path, enable:

```text
./scripts/t32_enable_gdb.shs localhost 20000 2331
```

6. Attach GDB to `localhost:2331`
7. Promote the current readiness specs to real on-device smoke runs using the shared STM fixture.

Until step 1 works, `t32_native` and `t32_gdb` cannot be considered hardware-verified.

## Sources

- https://support.lauterbach.com/kb/articles/how-to-remotely-control-trace32-powerview
- https://support.lauterbach.com/kb/articles/how-to-use-the-t32rem-tool
- https://support.lauterbach.com/kb/articles/does-trace32-support-the-gdb-remote-serial-protocol-rsp
- https://www2.lauterbach.com/pdf/api_remote_c.pdf
- https://www2.lauterbach.com/pdf/backend_gdb.pdf
- https://www2.lauterbach.com/pdf/installation.pdf
- https://support.lauterbach.com/kb/articles/how-do-i-start-a-hidden-instance-of-trace32
