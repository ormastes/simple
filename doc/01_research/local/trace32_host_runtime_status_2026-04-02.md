# TRACE32 Host Runtime Status

Date: 2026-04-02

## Summary

The repo-side TRACE32 work is largely complete, but live host TRACE32 runtime
startup is still not end-to-end fixed. This report captures what has been
implemented, what was proven during the latest host investigation, and what
still needs to be patched and re-verified.

## Already Implemented In Repo

- Native `t32_mcp` cold-path/runtime fixes were completed earlier and the
  packaged binary was rebuilt.
- The TRACE32 container wrapper was added:
  - `scripts/t32q.shs`
- The container lifecycle was implemented and verified for the headless MCI
  path.
- The semihost hello runner was added:
  - `scripts/t32_semihost_hello.shs`
- The TRACE32 host doctor was added:
  - `scripts/t32_rcl_doctor.shs`
- TRACE32 docs and Claude/Codex T32 skills were updated.
- The semihost runner/spec passes in build-only and repo-readiness mode.

## What Was Proven In The Latest Host Investigation

### 1. The installed TRACE32 layout is mixed-version

Observed under `/opt/t32/bin/pc_linux64`:

- `t32rem` and `t32usbchecker` are recent enough to be stamped in 2026.
- PowerView binaries such as `t32marm`, `t32marm64`, `t32marm-qt`,
  `t32marm64-qt` are still from:
  - `Release Feb 2013`
  - `Software Version : R.2013.02.000045901`

This means the installed environment is not a clean modern TRACE32 runtime. The
repo must bootstrap around an old PowerView binary even though some companion
tools are newer.

### 2. `t32marm64` is the stronger host candidate than `t32marm`

The latest checks showed:

- `t32marm64` can stay alive under `xvfb-run`
- `t32marm64` gets further into startup than the old `t32marm` path
- `t32marm64` is therefore the better default executable for host launchers

### 3. The host bootstrap is currently wrong about `T32SYS`

The host probe showed that command-line startup fails unless TRACE32 can locate
its real `config.t32`.

Observed behavior:

- with `T32SYS=/opt/t32`:
  - TRACE32 still reports `config.t32 not found`
- with `T32SYS=/opt/t32/bin/pc_linux64`:
  - TRACE32 reports:
    - `CONFIG: '/opt/t32/bin/pc_linux64/config.t32'`

Conclusion:

- The host runtime should treat `/opt/t32/bin/pc_linux64` as the effective
  TRACE32 root for this install.
- Existing scripts/configs still assume `/opt/t32`, which is incorrect for the
  current machine.

### 4. The X11 bootstrap also needs the TRACE32 bitmap fonts

When launched with the corrected `T32SYS`, PowerView still failed with:

- `FATAL ERROR from X-windows: T32 font not found`
- `Font not found: t32-sys-13`

This was narrowed down further:

- TRACE32 bitmap fonts exist under:
  - `/opt/t32/fonts`
- Copying them to:
  - `/tmp/t32-fonts`
- Running `mkfontdir /tmp/t32-fonts`
- Starting Xvfb with:
  - `-fp /tmp/t32-fonts`

made the font visible. A direct check under Xvfb showed:

- `xlsfonts` contains:
  - `t32-sys-13`

Conclusion:

- Host launchers must bootstrap an X11 font path containing the TRACE32 bitmap
  fonts before starting PowerView.
- Using plain `xvfb-run -a` without a font path is not sufficient.

### 5. Remote API readiness is still not proven

Even after fixing the runtime root and confirming the font visibility, the live
host probes still did not show:

- a listener on port `20000`
- a successful `t32rem localhost port=20000 ... PING`

So the remaining open question is:

- whether the 2013 PowerView binary can expose usable `NETTCP` Remote API once
  fully launched with the corrected environment
- or whether the binary vintage itself remains the final blocker

## What Was Not Finished

- The shared host-runtime patch was not completed.
- A new helper script for host runtime/bootstrap was started conceptually but
  not committed.
- The patch attempt was interrupted before it landed, so no new host-bootstrap
  code from that attempt is present in the repo.
- End-to-end live semihost hello output through host TRACE32 was not observed.

## Required Next Patch Set

### Add a shared host runtime helper

Create a helper script for host TRACE32 startup that does all of the following:

- prefers `t32marm64` before `t32marm`
- sets:
  - `T32SYS=/opt/t32/bin/pc_linux64`
  - `T32TMP=/tmp`
- prepares a temporary font directory such as `/tmp/t32-fonts`
- copies `/opt/t32/fonts/*` into that temp directory
- runs `mkfontdir` on it
- provides Xvfb server args that include:
  - `-fp /tmp/t32-fonts`
- defaults the host automation protocol to:
  - `NETTCP`

### Patch these scripts to use the helper

- `scripts/t32_start_stm.shs`
- `scripts/t32_rcl_doctor.shs`
- `scripts/t32_check_ready.shs`
- `scripts/t32_semihost_hello.shs`
- `scripts/t32_enable_gdb.shs`

### Patch host-oriented config files

Update protocol and runtime assumptions in:

- `config/t32/t32_rcl_only.t32`
- `config/t32_stm_linux_hidden.t32`
- `config/t32/t32_stm_headless.t32`
- `config/t32/t32_stm_gui.t32`

Expected changes:

- switch `RCL=NETASSIST` to `RCL=NETTCP`
- update `SYS=` to the correct runtime root for this machine

## Required Re-Verification After Patch

Run these checks again after the bootstrap patch lands:

1. `scripts/t32_rcl_doctor.shs`
2. `scripts/t32_start_stm.shs --kill-stale stm32wb native`
3. `scripts/t32_check_ready.shs`
4. `scripts/t32_semihost_hello.shs --board stm32wb`

Success criteria:

- PowerView stays alive under the corrected host bootstrap
- port `20000` is actually bound
- `t32rem localhost port=20000 protocol=NETTCP PING` succeeds
- the semihost hello runner reaches:
  - `Data.LOAD.Elf`
  - `Go`
  - `Break`
  - `WinPrint.AREA MCP_OUT`
- the marker `simple-stm-smoke` is observed

## Current Conclusion

The latest investigation materially narrowed the problem:

- the host runtime bootstrap is definitely incomplete today
- the missing pieces are:
  - correct TRACE32 runtime root
  - X11 bitmap font bootstrap
  - likely protocol default migration from `NETASSIST` to `NETTCP`

What remains unknown is not the repo direction but the final capability of the
old 2013 PowerView binary once launched correctly. That must be settled by the
next patch-and-verify cycle.
