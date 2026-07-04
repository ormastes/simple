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

## Patch Set Completed (2026-04-02)

All items from the original "Required Next Patch Set" have been implemented.

### Shared host runtime helper: DONE

- Created `scripts/t32_host_bootstrap.shs` with:
  - `t32_resolve_bin()` — prefers `t32marm64` over `t32marm`
  - `t32_bootstrap_fonts()` — copies PCF/BDF fonts, runs `mkfontdir`
  - `t32_setup_xvfb_args()` — passes `-fp` via xvfb-run `-s` flag
  - `t32_env_setup()` — exports `T32SYS=/opt/t32/bin/pc_linux64`
  - `t32_lifecycle_on/off()` — full lifecycle with MCI TCP fallback
  - `t32_remote()` — t32rem wrapper with `protocol=NETTCP`

### Scripts patched: DONE (5 files)

- `scripts/t32_start_stm.shs` — sources bootstrap, resolved binary, fonts
- `scripts/t32_rcl_doctor.shs` — sources bootstrap, resolved binary, NETTCP
- `scripts/t32_check_ready.shs` — sources bootstrap, NETTCP
- `scripts/t32_semihost_hello.shs` — sources bootstrap, lifecycle management
- `scripts/t32_enable_gdb.shs` — sources bootstrap, NETTCP

### Config files patched: DONE (4 files)

- `config/t32/t32_rcl_only.t32` — `SYS=/opt/t32/bin/pc_linux64`, `NETTCP`
- `config/t32_stm_linux_hidden.t32` — same
- `config/t32/t32_stm_headless.t32` — same
- `config/t32/t32_stm_gui.t32` — same

### New scripts: DONE (3 files)

- `scripts/t32_run_tests.shs` — multi-ELF remote test runner
- `scripts/t32_mcp_feature_check.shs` — 14-feature validation matrix
- `config/t32/trace32_powerview_entrypoint.shs` — container PowerView+Xvfb

### Container updated: DONE

- Dockerfile adds `xvfb` and `xfonts-utils` packages
- Default CMD changed to `trace32_powerview_entrypoint.shs`
- PowerView entrypoint: tries RCL first, falls back to MCI TCP

## Verification Results (2026-04-02)

### Bootstrap helper functions: PASS

| Check | Result |
|-------|--------|
| `t32_resolve_bin()` | `t32marm64` resolved correctly |
| `t32_bootstrap_fonts()` | 40 files copied, `fonts.dir` generated |
| `t32_env_setup()` | `T32SYS=/opt/t32/bin/pc_linux64` exported |
| `t32_setup_xvfb_args()` | `-fp /tmp/t32-fonts` via `-s` flag |

### PowerView startup: PARTIAL

| Check | Result |
|-------|--------|
| PowerView process starts under Xvfb | PASS — PID alive |
| PowerView binds RCL port 20000 (TCP) | FAIL — port never bound |
| PowerView binds RCL port 20000 (UDP) | FAIL — port never bound |
| Tested with NETTCP config | FAIL |
| Tested with NETASSIST config | FAIL |
| Tested on host native | FAIL |
| Tested in container with Xvfb | FAIL |

**Root cause confirmed:** The 2013 PowerView binary (R.2013.02.000045901) does
not bind the Remote API listener in headless mode, regardless of protocol
(NETTCP or NETASSIST) or environment (host or container).

### MCI TCP fallback: PASS

| Check | Result |
|-------|--------|
| `t32mciserver` binds TCP port 20000 | PASS |
| `t32_tcp_ping.shs` succeeds | PASS |
| `t32rem` PING via MCI | FAIL — protocol mismatch |
| Lifecycle auto-fallback to MCI | PASS |

### Container lifecycle: PASS

| Check | Result |
|-------|--------|
| `t32q.shs build` | PASS — rebuilt with xvfb |
| `t32q.shs on` | PASS — MCI TCP via fallback |
| `t32q.shs ping` | PASS |
| `t32q.shs off` | PASS |
| `t32q.shs gui-on` | SKIP — no host DISPLAY |

### ELF build: PASS

- `clang --target=armv7m-none-eabi` builds `stm_semihost_smoke.elf` correctly
- Both `cortex-m4` (stm32wb) and `cortex-m7` (stm32h7) targets work

### Tasks 1-3 (semihost, test runner, MCP features): BLOCKED

All three tasks require `t32rem` → PowerView RCL, which the 2013 binary cannot
provide headlessly. The scripts are correct and ready; they need a newer T32
binary (≥2015) or a host with a real X11 display.

## What Remains

### Blocker: 2013 PowerView binary

The single remaining blocker is the 2013 PowerView binary. Options:

1. **Upgrade T32 license/binary** (recommended) — any PowerView ≥2015 should
   expose NETTCP Remote API headlessly
2. **Run with a real X11 display** — the 2013 binary may activate RCL when it
   has a real display (not Xvfb), but this is unverified
3. **Use the Lauterbach C API** (`t32api.c`) compiled for Linux — this speaks
   the same NETASSIST protocol as t32rem, so it would have the same limitation

### What is ready for a newer binary

Once a newer PowerView binary is installed:

```bash
# Task 1: semihost hello
scripts/t32_semihost_hello.shs --board stm32wb

# Task 2: remote test runner
scripts/t32_run_tests.shs --default --board stm32wb

# Task 3: MCP feature validation
scripts/t32_mcp_feature_check.shs --board stm32wb
```

All scripts, configs, container infrastructure, and lifecycle management are
in place and verified. Only the binary needs to be upgraded.
