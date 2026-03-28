# TRACE32 Linux Setup

**Date:** 2026-03-08

## Purpose

This guide captures the remaining Linux host setup needed to run real
on-device `t32_native` and `t32_gdb` baremetal smoke tests from this repo.

Repo-side preparation is now in place. The remaining blocker is a usable local
TRACE32 PowerView session that can see the Lauterbach probe and expose the
Remote API.

## Repo-Managed Assets

The repo now ships the pieces needed to start and validate the STM TRACE32
lanes once the host runtime works:

- shared hidden Linux config:
  - `config/t32_stm_linux_hidden.t32`
- board-specific startup wrappers:
  - `config/t32/stm32wb_native_start.cmm`
  - `config/t32/stm32h7_native_start.cmm`
  - `config/t32/stm32wb_gdb_start.cmm`
  - `config/t32/stm32h7_gdb_start.cmm`
- shell helpers:
  - `scripts/t32_start_stm.shs`
  - `scripts/t32_check_ready.shs`
  - `scripts/t32_enable_gdb.shs`
- shared STM smoke fixture:
  - `test/fixtures/baremetal/stm_semihost_smoke.s`
  - `test/fixtures/baremetal/stm_semihost_smoke.ld`
- readiness specs:
  - `test/integration/debug/hardware/t32_native_spec.spl`
  - `test/integration/debug/hardware/t32_gdb_bridge_spec.spl`

## Verified Local Symptoms

On this host:

- `lsusb` reports `0897:0002 Lauterbach Power Debug/Power Debug II`
- `/opt/t32/bin/pc_linux64/t32rem` exists
- `/opt/t32/bin/pc_linux64/t32usbchecker` exists
- `t32usbchecker` reports:

```text
Error: no useable TRACE32 devices found.
```

- `t32rem localhost port=20000 PING` reports:

```text
error initializing TRACE32
```

- `t32marm` with a valid Linux config now gets past config parsing and fails at
  the hardware/runtime layer:

```text
FATAL ERROR from PODBUS-driver: TRACE32 not connected or not accessible
```

- the expected vendor device path is still missing:

```text
/dev/lauterbach/trace32/*
```

## Why USB Presence Is Not Enough

Two independent conditions must be true before `t32_native` or `t32_gdb` can
run:

1. TRACE32 must be able to open the Lauterbach probe on Linux.
2. A PowerView session must stay alive with Remote API access enabled.

This host currently satisfies neither condition fully.

The USB probe is visible to Linux, but TRACE32 still cannot use it through the
device path it expects. Even if the probe becomes accessible, `t32rem` still
needs a live PowerView session on the configured API port.

## Required Host Fix

Lauterbach ships a Linux udev rule in:

```text
/opt/t32/bin/pc_linux64/udev.conf/kernel_starting_2.6.32/10-lauterbach.rules
```

The shipped rule is:

```text
ACTION=="add", SUBSYSTEM=="usb", ENV{DEVTYPE}=="usb_device", ATTR{idVendor}=="0897", SYMLINK+="lauterbach/trace32/%k", MODE:="0666"
```

Apply that rule on the host, then reload udev or reconnect the probe:

```bash
sudo cp /opt/t32/bin/pc_linux64/udev.conf/kernel_starting_2.6.32/10-lauterbach.rules /etc/udev/rules.d/
sudo udevadm control --reload-rules
sudo udevadm trigger
```

Then verify:

```bash
ls -l /dev/lauterbach/trace32
/opt/t32/bin/pc_linux64/t32usbchecker
```

The expected next state is that `t32usbchecker` no longer reports
`no useable TRACE32 devices found`.

## Repo Default TRACE32 Config

The repo-managed Linux config accepted by the installed `t32marm` binary is:

```text
config/t32_stm_linux_hidden.t32
```

It enables:

- `PBI=` / `USB`
- `RCL=NETASSIST`
- `PORT=20000`
- `SCREEN=INVISIBLE`

This is the config the repo startup helpers use by default.

## Start Commands

Start a native Remote API session for STM32WB:

```bash
./scripts/t32_start_stm.shs stm32wb native
```

Start a native Remote API session for STM32H7:

```bash
./scripts/t32_start_stm.shs stm32h7 native
```

Start the GDB-backed session variants:

```bash
./scripts/t32_start_stm.shs stm32wb gdb
./scripts/t32_start_stm.shs stm32h7 gdb
```

These wrappers launch `t32marm` with the repo config and the board-specific
repo PRACTICE wrapper.

## Readiness Checks

Check probe access and Remote API availability:

```bash
./scripts/t32_check_ready.shs
```

This runs:

1. `t32usbchecker`
2. `t32rem localhost port=20000 PING`

If step 1 fails, the host USB setup is still wrong.
If step 2 fails, PowerView is not exposing a usable Remote API session yet.

## Enable TRACE32 GDB Back-End

After a working TRACE32 session is up, enable the GDB back-end on the repo
default port:

```bash
./scripts/t32_enable_gdb.shs localhost 20000 2331
```

At that point an external GDB client should attach to `localhost:2331`.

## Shared STM Smoke Fixture

The repo now includes a shared Cortex-M smoke artifact source used to align the
OpenOCD and TRACE32 lanes:

- `test/fixtures/baremetal/stm_semihost_smoke.s`
- `test/fixtures/baremetal/stm_semihost_smoke.ld`

This fixture is intended to be the first common on-device smoke workload for:

- STM32WB + OpenOCD
- STM32H7 + OpenOCD
- STM32WB + TRACE32 native
- STM32H7 + TRACE32 native
- STM32WB + TRACE32 GDB
- STM32H7 + TRACE32 GDB

The repo-side asset is ready. Actual device execution still depends on the host
TRACE32 runtime becoming usable.

## Repo Test Commands

Once the session is live, rerun:

```bash
./src/compiler_rust/target/debug/simple test test/integration/debug/hardware/t32_native_spec.spl --leak=off
./src/compiler_rust/target/debug/simple test test/integration/debug/hardware/t32_gdb_bridge_spec.spl --leak=off
./src/compiler_rust/target/debug/simple test test/integration/debug/hardware/hardware_check_spec.spl --leak=off
```

These specs currently verify repo readiness, helper paths, and command shape.
The final missing step after host repair is to promote them from readiness
validation to real on-device smoke execution.
