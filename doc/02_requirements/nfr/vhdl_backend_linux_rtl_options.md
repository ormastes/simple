<!-- codex-research -->
# VHDL Backend + Linux RTL NFR Options

## Option 1: Proof-First Minimal CI

Description: every generated VHDL example must pass GHDL analysis/elaboration; generated RV32I must run at least one semihosting program.

Pros:
- Keeps scope practical.
- Prevents text-only backend claims.

Cons:
- Does not prove synthesis timing or FPGA hardware.

Effort: M.

## Option 2: Simulation-Grade RTL CI

Description: generated CPU/SoC must run GHDL or Verilator tests, compare instruction traces against emulator/reference, and produce VCD on failure.

Pros:
- Catches real CPU/RTL bugs.
- Enables Linux bring-up debugging.

Cons:
- More infrastructure and slower tests.

Effort: L.

## Option 3: Linux Boot Acceptance

Description: generated RV64 SoC must boot Linux to serial markers: firmware banner, `Linux version`, DTB recognition, init/userspace marker.

Pros:
- Strongest proof of real platform.

Cons:
- Too expensive for the first backend completion milestone.
- Requires firmware/rootfs artifacts and long Verilator runs.

Effort: XL/XXL.

## Recommended NFR Path

Start with Option 1, add Option 2 for generated RV32I, and reserve Option 3 for the RV64 Linux SoC milestone.
