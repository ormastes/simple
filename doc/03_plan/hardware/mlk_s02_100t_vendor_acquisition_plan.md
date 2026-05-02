# MLK-S02-100T Vendor Acquisition And Integration Plan

**Date:** 2026-05-01
**Board:** MiLianKe `MLK-S02-100T`
**Status:** Waiting on vendor resource acquisition

## Goal

Acquire the authoritative vendor files needed to turn the current `MLK-S02-100T` scaffolds into real board support.

## What To Download

Download the MiLianKe resource bundle for:
- `MLK-S02-35T-100T`

From that bundle, the important files are:
- XDC constraint files: `*.xdc`
- Vivado project files: `*.xpr`
- Vivado script files: `*.tcl`
- Board-level wrapper or top files:
  - `*_top.v`
  - `*_top.vhd`
  - `*_wrapper.v`
  - `*_wrapper.vhd`
- Simple LED or GPIO examples
- UART or serial examples
- Clock/reset wiring examples
- DDR3 reference design files, if present
- README or PDF notes that explain jumper, clock, reset, and UART behavior

## Where To Download From

Primary vendor locations:
- `https://www.uisrc.com/download.html`
- `https://www.uisrc.com/download_list-0-0-0-1-1.html`

Supporting public references:
- Hardware manual:
  - `https://www.cnblogs.com/milianke/p/17683342.html`

## User Prerequisites

The user likely needs:
- a `uisrc.com` account
- purchase access or a membership that allows downloading `MLK-S02-35T-100T`
- ability to extract common archive types:
  - `.zip`
  - `.7z`
  - `.rar`

`Vivado` is not required just to download or unpack the vendor bundle.

`Vivado` becomes useful or required depending on what the bundle contains:

- If the bundle includes a ready-made `.bit` file and you only want to try programming it:
  - `Vivado` may be optional
  - `openFPGALoader` might be enough for an initial load attempt
- If the bundle includes only source projects, or if you need to rebuild, inspect IP, regenerate outputs, or modify the design:
  - AMD/Xilinx `Vivado` is effectively required
- If the bundle contains a `.xpr` project:
  - `Vivado` is required to open and validate it properly

If the vendor bundle includes Vivado projects, the user should install:
- AMD/Xilinx `Vivado`
- preferably the version recommended by the vendor bundle docs, if specified

Useful host tools:
- `7z` or another archive extractor
- `rg` for searching unpacked files
- optional: `openFPGALoader`, `openocd`

## What To Do Right After Download

After the vendor files are downloaded and unpacked, do this first:

1. Check whether the bundle contains a ready-made bitstream:
   - `*.bit`
2. Check whether the bundle contains a Vivado project:
   - `*.xpr`
3. Check whether the bundle contains an authoritative constraint file:
   - `*.xdc`
4. Check whether the bundle contains a simple reference top:
   - LED demo
   - UART demo
   - board test project

Decision point:

- If there is a usable `.bit`:
  - we can try a cautious programming step before full project integration
- If there is no `.bit` but there is a `.xpr` or source-only design:
  - install `Vivado` next
- If there is an `.xdc` and top-level sources but no obvious project:
  - I can still integrate the real pin map and wrapper, but a real build step will still need `Vivado`

## Where To Place The Downloaded Files

Put the raw vendor bundle under:
- `third_party/board_vendor/mlk_s02_100t/`

Recommended layout:

```text
third_party/board_vendor/mlk_s02_100t/
├── README.md
├── raw/
│   ├── <downloaded-archive-1>
│   └── <downloaded-archive-2>
└── unpacked/
    └── <vendor-project-files>
```

## Manual Steps For The User

1. Log into `uisrc.com`.
2. Open the `MLK-S02-35T-100T` resource entry.
3. Download the vendor archive or archives.
4. Put the original archives into:
   - `third_party/board_vendor/mlk_s02_100t/raw/`
5. Extract them into:
   - `third_party/board_vendor/mlk_s02_100t/unpacked/`
6. Tell me when that directory is populated.

## What I Will Do After The Download Is Present

Once the vendor files exist locally, I will:

1. Identify the authoritative XDC and compare it against the current scaffold:
   - `examples/09_embedded/fpga_riscv/constraints/mlk_s02_100t.xdc`
2. Replace the commented placeholder XDC with real pin assignments.
3. Identify the vendor top-level wrapper or reference design.
4. Map the vendor wrapper onto the repo’s logical interface contract:
   - `clk25`
   - `rst_n`
   - `uart_tx`
   - `uart_rx`
   - `led[7:0]`
   - `btn[3:0]`
5. Update:
   - `examples/09_embedded/fpga_riscv/rtl/mlk_s02_100t_wrapper_stub.vhd`
   into a real wrapper or replace it with a verified one.
6. Update:
   - `examples/09_embedded/fpga_riscv/build_mlk_s02_100t.tcl`
   - `examples/09_embedded/fpga_riscv/program_mlk_s02_100t.tcl`
   so they reflect the actual project files and bitstream path.
7. Add a minimal board proof target:
   - LED blink or LED pattern example
   - UART hello example, if the vendor design supports it
8. Update docs and status files with the verified flow.

## What You Should Do After The Download Is Present

After you place the files under `third_party/board_vendor/mlk_s02_100t/`, the next user actions are:

1. Tell me the vendor files are present.
2. If there is no `.bit` but there is a Vivado project or source-only design, install `Vivado`.
3. If you install `Vivado`, tell me the installed command path or confirm `vivado` is on `PATH`.
4. If the bundle includes multiple example projects, tell me whether you prefer:
   - LED first
   - UART first
   - vendor default demo first

If you do not choose, I will default to the simplest board proof:
- LED first

## Preferred First Verification After Integration

The first real board proof should be one of:
- static LED pattern
- blinking LED
- UART banner at `115200`

That keeps the first hardware pass simple and easy to validate.

## Current Repo Files That Will Be Updated Later

- `config/resources/boards/mlk_s02_100t.sdn`
- `examples/09_embedded/fpga_riscv/constraints/mlk_s02_100t.xdc`
- `examples/09_embedded/fpga_riscv/rtl/mlk_s02_100t_wrapper_stub.vhd`
- `examples/09_embedded/fpga_riscv/build_mlk_s02_100t.tcl`
- `examples/09_embedded/fpga_riscv/program_mlk_s02_100t.tcl`
- `doc/07_guide/hardware/xilinx_fpga_board_bringup.md`
- `doc/07_guide/hardware/simple_generated_fpga_rtl.md`

## Success Condition

This plan is complete when:
- vendor bundle is present locally
- XDC is authoritative
- wrapper is wired to real board signals
- build script produces a bitstream
- programming path is tested
- one minimal runtime proof is observed on the real board
