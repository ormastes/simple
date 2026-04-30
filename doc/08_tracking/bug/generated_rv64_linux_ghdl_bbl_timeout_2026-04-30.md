# Generated RV64 Linux GHDL BBL Timeout

Date: 2026-04-30
Status: Open

## Summary

The repo-native `generated_rv64_linux` lane now reaches real GHDL execution with a
file-backed payload loader, but the full Linux-capable `build/third_party/rtl/cva6-sdk/v0.3.0/bbl`
payload still times out without any observed UART output.

## Observed Behavior

- Command:
  - `scripts/rtl_riscv64_linux_generated.shs --skip-proofs --timeout=120`
- Result:
  - `MARKER_MISSING: OpenSBI`
  - `MARKER_MISSING: Linux version`
  - `MARKER_MISSING: Freeing unused kernel memory`
  - `[GHDL-GEN-RV64-BOOT-INFO-DTB] TIMEOUT after 120s`
- Artifact state:
  - `build/rtl_linux/generated_rv64/generated_rv64_linux_runner.log` remained `0` bytes
  - `build/rtl_linux/generated_rv64/generated_rv64_linux_uart.log` remained `0` bytes
- Follow-up diagnostic runs:
  - with preload progress reporting every `1_000_000` bytes, a `30s` run still produced no preload log lines
  - with preload progress reporting every `100_000` bytes, a `15s` run still produced no preload log lines
  - interpretation: the time-0 VHDL textio preload path does not reach even `100_000` payload bytes inside `15s` of wall-clock time for the `bbl` image

## What Changed

- The generated DTB lane no longer embeds a multi-megabyte payload as VHDL byte-array literals.
- Firmware and payload are converted to hex files and loaded by the testbench from disk.
- The long-running lane now reaches `ghdl -r`; the earlier `ghdl -e` payload-scaling bottleneck is removed.
- The DTB Linux runner hot path no longer uses `bin/simple run` to generate the full-`bbl` preload files. It now writes word-oriented preload files and the small `test_program.vhd` package directly in the Bash/Python setup path, which gets the real lane through payload preparation, `ghdl -a`, and `ghdl -e`.
- The Linux DTB runner no longer flattens the whole `bbl` ELF into the payload slot.
  - It now detects the `bbl` shape and splits it into:
    - a machine image at `0x80000000`
    - a `.payload` image at `0x80200000`
- The generated DTB testbench no longer uses a single monolithic full-RAM copy for Linux payload streaming.
  - FW preload is separate.
  - Payload loading is chunked with scheduled yields.
  - Full-array RAM copies were removed from the chunked payload path.
- The bounded generated RV64 proof stack is now green again from the generated bundle path:
  - `ghdl_generated_rv64_fw_jump_runner.shs`
  - `ghdl_generated_rv64_boot_info_real_dtb_runner.shs`
  - `ghdl_generated_rv64_sv39_runner.shs`
  - `ghdl_generated_rv64_sv39_fault_runner.shs`

## Latest Verification

- Date:
  - 2026-04-30
- Commands:
  - `timeout 45 bash -x src/lib/nogc_async_mut_noalloc/baremetal/ghdl_generated_rv64_boot_info_dtb_runner.shs --payload-elf build/third_party/rtl/cva6-sdk/v0.3.0/bbl --timeout=15 --max-cycles 200000000 --log-path /tmp/generated_rv64_runner_trace.log --uart-log-path /tmp/generated_rv64_uart_trace.log --expect-marker OpenSBI --expect-marker "Linux version" --expect-marker "Freeing unused kernel memory"`
  - `bash scripts/rtl_riscv64_linux_generated.shs --skip-proofs --timeout=120`
- Result:
  - the runner now gets through payload conversion, `ghdl -a`, and `ghdl -e`
  - `ghdl -r` starts under the expected timeout wrapper
  - a clean short split-ELF run such as:
    - `bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_generated_rv64_boot_info_dtb_runner.shs --payload-elf build/third_party/rtl/cva6-sdk/v0.3.0/bbl --timeout=10 --max-cycles 200000000 --log-path /tmp/generated_rv64_clean.log --uart-log-path /tmp/generated_rv64_clean.uart --expect-marker OpenSBI`
    now also reaches the split-ELF `ghdl -r` path and ends with:
    - `MARKER_MISSING: OpenSBI`
    - `[GHDL-GEN-RV64-BOOT-INFO-DTB] TIMEOUT after 10s`
    - empty raw log and empty UART log
  - after `120s`, the generated lane still reports:
    - `MARKER_MISSING: OpenSBI`
    - `MARKER_MISSING: Linux version`
    - `MARKER_MISSING: Freeing unused kernel memory`
    - `[GHDL-GEN-RV64-BOOT-INFO-DTB] TIMEOUT after 120s`
  - raw runner and UART logs remained `0` bytes for that run
  - host-side `strace` on the full DTB lane shows `ghdl -r` opening both generated preload files but issuing no `read(...)` on them before timeout
  - moving `file_open(...)` out of the preload-process declarative region and into the process body still produces no `PRELOAD_*_PROCESS_START` markers within `15s`
  - a temporary reduced-memory experiment with `MEM_WORDS := 65536` does begin issuing `read(...)` on `fw_stub.hex`, which points at startup cost of the dense memory object rather than at the loader loop itself

## New Verification After Runtime Fixes

- Date:
  - 2026-04-30
- Commands:
  - `bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_generated_rv64_fw_jump_runner.shs examples/09_embedded/fpga_riscv/sw/generated_rv64_fw_jump_smoke.s --timeout=30`
  - `bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_generated_rv64_boot_info_dtb_runner.shs --payload-elf /tmp/rv64_dtb_smoke_fixed_uH3mVl/payload.elf --timeout=30`
  - `scripts/rtl_riscv64_linux_generated.shs --skip-proofs --timeout=30`
- Result:
  - the DTB lane is no longer silent:
    - `PRELOAD_FW_PROCESS_START`
    - `PRELOAD_FW_READY`
    - `PRELOAD_PAYLOAD_PROCESS_START`
    - `RESET_PROCESS_START`
    - heartbeat PC / privilege / instruction traces
  - the shared-variable RAM model plus `-frelaxed` gets the lane past the previous `ghdl -r` startup wall
  - the Python preload writer was also fixed so short final chunks are packed correctly
  - repo-style ELF payloads with `.text.payload` are now split correctly, not flattened into the payload slot
  - the bounded DTB smoke payload now reaches S-mode payload execution, DTB reads, proof-memory writes, and UART `FAIL`
  - the real Linux `bbl` lane now reaches OpenSBI runtime instead of dying before first observable execution
  - `bbl` no longer traps on the first `csrr mhartid`; the generated core now answers:
    - `misa = 0x800000000014112D`
    - `mvendorid = 0`
    - `marchid = 0`
    - `mimpid = 0`
    - `mhartid = 0`
  - the Linux lane still fails before `OpenSBI` UART output:
    - one run reached a trap at `PC=0x800065A0` inside OpenSBI `strcmp`, which exposed a missing RV64C `C.SUBW` decode path
    - after adding that decompression case, the lane progressed further and later trapped at `PC=0x80001ED2`
    - `MARKER_MISSING: OpenSBI`
    - `MARKER_MISSING: Linux version`
    - `MARKER_MISSING: Freeing unused kernel memory`

## Current Interpretation

- This is no longer a packaging/elaboration/startup-silence failure.
- This is no longer blocked on flat-`bbl` misuse or the old dense-signal preload wall.
- The generated lane did truthfully reach OpenSBI machine-mode code and expose missing ISA / privileged-runtime coverage gaps.
- The latest runtime work fixed the next two concrete firmware blockers:
  - `mcounteren` / `scounteren` CSR state is now implemented in the generated core
  - `misa` now advertises the generated core surface that is actually implemented:
    - `A/C/I/M/S/U`
    - no longer `F/D`
- The strongest current evidence is:
  - after the `misa` correction, the lane is no longer ending at a traced OpenSBI trap PC
  - instead, the GHDL DTB simulation now crashes at host runtime before any UART or runner markers are emitted
  - that crash reproduces both for:
    - the full Linux `bbl` payload
    - the tiny DTB smoke payload
- The active blocker is now the generated DTB bench / GHDL runtime path, not the previously traced OpenSBI instruction sequence.

## Next Step

Stabilize the generated DTB simulation runtime before continuing firmware bring-up:

- isolate why `ghdl -r` is now crashing with:
  - `timeout: the monitored command dumped core`
  - `Segmentation fault`
- keep a bounded tiny-payload reproducer in the loop so host-runtime stability can be tested without Linux-scale runtime noise
- once the bench is stable again, resume the previous OpenSBI PC-by-PC compatibility loop until `OpenSBI` UART appears

PC / privilege / UART instrumentation should remain in the lane; it was useful before the current
runtime crash and will be needed again after the bench is stable.

## New Verification After CSR And MISA Fixes

- Date:
  - 2026-05-01
- Commands:
  - `bin/simple test test/unit/hardware/fpga_linux/riscv_fpga_linux_spec.spl`
  - `scripts/rtl_riscv64_linux_generated.shs --skip-proofs --timeout=30`
  - `bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_generated_rv64_boot_info_dtb_runner.shs --payload-elf build/third_party/rtl/cva6-sdk/v0.3.0/bbl --timeout=30 --max-cycles 50000 --log-path /tmp/gen_rv64_bounded.log --uart-log-path /tmp/gen_rv64_bounded.uart`
  - `bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_generated_rv64_boot_info_dtb_runner.shs --payload-elf /tmp/.../payload.elf --timeout=30 --log-path /tmp/gen_rv64_smoke.log --uart-log-path /tmp/gen_rv64_smoke.uart`
- Result:
  - the generated core unit/spec still passes
  - the generated Linux wrapper now compiles the regenerated DTB bench cleanly again after Simple-owned VHDL declaration-order and subtype fixes
  - the latest runner logs no longer show a traced guest trap PC
  - instead, both the full Linux payload and the tiny DTB smoke payload end with:
    - `timeout: the monitored command dumped core`
    - `Segmentation fault`
  - both corresponding UART logs remain empty
  - current repo-facing wrapper output is therefore:
    - `MARKER_MISSING: OpenSBI`
    - `MARKER_MISSING: Linux version`
    - `MARKER_MISSING: Freeing unused kernel memory`
    - `[GHDL-GEN-RV64-BOOT-INFO-DTB] FAIL`

## New Verification After Region-Windowed Bench Recheck

- Date:
  - 2026-05-01
- Commands:
  - `bin/simple run src/hardware/fpga_linux/generate_riscv_fpga_bundle.spl -- /tmp/rv64_regen_test`
  - direct unwrapped `ghdl -r` reproducer against `build/os/ghdl_boot_info_payload.elf`
  - `bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_generated_rv64_boot_info_dtb_runner.shs --payload-elf build/os/ghdl_boot_info_payload.elf --timeout=20 --log-path /tmp/generated_dtb_run.log --uart-log-path /tmp/generated_dtb_uart.log`
- Result:
  - the DTB bench generator is syntactically back to a coherent state
  - the wrapped runner still times out silently with empty persisted logs
  - the unwrapped direct run is more truthful and now shows the first-cycle failure clearly:
    - `PRELOAD_FW_WORD0_LOW32: 4010029B`
    - `PRELOAD_FW_WORD0_HIGH32: 01529293`
    - `RESET_REGION0_WORD0_LOW32: 00000000`
    - `RESET_REGION0_WORD0_HIGH32: 00000000`
    - `HEARTBEAT_PC_HEX32: 80000000`
    - `HEARTBEAT_IMEM_HEX32: 00000000`
    - `TRAP_SEEN: '1'`
  - this proves the region-windowed signal-backed RAM bench is exposing zeroed memory to the CPU at reset release even though the FW preload variable contains the expected first word
  - the active blocker is therefore not OpenSBI yet; it is the current region-windowed DTB bench memory-visibility model

## Updated Interpretation

- The temporary region-windowed signal-backed bench is not yet a valid replacement for the older flat/shared-memory loader.
- The generated core is trapping at the first instruction because the bench is not making the FW preload visible at reset release.
- Once the bench is restored to a truthful memory model, the next likely guest-side blocker is still generated-core ISA support, with AMO/A-extension coverage the strongest locally supported candidate for the earlier deeper `bbl` failure around `PC_HEX32=00380000`.
