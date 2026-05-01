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

## New Verification After Runtime Window And Readback Fixes

- Date:
  - 2026-05-01
- Commands:
  - `bin/simple test test/unit/hardware/fpga_linux/riscv_fpga_linux_spec.spl`
  - `bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_generated_rv64_boot_info_dtb_runner.shs --payload-elf build/os/ghdl_boot_info_probe_payload.elf --timeout=20 --max-cycles 50000`
  - `bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_generated_rv64_boot_info_dtb_runner.shs --payload-elf build/os/ghdl_boot_info_payload.elf --timeout=20 --max-cycles 50000`
- Result:
  - the generated bench now backs an 8 MiB contiguous window from `0x80000000`, so the runtime stack / mailbox-adjacent region around `0x80610xxx` is no longer silently dropped
  - the bench now toggles a small memory-epoch signal on RAM writes so same-address read-after-write no longer stays stale inside the DTB lane
  - bounded probe payload evidence improved:
    - before the readback fix, a read from `0x80610F90` still returned `0x00000000` immediately after a write of `0x55667788`
    - after the fix, the same read returns `0x55667788`
  - bounded main boot-info payload evidence improved:
    - the run still reaches the deeper boot-info helper PCs around `0x8020C95x`
    - the run now continues until a later failing end-state at `PC_HEX32=8020B706`
  - the repo-native lane still does **not** satisfy the DTB proof contract:
    - `MAGIC_LOW32: 0`
    - `DTB_ADDR_HEX32: 00000000`
    - `DTB_PROBE_SEEN: false`
    - `UART_MARKER_SEEN: false`
    - `GENERATED_RV64_BOOT_INFO_DTB: FAIL`

## Current Interpretation After These Fixes

- The bench is no longer failing for the original two reasons:
  - missing runtime RAM backing for `0x8060xxxx`
  - stale same-address read-after-write in the shared-variable RAM model
- The remaining blocker is guest/core behavior again, not silent bench memory loss.
- The strongest current symptom is:
  - bounded boot-info payloads still fail to complete their proof mailbox / DTB contract
  - the main payload ends in a later trap/end-state around `PC_HEX32=8020B706`
- Next investigation should stay on the generated core / guest-side execution path, starting from the instruction stream around that later PC and the remaining boot-info / MMIO contract usage.

## New Verification After RV64 `lw` Lane And `c.xor` Decompress Fixes

- Date:
  - 2026-05-01
- Commands:
  - `bin/simple test test/unit/hardware/fpga_linux/riscv_fpga_linux_spec.spl`
  - `bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_generated_rv64_boot_info_dtb_runner.shs --payload-elf build/os/ghdl_boot_info_payload.elf --timeout=20 --max-cycles 50000`
- Result:
  - the RV64 core now lane-selects `lw` correctly for aligned word loads in the upper half of a 64-bit memory beat
  - the RV64C decompressor now expands the previously missing `c.xor` subcase, which matched the old terminal helper PC at `0x8020B706`
  - the bounded DTB payload no longer ends in the prior trap state:
    - previous bounded end-state: `TRAP_SEEN='1'`, `PC_HEX32=8020B706`
    - new bounded end-state at `MAX_CYCLES=50000`: `TRAP_SEEN='0'`, `PC_HEX32=80209C8E`
  - the DTB proof contract still does not complete:
    - `MAGIC_LOW32: 0`
    - `DTB_ADDR_HEX32: 00000000`
    - `DTB_PROBE_SEEN: false`
    - `UART_MARKER_SEEN: false`
    - `GENERATED_RV64_BOOT_INFO_DTB: FAIL`
  - a suspicious early aligned write/read pair at `0x80610E40` still appears in bounded traces and remains worth revisiting, but it is no longer the top-level terminal signature

## Current Interpretation After `c.xor` Fix

- The missing compressed-ALU decode was a real generated-core bug and materially advanced execution.
- The repo-native RV64 Linux lane now survives past the previous `rt_native_eq` trap point and continues running until the bounded cycle cap.
- The next debugging target should move forward with execution, centered on the later path around `PC_HEX32=80209C8E`, while keeping the earlier `0x80610E40` readback anomaly as a secondary core-state suspect.

## New Verification After `calloc` Register And Frame Instrumentation

- Date:
  - 2026-05-01
- Commands:
  - `bin/simple test test/unit/hardware/fpga_linux/riscv_fpga_linux_spec.spl`
  - `bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_generated_rv64_boot_info_dtb_runner.shs --payload-elf build/os/ghdl_boot_info_payload.elf --timeout=20 --max-cycles 200000 --log-path /tmp/rv64_calloc_debug2.log --uart-log-path /tmp/rv64_calloc_debug2.uart`
- Result:
  - bounded progress still lands inside `calloc`:
    - `PROGRESS_PC_HEX32: 80209C9C` at 100k cycles
    - `PROGRESS_PC_HEX32: 80209C8E` at 200k cycles
  - direct register/frame instrumentation shows this is not just a large-but-sane zeroing loop:
    - `RA_HEX32: 80209C6A`
    - `S0_HEX32: 80610A50`
    - `A0_HEX32: 00002041`
    - `A1_HEX32: 80612AC1`
    - `S0_M64_HEX32: 00002042`
    - `S0_M56_HEX32: 80610A80`
    - `S0_M40_HEX32: 80215460`
  - interpretation of those slots in `calloc`:
    - `s0-64` is the loop index local
    - `s0-56` is the saved base pointer returned by `rv_alloc`
    - `s0-40` is the saved total byte count (`nmemb * size`)

## Current Interpretation After `calloc` Frame Dump

- The `calloc` frame locals are nonsensical for a healthy allocator call:
  - saved base pointer `s0-56 = 0x80610A80` looks stack-like, not like the expected heap region near `g_heap`
  - saved byte-count `s0-40 = 0x80215460` looks pointer/code-data-like, not like a reasonable allocation size
- This means the current blocker is stronger than “bytewise zeroing is slow”:
  - either the allocator inputs are already corrupted before/during `calloc`
  - or an earlier execution bug is corrupting `calloc` frame locals in RAM
- The earlier `0x80610E40` aligned readback anomaly is now demoted further; the priority target is the `rt_alloc` caller chain and the provenance of the corrupted `calloc` locals.

## New Verification After Registered DTB Bench Read Response

- Date:
  - 2026-05-01
- Commands:
  - `bin/simple test test/unit/hardware/fpga_linux/riscv_fpga_linux_spec.spl`
  - `bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_generated_rv64_boot_info_dtb_runner.shs --payload-elf build/os/ghdl_boot_info_payload.elf --timeout=20 --max-cycles 200000 --log-path /tmp/rv64_calloc_debug5.log --uart-log-path /tmp/rv64_calloc_debug5.uart`
- Change under test:
  - switched the generated RV64 boot-info DTB bench from combinational `dmem_rdata` readback to a registered one-cycle read response in the clocked process
- Result:
  - the old stale-read symptom disappeared:
    - `DMEM_READ_EVENT_ADDR_HEX32: 80610E40`
    - `DMEM_READ_EVENT_DATA_HEX32: 524F4F46`
  - the allocator path now receives sane arguments again:
    - `WATCH_RT_ALLOC_RELOAD_S0_M24_HEX32: 00000050`
    - `WATCH_RT_ALLOC_RELOAD_S0_M32_HEX32: 00000050`
    - `WATCH_RT_ALLOC_RELOAD_A0_HEX32: 00000050`
    - `WATCH_CALLOC_SPILL_A0_HEX32: 00000001`
    - `WATCH_CALLOC_SPILL_A1_HEX32: 00000050`
  - bounded execution no longer stalls in `calloc`; it halts after `boot_main` returns:
    - `CYCLES: 47672`
    - `HALT_SEEN: '1'`
    - `TRAP_SEEN: '0'`
    - `PC_HEX32: 8020C5DC`
  - boot-info bring-up now reaches later success markers:
    - `MAGIC_LOW32: 1380929350` (`0x524F4F46`, low 32 bits of `PROOF_MAGIC_EXPECTED`)
    - `DONE_LOW32: 1`
    - `DTB_PROBE_SEEN: true`
    - `DTB_PROBE_ADDR_HEX32: 88000000`
    - `UART_MARKER_SEEN: true`
  - but the proof contract is still incomplete at halt:
    - `DTB_ADDR_HEX32: 00000000`
    - `RAM_BASE_HEX32: 00000000`
    - `RAM_SIZE_HEX32: 00000000`
    - `SERIAL_BASE_HEX32: 00000000`
    - `MAP_LEN_LOW32: 0`

## Current Interpretation After Registered Read Fix

- The earlier `calloc` corruption was not a guest allocator bug; it was caused by the generated DTB bench returning stale data on the load path.
- The registered read response fixed both:
  - the `rt_alloc`/`calloc` argument corruption
  - the earlier same-address readback anomaly at `0x80610E40`
- The primary blocker has moved again:
  - execution now returns from `boot_main` and halts cleanly
  - but the proof mailbox still does not receive the expected boot-info fields even though DTB parsing and UART progress are clearly happening
- The next target is no longer memory-model plumbing. It is the boot-info proof/output path between successful boot parsing and the mailbox writes checked by the bounded DTB contract.

## New Verification After Narrow RV64 Proof Runtime

- Date:
  - 2026-05-01
- Commands:
  - `cargo build -p simple-driver --bin simple --features llvm` (from `src/compiler_rust`)
  - `SIMPLE_LINKER_DEBUG=1 SIMPLE_BOOT_MINIMAL=1 src/compiler_rust/target/debug/simple native-build --verbose --backend llvm --timeout 120 --entry-closure --source examples/simple_os/arch/riscv64 --source src/os --entry examples/simple_os/arch/riscv64/ghdl_boot_info_entry.spl --target riscv64-unknown-none -o /tmp/ghdl_boot_info_payload_new.elf --linker-script examples/simple_os/arch/riscv64/linker.ld`
  - `bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_generated_rv64_boot_info_dtb_runner.shs --payload-elf /tmp/ghdl_boot_info_payload_new.elf --timeout=20 --max-cycles 200000 --log-path /tmp/rv64_proof_trace6.log --uart-log-path /tmp/rv64_proof_trace6.uart`
  - `bin/simple test --clean test/unit/hardware/fpga_linux/riscv_fpga_linux_spec.spl`
- Change under test:
  - replaced broad RV64 boot auto-discovery for `ghdl_boot_info*` proof entries with a proof-only runtime object `examples/simple_os/arch/riscv64/boot/ghdl_boot_info_runtime.c`
  - restored the required C `_start` trampoline in `.text.entry` while keeping only the minimal runtime symbols needed by the narrow proof payload
- Result:
  - the LLVM-enabled build now proves the linker is taking the narrow path:
    - `Boot autodiscovery skipped for .../ghdl_boot_info_entry.spl`
    - `Boot C source: .../boot/ghdl_boot_info_runtime.c`
    - `Freestanding unresolved symbol check: 0 unexpected symbol(s)`
    - payload size dropped to `69 KB`
  - the first narrow-runtime attempt without `_start` failed immediately because execution started at `80200000 <malloc>`; adding the `_start -> spl_start` trampoline fixed that false failure mode
  - the corrected narrow payload now enters the intended SPL path:
    - `HEARTBEAT_PC_HEX32: 80208244` (`ghdl_boot_info_entry__boot_main`)
    - execution advances through the prologue and the first `proof_store_u64` call site
  - the bounded run still fails, but much later than the entry/runtime shape failures:
    - progress reaches `PC_HEX32` through `0x802082C0`
    - `TRAP_SEEN: '1'`
    - final summary still leaves mailbox fields zeroed:
      - `MAGIC_LOW32: 0`
      - `DONE_LOW32: 0`
      - `DTB_PROBE_SEEN: false`
      - `UART_MARKER_SEEN: false`
  - DMEM traces show regular stack/heap traffic and a successful readback of `0x524F4F46`, so this is no longer an “entry never ran” failure

## Current Interpretation After Narrow Proof Runtime

- The narrow RV64 proof lane is now software-correct enough to:
  - link cleanly with an LLVM-enabled compiler
  - start at the proper `_start`
  - reach `ghdl_boot_info_entry__boot_main`
- The remaining failure is after entry/runtime bring-up, not before it.
- The next target is to determine why the first proof-output path still does not surface as a mailbox write at `0x80600000` even though:
  - `ghdl_boot_info_proof_layout__proof_store_u64` computes `0x80600000 + slot * 8`
  - `rt_mmio_write_u64` itself compiles to the expected `sd a0, 0(a1)` store sequence
- That points the next pass back toward the generated RV64 execution/bench interaction on this later narrow proof path, rather than linker wiring or missing freestanding support.
