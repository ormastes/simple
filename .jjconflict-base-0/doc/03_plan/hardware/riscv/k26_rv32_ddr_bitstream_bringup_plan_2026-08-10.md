# K26 RV32-DDR bitstream synthesis + board bringup — execution plan

Date: 2026-08-10
Source research: `doc/01_research/os/simpleos/board_bringup_next_steps_2026-08-10.md`
(commit `c910fb1d427`). Read it in full first. Scope here is the K26/KV260 RV32
soft-core DDR lane only; the generated-RTL-Linux milestones stay in
`doc/03_plan/hardware/riscv/riscv32_riscv64_fpga_simpleos_production.md` and
are untouched. Board-runnable rule: `.claude/rules/board-runnable.md`.

## State (verified 2026-08-10)

Everything is PRESENT except one artifact: hardware (ML Carrier Card serial
`XFL1OSWWFM2B` at `/dev/ttyUSB0-3`), Vivado 2025.2, RISC-V objcopy/nm, RTL
(`examples/09_embedded/fpga_riscv/rtl/soc_top_rv32_k26_ddr.vhd` + 3 siblings),
build script `scripts/fpga/build_k26_rv32_ddr_bitstream.shs`, bringup script
`scripts/fpga/bringup_kv260_rv32_ddr.shs`. Missing:
`build/fpga/k26_rv32_ddr/k26_rv32_ddr.bit` — one 30–60 min (up to 90+ min on a
loaded host) Vivado synthesis job.

## Scope

IN: run synthesis; run automated bringup; capture and land board evidence per
the board-runnable evidence bar (board identity + boot path + transcript).
OUT (deferred): fabric-UART external wiring (PMOD J2 H12 is not routed to the
FT4232H; JTAG/xsdb observation is the path — this does NOT block bringup);
aarch64 EFI-stub gap (tracked separately); x86_64 WM-on-hardware (different
board, orthogonal).

## Ordered steps

1. Host-saturation preflight (HARD — this is the collision risk with tonight's
   parallel agents): `free -h` must show ≥30 GB free; `pgrep -f
   '[l]nx64\.o/vivado'` empty; `pgrep -f '[s]imple .*native-build'` empty. The
   script fail-closes on all three; do NOT set `ALLOW_CONCURRENT_BUILD=1` or
   `ALLOW_LOW_MEM=1` while other agents may launch builds — a Vivado job OOMing
   or starving a bootstrap wastes hours on both sides. If the host is
   contended, DEFER this track rather than override.
2. Synthesis: from repo root,
   `sh scripts/fpga/build_k26_rv32_ddr_bitstream.shs 2>&1 | tee <scratch>/k26_build.log`,
   run FOREGROUND with self-polling (background Bash gets SIGTERM'd at 600 s —
   known trap; use run_in_background + Monitor-style polling of the log, never
   a blocking wait). Watch for `SYNTH_WNS`, `IMPL_WNS`, `BITSTREAM_WRITTEN`.
   Acceptance: exit 0 and `build/fpga/k26_rv32_ddr/k26_rv32_ddr.bit` exists
   (~4–5 MB) with timing MET (exit 3 = negative slack; 5/6 = synth/impl fail —
   read `vivado.log`, do not retry blind).
3. Payload check before bringup: SimpleOS RV32 kernel ELF at
   `build/os/simpleos_riscv32_smf_fs.elf` and FAT32 image at
   `build/os/fat32-riscv32.img`; build them first if absent (this is the only
   possible extra dependency; the bringup script derives `.bss` offsets from
   the ELF at runtime — never hardcode offsets).
4. Bringup: `sh scripts/fpga/bringup_kv260_rv32_ddr.shs 2>&1 | tee <scratch>/k26_bringup.log`
   (~5–10 min, automated: JTAG chain, A53 halt + cache-invalidate reset,
   mandatory `psu_init` from the XSA, program bitstream, PS-PL isolation
   removal, control-slave magic check `0x52563332` at `0xA0000000+0x24`, DDR
   load + word0 coherency verify, core release, UART transcript poll).
   Acceptance ladder: exit 0 = `TEST PASSED`; exit 2 = boot marker
   (`SimpleOS RV32 boot OK`) without TEST PASSED — partial, still landable
   evidence; exit 3 or `CTRL_MAGIC_MISMATCH` = PL/AXI broken, stop and triage
   from `build/fpga/k26_rv32_ddr/bringup/bringup.log`.
5. Evidence landing: save transcript to
   `doc/09_report/board_evidence/simpleos_rv32_k26_bring_up_transcript_2026-08-10.txt`
   with board identity (`BOARD_JTAG_CHAIN_*` block), `CTRL_MAGIC`,
   `DDR_*_WORD0`, `CORE_RELEASED`, `UART_BYTE_COUNT`, and the
   `TRANSCRIPT_BEGIN/END` body; land via plumbing, blob-verify at the tip.
   Update `doc/08_tracking/bug/simpleos_wm_lane_not_board_runnable_2026-08-08.md`
   with the evidence path.

Optional zero-cost probe while waiting or if deferring synthesis: the JTAG
chain/idcode xsdb probes in research §"Partial Verification" prove board
reachability only (no PL/DDR/soft-core claims — do not oversell it).

## Dependencies / risks

- Independent of both the WM rung-(d) track and the blink paint track — no
  shared code, only shared HOST RESOURCES (RAM/CPU). That resource collision is
  the main risk: schedule synthesis in a window with no `native-build` /
  bootstrap activity.
- Multi-hour-stall risk is the highest of the three tracks: one timing-fail or
  OOM burns the whole window. Mitigate by never overriding the guardrails and
  by reading exit codes instead of retrying.
- Evidence honesty: `TEST PASSED` must come from the kernel transcript, not the
  script scaffolding; exit 2 is reported as partial boot, never as full pass.
