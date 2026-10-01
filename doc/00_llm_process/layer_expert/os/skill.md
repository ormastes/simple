# os Layer Expert

## Role

Maintain process knowledge for the `os` layer: owned source, architecture links, expected tests, and boundary rules. Use this skill when a task changes `src/os` or depends on its public behavior.

## Pipeline Links

- [research](../skill_command/skills/pipe/research/skill.md)
- [design](../skill_command/skills/pipe/design/skill.md)
- [impl](../skill_command/skills/pipe/impl/skill.md)
- [verify](../skill_command/skills/pipe/verify/skill.md)
- [release](../skill_command/skills/pipe/release/skill.md)

## Layer Links

- [Source](../../../src/os/)
- [Architecture index](../../04_architecture/README.md)
- [Architecture modules](../../04_architecture/architecture_modules.md)
- [Design docs](../../05_design/)
- [Specs](../../06_spec/)

## Boundary Rules

- Pure Simple first: never a C implementation where pure Simple can do it; the C runtime is a boundary, not a place for logic. Bootstrap-required C keeps a pure-Simple twin (`scripts/check/check-dual-run-shadow.shs`). HAL code minimizes inline asm (typed register views > optimization-restraining tags > intrinsics > asm for irreplaceable ops only). Full policy: [pure_simple_hal.md](../../../07_guide/os/hal/pure_simple_hal.md).

## Update Rule

When project work changes this layer's public contract, source ownership, tests, architecture, or verification requirements, update this skill with current links and handoff notes.

Template: [layer_skill.md](../../template/layer_skill.md)

## Board bring-up notes (2026-09-26/27)

### Cortex-M (Arduino UNO Q / STM32U585, RA4M1, QEMU mps2)

- **ARM32 bare-metal triples must keep the M-profile arch.** Collapsing
  `thumbv8m.main-none-eabi` to `armv7` made LLVM emit A32 on a Thumb-only
  core (UsageFault UNDEFINSTR at the first instruction). Fixed in the backend
  (`llvm_arm32_baremetal_arch`, [backend](../backend/skill.md) § 2026-09-26);
  the presets carry `arch: "thumbv8m.main"`
  ([target_presets.spl](../../../../src/compiler/70.backend/target_presets.spl) :69).
- **Cortex-M images need the pure-Simple policy objects linked.** All three
  board runners (`run_simpleos_cortex_m33_qemu.shs`, `run_simpleos_stm32u585.shs`,
  `run_simpleos_ra4m1.shs`) previously compiled only the C shim; they now call
  [build-cortex-m-policy-objects.shs](../../../../scripts/os/build-cortex-m-policy-objects.shs)
  (`03553bcb5f6`). This is where the `@export("C")` bridge bug surfaced
  (unlinkable `os.kernel...cm33_policy_*` names) —
  [mir_lowering](../mir_lowering/skill.md) § 2026-09-26.
- **UNO Q console is LPUART1, not USART1** (`5afe174a685`,
  [board_stm32u585.h](../../../../src/os/kernel/arch/cortex_m33/board_stm32u585.h)).
  The header used to describe the NUCLEO layout (USART1 PA9/PA10). On the UNO
  Q: USART1 is PB6/PB7 = header D1/D0; the MCU<->MPU link is **LPUART1
  PG7(TX)/PG8(RX) AF8**, exposed by the Qualcomm side as `/dev/ttyHS1` @
  115200. Bring-up order: RCC `PWREN` (AHB3ENR bit 2) + `GPIOGEN` (AHB2ENR1
  bit 6) + `LPUART1EN` (APB3ENR bit 6), then `PWR_SVMCR.IO2SV` (bit 29) —
  PG[15:2] are VDDIO2-domain and read zero until it is set. Record:
  [uno_q_simpleos_flashed_uart_poll_never_completes_2026-09-26](../../../08_tracking/bug/uno_q_simpleos_flashed_uart_poll_never_completes_2026-09-26.md).

### StarFive JH7110 (VisionFive-2 class) — physical board boot over JTAG, 2026-09-27

Production `build/os/starfive-jh7110/simpleos.elf` booted to `simpleos>` on
the real board: Tigard JTAG load into DRAM at `0x48000000`, then U-Boot
`bootelf -s 0x48000000` over serial. Observed sequence:
`## Starting application at 0x40200000` -> `STARFIVE entry` ->
`console-ready` -> `filesystem-ready entries=bin,etc,README.txt` -> `BOOT OK`
-> `STARFIVE shell-ready` -> `simpleos>` (`ls /` answers `/bin /etc /README.txt`).

Reusable scripts (no rediscovery needed):
- [openocd-tigard-jtag.cfg](../../../../scripts/os/openocd-tigard-jtag.cfg) —
  the stock `interface/ftdi/tigard.cfg` matches `device_desc "Tigard V1.1"`;
  real units enumerate as `port A:Serial  port B:JTAG` and openocd fails
  `unable to open ftdi device`. Everything else in the stock file is right.
  The `starfive-jtag-*.shs` gates get the same effect with an inline
  `-c 'ftdi device_desc {...}'`.
- [boot-simpleos-starfive-jh7110-board.shs](../../../../scripts/os/boot-simpleos-starfive-jh7110-board.shs)
  — stage via [stage-simpleos-starfive-jh7110-jtag.shs](../../../../scripts/os/stage-simpleos-starfive-jh7110-jtag.shs)
  (`targets jh7110.u74_hart2; halt; load_image; verify_image; resume`, 1000 kHz
  verified), then `bootelf` over serial and marker-order assertion. The full
  `scripts/check/check-simpleos-starfive-jh7110.shs` gate re-runs the
  production build first; the helper does not.

Operator facts, all measured on the board:
- **Load to DRAM only — never write SPI flash / eMMC / SD.** A DRAM load is
  volatile; a power cycle restores stock boot. U-Boot's own DRAM copy at
  `0x40200000` is overwritten by the load, which is expected.
- Under `openocd -c ...`, `reg` and `mdw` print NOTHING. Use
  `echo [get_reg {pc}]` / `echo [read_memory <addr> 32 <n>]` — but on OpenOCD
  0.12 the tcl `get_reg` can return stale all-zero values; `reg <name>` one
  per TCL-port RPC (port 6666, `printf '%s\032' "$cmd" | nc ...`) is the
  reliable form.
- A static `pc` inside `rt_starfive_uart_read` (`lwu 0x14(base); andi a0,1;
  beqz`) is the shell's non-blocking RX poll, NOT a hang — the shell answers
  a command sent afterwards.
- The vendor-flow note "hart 1 rejects halt" did not reproduce: hart 1 halted
  fine at the U-Boot prompt (`dcsr` prv=S, `satp` 0). Stage through hart 2
  regardless, as the scripts do.
