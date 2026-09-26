# SimpleOS runs on the real UNO Q board but spins forever in a UART status poll

- **Filed:** 2026-09-26
- **Status:** OPEN — the image is FLASHED and EXECUTING on real hardware; it never
  reaches a console. This is a board-vs-QEMU divergence, exactly the class
  `.claude/rules/board-runnable.md` exists to prevent shipping as "board-runnable".
- **Area:** `src/os/kernel/arch/cortex_m33/cm33_shim.c` UART bring-up / STM32U585
  peripheral setup
- **Board:** Arduino UNO Q, USB `2341:0078`, `iSerial 3655308719`;
  Qualcomm side `Linux uno-q 6.16.7-g0dd6551ae96b aarch64`, shell user `arduino`

## Board evidence (the bar in .claude/rules/board-runnable.md)

**Identity:** `adb devices -l` -> `3655308719   device   usb:3-9   transport_id:1`;
`uname -a` -> `Linux uno-q 6.16.7-g0dd6551ae96b #1 SMP PREEMPT ... aarch64`.

**Flash path — found, and it is the vendor's own.** The Qualcomm SoC has a local
**bit-banged GPIO SWD** link to the STM32U585, which is why no host-side route
ever existed (the host sees no SWD; see
`uno_q_stm32u585_board_flash_path_unavailable_on_host_2026-09-26.md`):

```
/opt/openocd/bin/openocd            # 0.12.0+dev, runs UNPRIVILEGED
/opt/openocd/openocd_gpiod.cfg      # adapter driver linuxgpiod
                                    # swclk 26 / swdio 25 / srst 38, -chip 1
                                    # transport select swd; source stm32u5x.cfg
```
`/dev/gpiochip*` are `root:gpiod` and user `arduino` is in group `gpiod`, so no
sudo is needed on the board. Host-side access required exactly one root action, a
udev rule for `2341:0078` (`MODE="0664" GROUP="plugdev"`), after which `adb` went
from `no permissions` to `device`.

**Flash transcript:**
```
adb push build/os/simpleos_stm32u585.elf /tmp/simpleos_stm32u585.elf     # rc=0, 135456 bytes
adb shell "/opt/openocd/bin/openocd -d1 -s /opt/openocd -f openocd_gpiod.cfg \
  -c 'init; reset; halt; flash write_image erase /tmp/simpleos_stm32u585.elf; reset; shutdown'"
# rc=0; only diagnostic: Warn : Adding extra erase range, 0x08005210 .. 0x08005fff
#                        (benign sector-boundary rounding)
```
No explicit address is given: openocd takes the load address from the ELF's own
program headers, which is the vendor's own full-firmware-replace shape
(`unoq.bootloader.tool=remoteocd` / `arduino-cli burn-bootloader` do the same).

**Two rollbacks were secured BEFORE writing**, and both still exist:
1. the untouched vendor core,
   `/home/arduino/.arduino15/packages/arduino/hardware/zephyr/0.54.1/firmwares/zephyr-arduino_uno_q_stm32u585xx.elf`
   (1,999,112 bytes, md5 `dfc0530d31f1f367e1c10ffd64e51cac`), restorable with the
   same openocd invocation or `arduino-cli burn-bootloader -b arduino:zephyr:unoq -P jlink`;
2. a raw 512 KiB dump of the pre-existing flash,
   `dump_image /tmp/mcu_backup_0x08000000_512k.bin 0x08000000 0x80000`, pulled to
   the host and confirmed non-blank (not all-`00`, not all-`ff`).

## What IS proven: the MCU runs our image

```
init; reset halt; reg pc
  [stm32u5.cpu] halted due to breakpoint, current mode: Thread
  xPSR: 0xf9000000   pc: 0x08000740   msp: 0x200c0000
```
`0x08000740` is exactly this ELF's entry (`0x08000741` minus the Thumb bit), and
`msp` is a valid STM32U585 SRAM top. So the reset vector is ours.

Sampling the PC while running, twice, ~4 s apart:
```
  xPSR: 0x29000000   pc: 0x08001288   msp: 0x200bff98
  xPSR: 0x29000000   pc: 0x08001288   msp: 0x200bff98
```
It advanced from the reset vector into `_c_main` (`0x08000751`; next real symbol is
`cfsr_decode` at `0x08003629`, and `addr2line` places `0x08001288` in
`cm33_shim.c`), so our code really executes. `xPSR` ISR_NUMBER is **0** — Thread
mode, **not** inside an exception/fault handler, so this is not a HardFault spin.

## What is WRONG: it is parked in a UART status poll

PC and MSP are byte-identical across the 4 s gap, i.e. one instruction, no stack
movement. Decoding the image at that address (offset `0x1288` of the
`objcopy -O binary` image):

```
f8d9 0000    LDR.W r0, [r9, #0]     ; load a peripheral status register
0680         LSLS  r0, r0, #26      ; shift bit 5 into the N flag
d5fb         BPL   -5               ; branch back while bit 5 == 0
```

A three-instruction poll: load a status word, test **bit 5**, loop while clear.
That is a UART flag wait, and it never completes — which explains BOTH symptoms at
once: no console output, and a frozen PC.

Consistent with that, every console route is silent:
- host `/dev/ttyACM0`: 0 bytes (and note this node was provided by the *Zephyr*
  firmware's USB-CDC stack, which this flash replaced, so it is not expected to
  carry SimpleOS output);
- board-side `/dev/ttyMSM0`, `/dev/ttyS0`, `/dev/ttyS1`: 0 bytes each.

## Why this is a board-vs-QEMU divergence

`cm33_shim.c` was brought up against **QEMU MPS2-AN505**, whose UART is a
different peripheral at a different address with different flag bit positions
from the STM32U585's USART/LPUART. A poll that returns immediately on MPS2-AN505
can spin forever on real silicon if the peripheral is unclocked, not pin-muxed, or
if the tested bit is the wrong one for this part. On the UNO Q the devicetree maps
`usart1`/`lpuart1` as the MCU console, and those pins do not reach the external
host over USB.

## Unblock condition

SimpleOS boot output (e.g. `[TICK] SysTick enabled (~100 Hz)`) is captured from a
real console on this board.

Next steps, cheapest first:
1. Identify the polled peripheral: halt and read `r9` plus the status word
   (`reg r9`, `mdw <r9>`) — that names the exact register being waited on. Note
   `mdw` produced no output in this session's openocd invocations while `reg` did;
   sort that out first or read the value via a `reg`-based path.
2. Compare that address against the STM32U585 USART1/LPUART1 base and check the
   flag bit: for STM32 USART `ISR`, TXE/TXFNF and RXNE/RXFNE are **not** at bit 5
   in every family/part, and the MPS2-AN505 UART `STATE` register bit assignments
   are unrelated. A wrong bit index alone would produce exactly this spin.
3. Confirm the USART is clocked and pin-muxed on this board before the poll runs
   (RCC enable + GPIO AF), since an unclocked USART reads a status word that never
   changes.
4. Pick a console that physically reaches somewhere observable on the UNO Q, or
   add an SWD-visible liveness counter (e.g. bump `tick_count` at `0x20000018`)
   so progress can be proven without a UART at all.

Do NOT "fix" this by reverting to QEMU-only validation: the image is genuinely on
hardware and genuinely executing, and that is the part that was previously
unproven.

## Related

- `uno_q_stm32u585_board_flash_path_unavailable_on_host_2026-09-26.md` — the
  host-side flash-path gap this supersedes (the on-board GPIO-SWD route is the answer).
- `simpleos_cm33_policy_symbols_mangled_2026-09-26.md` — the symbol-naming fix
  that made this linkable image exist.
- `simple_module_const_scalars_need_runtime_init_on_baremetal_2026-09-19.md` — the
  `.bss`/module-init hazard on this same shim.
