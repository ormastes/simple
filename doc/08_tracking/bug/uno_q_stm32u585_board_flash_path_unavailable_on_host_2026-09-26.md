# SimpleOS Cortex-M cannot be flashed to the connected Arduino UNO Q from this host

- **Filed:** 2026-09-26
- **Status:** OPEN — board-run blocked. Scope is explicitly NOT "QEMU-only is fine";
  this record exists because `.claude/rules/board-runnable.md` requires a blocked
  board path to be named and filed rather than silently shipped as QEMU-only.
- **Area:** `scripts/os/run_simpleos_stm32u585.shs` flash lane / host tooling
- **Host:** yoon-note, x86_64 Linux
- **Board:** Arduino UNO Q, USB `2341:0078`, `iProduct "UNO Q - uno-q"`,
  `iSerial 3655308719`, enumerated at `/dev/ttyACM0` (user is in `dialout`)

## What IS established

The kernel ELF at `build/os/simpleos_stm32u585.elf` (built 2026-09-19, 135092
bytes) is a correct Cortex-M33 image and carries the whole Cortex-M bring-up fix
set:

```
Type: EXEC   Machine: ARM   Entry point: 0x8000741
Flags: 0x5000200, Version5 EABI, soft-float ABI
Tag_CPU_name: "cortex-m33"
Tag_CPU_arch: v8-M.mainline
Tag_CPU_arch_profile: Microcontroller
Tag_THUMB_ISA_use: Yes
```

- Entry `0x8000741` is odd (Thumb bit set) and in the STM32 flash aperture
  (`0x08000000`).
- `Tag_CPU_arch: v8-M.mainline` + profile `Microcontroller` is direct artifact
  evidence that the M-profile triple is preserved rather than collapsed to
  `armv7` (which would report `v7` / profile `Application`).
- `readelf -s` finds `cm33_policy_fs_add_file`, so the pure-Simple policy objects
  were linked in, and
  `__module_init_src_os_kernel_arch_cortex_m33_scalar_parser_fs_policy_spl_dynamic`,
  so the module initializer the C shim calls is present.

So the image side is done. What is missing is a way to get it onto the MCU.

## Why the flash lane cannot run here

`run_simpleos_stm32u585.shs` defaults to `FLASHER=st-flash` and also supports
`openocd` / `stm32prog`. On this host:

| tool | present |
|---|---|
| `st-flash` | no |
| `dfu-util` | no |
| `STM32_Programmer_CLI` / `stm32prog` | no |
| `openocd` | **yes** |
| `adb` | no |
| `arduino-cli` | no |

`openocd` alone is not sufficient, because the UNO Q exposes **no SWD/debug
interface over USB**. Its USB descriptors are a vendor-specific interface
(class 255, protocol 1 — the ADB-shaped function) plus a CDC pair:

```
bInterfaceClass 255 Vendor Specific Class   bInterfaceProtocol 1
bInterfaceClass   2 Communications          bInterfaceProtocol 1 AT-commands (v.25ter)
bInterfaceClass  10 CDC Data
```

On the UNO Q the STM32U585 sits behind the Qualcomm (QRB2210) SoC, which runs
Linux and owns MCU programming; the host does not see the STM32's SWD. So the
supported route is *through* the board's Linux side, which needs either `adb`
(absent) or a working console.

`/dev/ttyACM0` gave **zero bytes** in both directions: an 8-second read produced
nothing, and writing `\r\n\r\n` then reading for 8 more seconds produced nothing
(port set `115200 raw -echo`). No login prompt, no boot log.

## Unblock condition

Any ONE of:

- install `adb` (or `arduino-cli` with the UNO Q core) on this host and flash the
  STM32 from the board's Linux side, which is Arduino's supported UNO Q flow;
- attach an external SWD probe (ST-Link/CMSIS-DAP) to the board's debug pads and
  use the already-present `openocd` lane;
- install `st-flash` (`stlink-tools`) **and** confirm a DFU/SWD route actually
  reaches the MCU — note installing it alone does not create a path if no debug
  interface is exposed;
- identify what `/dev/ttyACM0` is actually bound to on a booted UNO Q and
  document the console handshake, if a console route exists.

Then run `sh scripts/os/run_simpleos_stm32u585.shs --no-build` (the ELF above is
already correct) with `SIMPLEOS_SERIAL_LOG` set, and record board identity +
flash transcript + serial transcript per the board evidence bar.

## Related

- Cortex-M image/link/init fixes that produced the verified ELF: see the
  `llvm_arm32_baremetal_arch` change, `scripts/os/build-cortex-m-policy-objects.shs`,
  and `doc/08_tracking/bug/simple_module_const_scalars_need_runtime_init_on_baremetal_2026-09-19.md`.
- Rebuilding the ELF from source on this host is *separately* blocked right now by
  `doc/08_tracking/bug/native_build_worker_sigill_ud2_at_codegen_entry_2026-09-26.md`
  (every `native-build` exits 132). The 2026-09-19 ELF predates that and is why
  artifact evidence was available at all.
