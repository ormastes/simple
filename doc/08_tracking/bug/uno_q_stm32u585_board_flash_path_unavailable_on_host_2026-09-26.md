# SimpleOS Cortex-M cannot be flashed to the connected Arduino UNO Q from this host

- **Filed:** 2026-09-26
- **Status:** OPEN — board-run still blocked, but narrowed on 2026-09-26 from "no
  tool can reach the board" to "one root udev rule" (see the 2026-09-26 update
  below: `adb` is now installed root-free and enumerates the board by serial).
  Scope is explicitly NOT "QEMU-only is fine";
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
| `adb` | **yes as of 2026-09-26** — see below |
| `arduino-cli` | no (no apt candidate on this host) |

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

Re-probed 2026-09-26 as an **AT-command modem port**, since the descriptor says
`bInterfaceProtocol 1 AT-commands (v.25ter)`: `AT\r` then `ATI\r` at 115200 raw
-echo -crtscts, reading for 6s, returned **0 bytes** as well. `/dev/ttyACM0`
binds interface `3-9:1.1` of the Arduino device, so it is the right device and
simply answers nothing. The console route remains dead.

## 2026-09-26 update: `adb` installed without root; blocker narrowed to ONE root action

`adb` is no longer missing. It was deployed **without root** using the same
`.deb`-into-a-private-prefix technique as
`doc/07_guide/infra/toolchain/llvm_23_deploy_2026-08-21.md` (that guide names
`/mnt/data`, which **does not exist on this host** — the prefix used is
`$HOME/.local/opt/adb-root`):

```
apt-get download adb android-libbase android-libboringssl android-libcutils \
                 android-liblog android-libziparchive libprotobuf32t64
dpkg-deb -x <each>.deb $HOME/.local/opt/adb-root
```

The Debian `adb` links against `libbase/libcrypto/libcutils/liblog/libssl/libziparchive`
`.so.0` which land in `usr/lib/x86_64-linux-gnu/android/` and are NOT on the
default loader path, so `$HOME/.local/opt/adb-root/bin/adb` is a two-line
`LD_LIBRARY_PATH` wrapper, symlinked to `$HOME/.local/bin/adb` (already on PATH).
`adb version` -> `Android Debug Bridge version 1.0.41 / 34.0.4-debian`.

**`adb` positively identifies the board** — this is the first host-side tool that
talks to the UNO Q's vendor-specific (class 255, protocol 1) interface at all:

```
$ adb devices -l
3655308719   no permissions (missing udev rules? user is in the plugdev group)   usb:3-9 transport_id:1
```

Serial `3655308719` matches the USB descriptor exactly, so the ADB-shaped
interface really is ADB and the transport is one permission away from working.

**The remaining blocker is a udev rule, which requires root exactly once:**

```
$ ls -l /dev/bus/usb/003/004
crw-rw-r-- 1 root root 189, 259 ...        # 0664 root:root
$ getfacl /dev/bus/usb/003/004             # user::rw- group::rw- other::r--  (no uaccess ACL)
```

The node is world-**readable** but not writable, and `adb`'s USB transport needs
`O_RDWR` on usbfs. Confirmed non-root workarounds do not exist here:

- `sudo -n true` -> `sudo: a password is required` (user IS in `sudo`/`plugdev`,
  but there is no passwordless sudo, per CLAUDE.md);
- no `uaccess` ACL is applied to the node, and no `/etc/udev/rules.d/` rule
  mentions `2341` (only snap rules are installed);
- no USB network interface appears (`ip -o link` shows only `lo` + `wlp3s0`), so
  `adb connect` over TCP is not available as a permission-free side door.

### The one root command that unblocks this

```sh
printf 'SUBSYSTEM=="usb", ATTR{idVendor}=="2341", ATTR{idProduct}=="0078", MODE="0664", GROUP="plugdev"\n' \
  | sudo tee /etc/udev/rules.d/51-arduino-uno-q.rules
sudo udevadm control --reload-rules && sudo udevadm trigger
adb kill-server && adb devices          # must show `3655308719  device`, not `no permissions`
```

(`pkexec` exists and would prompt on the desktop session instead of the terminal;
it was not invoked, since popping a password dialog is the user's call.)

### Still unverified beyond that point

Nothing about the board's *own* flash path could be checked, because it needs a
working `adb shell` to look at: which on-board tool/service the QRB2210 Linux
side uses to program the STM32U585, and whether the ELF must be converted to
`.bin`/`.hex` first. That is the next step once `adb devices` reports `device`,
and it is **not** established.

### The three `run_simpleos_stm32u585.shs` lanes are all probe-only

Re-read at `:96-110`: `st-flash write ... 0x08000000`, `openocd -f
interface/stlink.cfg -f target/stm32u5x.cfg`, and `STM32_Programmer_CLI -c
port=SWD`. Every one assumes a host-visible SWD/ST-Link probe. **None of them has
a route that works through the board's own USB connection**, so no combination of
them flashes this board without either an external probe or the adb path above.
Nothing was flashed and nothing was written to the board.

## Unblock condition

Any ONE of:

- **(closest — `adb` half is DONE)** apply the udev rule above so `adb devices`
  reports `device`, then flash the STM32 from the board's Linux side, which is
  Arduino's supported UNO Q flow;
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
