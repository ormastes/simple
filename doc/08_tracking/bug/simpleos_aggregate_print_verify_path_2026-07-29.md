# Verify path: does the runtime_native.c aggregate-print/join fix reach SimpleOS guests?

Status: INVESTIGATION (read-only), 2026-07-29.

## Headline finding

**NO. The `src/runtime/runtime_native.c` fix does not reach SimpleOS guest
programs at all.** SimpleOS links a completely separate, independent
reimplementation of `rt_to_string` (`src/os/libc/simpleos_simple_runtime.c`)
that shares no code with `runtime_native.c` and currently has **no aggregate
handling whatsoever** — every tuple/dict/enum/object falls through to the
literal placeholder string `"<value>"`. Fixing `runtime_native.c` only fixes
host-native builds (Linux/macOS/FreeBSD); it is a no-op for SimpleOS.

## Q1 — Build + boot recipe for a SimpleOS user program

Two families exist:

- **Kernel-only smoke (NOT board-runnable per `.claude/rules/board-runnable.md`):**
  `scripts/os/run_simpleos_qemu.shs` (`-kernel "$SIMPLEOS_KERNEL_ELF"`) and
  `scripts/os/run_simpleos_q35_smoke.shs` (`-kernel` + `-device
  isa-debug-exit,iobase=0xf4`). Both use QEMU `-kernel`/`isa-debug-exit`
  pass-through semantics the board-runnable rule explicitly forbids as a
  final-evidence channel.
- **Real-firmware proxy (compliant):** `scripts/os/scp_retrieve_over_ssh_uefi.shs`
  boots OVMF pflash (`OVMF_CODE_4M.fd`/`OVMF_VARS_4M.fd`) → GRUB-EFI
  (`grub-mkstandalone` memdisk over vvfat) → multiboot1 kernel → ring-3 loader
  → sshd accept loop; the guest then runs `clang -cc1 -emit-obj` in ring-3 and
  writes `/hello.o` to an NVMe/FAT32 volume, retrieved over SCP for a byte-exact
  check. This is the harness referenced as the "OVMF reference harness" in
  `doc/03_plan/os/simpleos/hw_qemu/clang_board_bringup_x86_64_uefi.md`. Ladder
  markers L1 ("[grub-uefi] multiboot loading") → ring-3 accept loop are the
  observation channel; a `/BOOTLOG.TXT` marker file on the FAT32 volume is the
  firmware-independent fallback channel documented in that plan's P0.2.

No generic "compile+run one small SimpleOS user program and observe stdout"
script exists today; the existing real-firmware harness is built around the
in-guest clang goal. The smallest aggregate-print exerciser (Q3) would need to
be staged the same way `clang_static`/`hello.c` are staged in
`scp_retrieve_over_ssh_uefi.shs`.

## Q2 — Does SimpleOS link pull in `src/runtime/runtime_native.c`? **NO.**

- `doc/04_architecture/os/simpleos/kernel/simpleos_multiarch_hal.md` (§3.3,
  lines 347-353) states explicitly: `runtime.c`, `runtime_thread.c`,
  **`runtime_native.c`**, `async_driver.c`, `runtime_memtrack.c`, and the 6
  `platform/async_*.c` files "do NOT ship in the kernel image and are on the
  hosted-runtime path" — P1, out of scope for the AC-4 boot-smoke gate.
- SimpleOS ships its own from-scratch `rt_to_string`/`rt_print_value` etc. in
  `src/os/libc/simpleos_simple_runtime.c` (231 lines total). It has no
  `#include` of, and no call into, `runtime_native.c`. Its `rt_to_string`
  (lines 138-165) handles only: already-a-string, tagged int, true/false/nil —
  everything else (tuple/dict/enum/object/aggregate) returns the literal
  `"<value>"` (line 164). There is no aggregate-print logic to even be
  buggy — it was never implemented for SimpleOS.
- Build evidence this is what actually gets linked: `src/os/port/llvm/sysroot.shs`
  lines 124-131 compile `simpleos_simple_runtime.c` →
  `simpleos_simple_runtime.o`, then `ar rcs` it directly into
  `$SYSROOT/lib/libsimple_runtime.a` — the same archive name
  `scripts/os/simpleos-native-build.shs`'s `TARGET_RUNTIME` and
  `default_crt_search_dirs`/`default_libraries` (os == "simpleos") in
  `src/compiler/70.backend/linker/platform_defaults.spl` resolve against for
  every SimpleOS link. `runtime_native.c` is never compiled into this archive.
  (Historical bug note in
  `doc/08_tracking/bug/self_hosted_simpleos_target_native_build_crash_2026-07-11.md`
  independently confirms `libsimple_runtime.a` is the Simple-core/libc runtime
  archive linked for SimpleOS targets, not the hosted C runtime.)

**Consequence:** to make aggregate print (and join) actually work for
SimpleOS guests, the fix must be ported/added to
`src/os/libc/simpleos_simple_runtime.c`'s `rt_to_string`/`rt_write_value`
(currently a stub for this case), not just `runtime_native.c`.

## Q3 — Smallest exercising guest program + observation channel

A minimal `.spl` program compiled for `x86_64-unknown-simpleos` doing e.g.
`print((1, 2))` / `print({"a": 1})` / an enum-with-payload print, staged onto
the FAT32/NVMe volume the same way `hello.c`/`clang_static` are staged in
`scripts/os/scp_retrieve_over_ssh_uefi.shs`, and invoked from the ring-3 loader
in place of (or alongside) the clang step. Observation channels, in the order
the existing plan prefers them: (a) the already-wired 16550 serial console
(COM1 `0x3f8`) ladder-marker output; (b) appended text in `/BOOTLOG.TXT` on
the FAT32 volume, retrieved by moving the disk back to the host — this is
firmware-independent and needs no new capability.

## Q4 — Board-run status: **BLOCKED, gap named explicitly**

- x86_64 UEFI mini-PC: `doc/03_plan/os/simpleos/hw_qemu/clang_board_bringup_x86_64_uefi.md`
  is `Status: PLANNED 2026-07-13` — only the OVMF real-firmware proxy is
  proven (boot chain, ring-3, clang compile, byte-exact object). Physical
  board phases P0 (board/evidence-channel selection) through P2 (real NVMe
  compile-to-disk) are unchecked TODOs; no physical mini-PC has been
  purchased/booted yet per this doc. Named gap: no physical NIC driver exists
  either (Intel I210/I225 / Realtek 8111/8125 — QEMU lanes are virtio-net
  only), separate from the print/join concern.
- Other boards: `doc/03_plan/os/simpleos/hw_qemu/simpleos_real_board_hardening_driver_plan.md`
  labels the Cortex-M33 lane `c-shim-board-bringup` (build-only, QEMU
  MPS2-AN505 only) and states RA4M1/STM32U585 physical-board scripts "pass
  build-only mode" — "Physical flashing" is the explicit named gap, not yet
  done.

So today, for this fix, the ceiling is the OVMF/QEMU real-firmware proxy tier
(compliant per board-runnable.md's fallback allowance), not an actual physical
dev board — that must be stated explicitly per the rule, not implied.

## Answers (one line each)

1. Real-firmware build/boot recipe: `scripts/os/scp_retrieve_over_ssh_uefi.shs`
   (OVMF pflash → GRUB-EFI → multiboot → ring-3); the `-kernel`/`isa-debug-exit`
   scripts (`run_simpleos_qemu.shs`, `run_simpleos_q35_smoke.shs`) are
   QEMU-only shortcuts, non-compliant as final evidence.
2. **No** — SimpleOS links `src/os/libc/simpleos_simple_runtime.c`'s
   independent `rt_to_string` (compiled into `libsimple_runtime.a` by
   `src/os/port/llvm/sysroot.shs`), not `src/runtime/runtime_native.c`
   (explicitly excluded from the kernel/guest image per
   `simpleos_multiarch_hal.md` §3.3); SimpleOS's own copy has no aggregate
   printing implemented at all (returns `"<value>"`).
3. Smallest exerciser: a tiny `.spl` `print(tuple/dict/enum)` binary staged
   the same way `hello.c` is in the OVMF harness; observe via serial console
   or a `/BOOTLOG.TXT` marker on the FAT32 volume.
4. Board-run: **blocked**, named gap = physical mini-PC/board bring-up phases
   not yet executed (x86_64 plan still `PLANNED`; other boards explicitly
   labeled `c-shim-board-bringup`/build-only) — only the OVMF/QEMU
   real-firmware proxy tier is currently alive.
