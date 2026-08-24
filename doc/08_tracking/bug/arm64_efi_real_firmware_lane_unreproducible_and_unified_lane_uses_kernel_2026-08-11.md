# aarch64 real-firmware EFI lane was unreproducible; unified arm64 lane still uses QEMU `-kernel`

- **Date:** 2026-08-11
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  The `-kernel` dependency of the main arm64 desktop lane REMAINS OPEN.
- **Rule:** `.claude/rules/board-runnable.md`

## The filed claim was stale

`.claude/rules/board-runnable.md` said *"aarch64 currently lacks an EFI-stub —
that gap is filed"*. Measured on 2026-08-11, that is **not** what was missing.
The aarch64 real-firmware boot path already existed and already worked:

```
$ sh scripts/check/check-simpleos-aarch64-limine-framebuffer.shs
PASS — real-firmware (EDK2/AAVMF pflash + Limine BOOTAA64.EFI) aarch64 boot
obtained a framebuffer: addr=0x18446462600284340224 800x600 bpp=32 pitch=3200;
3 refusal paths checked and none fired
```

Host firmware is present (`/usr/share/AAVMF/AAVMF_CODE.fd`,
`/usr/share/AAVMF/AAVMF_VARS.fd`, `/usr/share/qemu-efi-aarch64/QEMU_EFI.fd`), and
`vendor/limine/BOOTAA64.EFI` is git-tracked. Rule text corrected in this change.

## What was actually broken (1): the boot artifact had no builder

`build/os/aarch64_limine/esp.img` was a **one-off hand-made artifact**. Per
`doc/08_tracking/bug/aarch64_real_firmware_boot_gap_and_seed_defects_2026-07-14.md`
it was populated "via the `pyfatfs` venv at `/tmp/pyfatvenv`" — a throwaway
virtualenv outside the repo, which no longer exists. Confirmed:

- `git ls-files build/os/aarch64_limine/` -> **empty** (`build/` is gitignored).
- `grep -rn aarch64_limine` across `*.shs *.spl *.sh` -> the only non-doc hit is
  the gate that *consumes* the image. **No producer existed anywhere.**
- No `mtools`, no system `pyfatfs`, and `/tmp/pyfatvenv` gone.

So a clean clone could not produce a bootable aarch64 EFI artifact at all. The
lane passed only because a binary happened to survive in a gitignored directory.

**Fixed** by `scripts/os/build-simpleos-aarch64-efi-esp.shs`, which builds the
ESP from tracked inputs (`vendor/limine/BOOTAA64.EFI` + the kernel ELF), with a
`mkfs.vfat` FAT32 filesystem, a repo-local pyfatfs build venv created on demand,
and a **read-back verification pass** so a silently-truncated FAT write cannot
report success.

### Design choice: EFI *application* chain, not a PE/COFF kernel stub

Deliberate, and the smaller diff. The repo already vendors a prebuilt
`BOOTAA64.EFI` and the kernel already speaks the Limine boot protocol
(`src/os/kernel/boot/limine_boot_aarch64.spl`), so zero compiler or linker work
is needed — this mirrors x86_64, which also chains through an EFI application on
a FAT ESP rather than stubbing the kernel. A PE/COFF stub would require PE
emission from the Simple backend, which does not exist. Rationale is recorded in
the build script header, not only here.

## What was actually broken (2): the main arm64 lane still uses `-kernel` — STILL OPEN

`scripts/check/check-simpleos-arm64-unified-live.shs:233` boots with:

```
    -kernel "$kernel" -device ramfb \
```

QEMU `-kernel` pass semantics do not exist on hardware. Under
`.claude/rules/board-runnable.md` this makes the **main arm64 desktop/WM lane
QEMU-only**, regardless of the EFI lane now being green. This is **not** fixed
here and is not narrowed away: the new gate proves the real-firmware chain
independently so that lane can be *migrated onto it* rather than blessed.

**Remaining work for full x86_64 parity:**
1. Migrate `check-simpleos-arm64-unified-live.shs` off `-kernel` onto the
   AAVMF + `BOOTAA64.EFI` + ESP chain proven here.
2. Give the unified arm64 kernel a from-source build in the ESP builder.
   `KERNEL_ELF` is currently an *input*; the kernel's own seed `native-build`
   lane (`--backend cranelift --target aarch64-unknown-none-elf --linker-script
   .../linker_limine.ld`) is not invoked by the builder, which fails loudly
   rather than inventing a kernel. So the ESP is reproducible; the kernel inside
   it is not yet.

   **CLOSED for the Limine kernel, 2026-08-24** by
   `scripts/os/build-simpleos-aarch64-limine-kernel.shs`, which runs exactly
   that seed `native-build` command and structurally verifies the result
   (non-empty, AArch64 ELF, has `.text`, read back with `readelf`). It fails
   loudly rather than inventing a kernel, same contract as the ESP builder.

   Verified end to end from a WIPED `build/os/aarch64_limine/` — the state a
   clean clone is in:

   ```
   $ rm -rf build/os/aarch64_limine
   $ sh scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs
   ERROR — nothing was checked: ESP build failed ... missing kernel ELF
   .../build/os/aarch64_limine/kernel.elf      (exit 2)

   $ sh scripts/os/build-simpleos-aarch64-limine-kernel.shs
   PASS — aarch64 Limine kernel built: .../kernel.elf (105768 bytes, AArch64 ELF with .text)
   $ sh scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs
   PASS — 4 boot-stage marker(s) checked, EDK2/AAVMF pflash real-firmware aarch64
   boot verified via BOOTAA64.EFI on a FAT ESP (no -kernel, no isa-debug-exit),
   76 serial line(s) captured; firmware /usr/share/AAVMF/AAVMF_CODE.fd
   ```

   Note on the compiler: this uses the Rust bootstrap seed deliberately. The
   aarch64 UNIFIED desktop kernel refuses the seed, but this Limine kernel is a
   different, much smaller artifact and links cleanly with it.

   Note on a near-miss worth recording, since it is the exact hazard
   `.claude/rules/vcs.md` warns about: the first attempt at this build failed
   with `ld.lld: error: undefined symbol: rt_raw_i64_to_string`, and a fix was
   written for `freestanding_runtime.c` — but that error came from a **stale
   working copy**. The tracked file already carried `rt_raw_i64_to_string`
   (landed by another session, found the same way, by a real ld.lld error). The
   working copy was 1562 lines behind. The file was restored to tracked content
   and the whole chain re-verified on it; the kernel is byte-identical in size
   either way. Nothing in this change touches the C runtime.

   The UNIFIED arm64 kernel still has no from-source build here; that half of
   item 2 stays open, as does item 1.
3. Physical board bring-up for aarch64 remains filed as before.

## Evidence — red then green

**RED.** `esp.img` deleted; before this change nothing in the repo could
regenerate it (`grep` for a producer returns nothing).

**GREEN.** Rebuilt from tracked inputs by the new builder:

```
[esp] firmware  CODE=/usr/share/AAVMF/AAVMF_CODE.fd
[esp] bootloader vendor/limine/BOOTAA64.EFI
[esp] kernel     build/os/aarch64_limine/kernel.elf (105736 bytes)
[esp]   /EFI/BOOT/BOOTAA64.EFI  274432 bytes
[esp]   /boot/kernel.elf  105736 bytes
[esp]   /limine.conf  127 bytes
[esp]   /startup.nsh  28 bytes
[esp] sha256 b25466a830c411b0266110b1b873d069dc3d059163ffab374b558fa7102269c0
```

Booted under EDK2/AAVMF pflash (no `-kernel`, no `isa-debug-exit`), 76 serial
lines, verbatim excerpts:

```
[BOOT] HHDM offset: 0x18446462598732840960
[BOOT] Memory map: 46 entries
[BOOT]   region 0: base=0x67108864 size=0x67108864 type=1
[BOOT] Framebuffer: addr=0x18446462600284340224 800x600 bpp=32 pitch=3200
[BOOT] Handing off to memory layer...
[BOOT] memory_init: wiring Layer 1 physical memory manager (aarch64, Limine lane)
[BOOT] SIMPLEOS-AARCH64-LIMINE-KERNEL-OK
```

Gate verdict:

```
PASS — 4 boot-stage marker(s) checked, EDK2/AAVMF pflash real-firmware aarch64
boot verified via BOOTAA64.EFI on a FAT ESP (no -kernel, no isa-debug-exit),
76 serial line(s) captured
```

## Gate is not tautological

`scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs` was sabotage-verified:

| variant | verdict | exit |
|---|---|---|
| real ESP, AAVMF pflash | `PASS — 4 boot-stage marker(s) checked ...` | 0 |
| ESP whose `/boot/kernel.elf` is 105,736 random bytes | `FAIL — ... never printed ...` | 1 |
| artifact dir empty (`SKIP_ESP_BUILD=1`, no `esp.img`) | `ERROR — nothing was checked: missing .../esp.img` | 2 |

It requires **four** positive boot-stage markers, so a partial boot (firmware up,
kernel wedged early) cannot pass; an empty serial log is ERROR, never PASS; and
it asserts the absence of `-kernel` / `isa-debug-exit` against the **assembled
argv it is about to execute**, not against its own prose.

## Files

- `scripts/os/build-simpleos-aarch64-efi-esp.shs` (new) — reproducible ESP builder.
- `scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs` (new) — the gate.
- `.claude/rules/board-runnable.md` — stale claim corrected, real gap restated.

## 2026-08-11 follow-up: item (1) of "remaining work" is a kernel-arch gap, not a script migration — STILL OPEN, re-scoped

Attempted the literal migration ("point `check-simpleos-arm64-unified-live.shs`
at the AAVMF + `BOOTAA64.EFI` + ESP chain"). It cannot be done as a script-only
change: the unified arm64 kernel and the aarch64 Limine kernel are **two
different kernels with incompatible boot contracts**, not two build outputs of
the same code.

**The unified kernel has no Limine protocol support.**
`examples/09_embedded/simple_os/arch/arm64/boot/crt0.S` is the entire boot
contract: it checks `CurrentEL`, drops EL2->EL1 if needed, sets up the stack
from a linker symbol, zeroes `.bss`, and jumps into C — it never reads a
bootloader-supplied argument, never parses a request/response table, and
`examples/09_embedded/simple_os/arch/arm64/linker.ld` says explicitly in its
header comment: *"Target: QEMU virt machine (aarch64), RAM starts at
0x40000000, kernel loaded by QEMU -kernel flag."* Contrast with
`src/os/kernel/boot/limine_boot_aarch64.spl`, which the **aarch64** (not
arm64) Limine kernel actually uses: ~20 named Limine request/response IDs
(`LIMINE_MEMMAP_ID_*`, `LIMINE_FRAMEBUFFER_ID_*`, `LIMINE_HHDM_ID_*`,
`LIMINE_KERNEL_ADDR_ID_*`, ...) with magic markers that the Limine bootloader
scans the kernel ELF for at load time. The unified kernel's ELF has none of
these markers. Limine's own protocol requires them to even recognize a binary
as a Limine-bootable kernel — without them Limine cannot chainload it, not "may
boot it wrong." Building an ESP that points `/boot/kernel.elf` at the unified
kernel and letting Limine try to load it is not expected to reach the unified
kernel's own boot markers at all; Limine's own request-scan is the layer that
fails first, so the SAME assertions the lane checks today (`desktop-ready`,
`wm-key-poll`, `wm-frame host-gpu-device-evidence`, `virtio_snd`, etc.) would
regress across the board, not selectively — this is a Limine-recognition
failure, not a partial-boot marker gap. (Not booted to first-hand serial
evidence in this session — see "what's still missing" below for why — but the
absence of the request markers is verified directly by reading the linked ELF
inputs, and the mechanism is inherent to how Limine's loader works: it will
not treat an ELF as Limine-bootable in the first place.)

**Second, independent blocker hit while trying to get a real kernel ELF for an
empirical boot attempt:** this repo's `bin/simple` / `bin/release/*/simple` is
currently the **Rust bootstrap seed**, not the pure-Simple self-hosted
compiler the unified lane itself requires (it checks
`case "$version" in *'Rust-built'*) fail compiler-is-bootstrap-seed`). Building
the self-hosted compiler from scratch was out of scope for this session
(multi-minute+ full bootstrap, and several other concurrent native-build
processes were already running on this shared machine). Building the unified
kernel with the seed directly (bypassing that guard, for evidence purposes
only) failed with **seed codegen defects**, not anything related to boot
protocol:

```
.../virtio_common.spl: codegen: Module error: codegen: 7 function body/bodies
failed to compile: [Virtqueue.init_free_list, Virtqueue.alloc_desc,
Virtqueue.free_desc, Virtqueue.push_avail, VirtioDevice.read_reg,
VirtioDevice.write_reg, VirtioDevice.init]
.../virtio_gpu.spl: codegen: Module error: codegen: 51 function body/bodies
failed to compile: [...]
```

This is the known seed-vs-self-host divergence class in
`.claude/memory/ref_*` (seed codegen is not trustworthy for aarch64 native
targets), unrelated to the EFI migration itself, but it means no fresh unified
kernel ELF could be produced in this session to attempt an empirical AAVMF
boot and capture real serial evidence either way.

**Re-scoped remaining work (supersedes item 1 above):**
1. Give the unified arm64 kernel Limine request/response support
   (`LIMINE_MEMMAP_ID_*`, `LIMINE_FRAMEBUFFER_ID_*`, `LIMINE_HHDM_ID_*`,
   `LIMINE_KERNEL_ADDR_ID_*` at minimum) in its own `crt0.S`/entry path, mirroring
   `src/os/kernel/boot/limine_boot_aarch64.spl`, OR give it a PE/COFF EFI-stub
   header so firmware can load it directly without going through a second-stage
   loader (rejected earlier in this doc for the aarch64 Limine kernel as "not
   worth inventing," but that call was made when the ESP-chain option existed
   and was cheap; here it does not exist without kernel changes either way, so
   the two options are back to being compared on their own merits).
2. Once the kernel speaks a real-firmware-loadable protocol, migrate
   `check-simpleos-arm64-unified-live.shs` off `-kernel` per the original
   item 1, reusing `scripts/os/build-simpleos-aarch64-efi-esp.shs` via its
   `KERNEL_ELF=`/`OUT_DIR=` overrides so the ESP builder is not forked.
3. Separately: get a pure-Simple self-hosted `bin/simple` deployed so the
   unified lane's own bootstrap-seed guard stops firing, and so a fresh kernel
   ELF can be built for evidence without hitting the seed's aarch64 codegen
   gaps.
4. Physical board bring-up for aarch64 remains filed as before.

**Status of this item: STILL OPEN**, and the "migrate the script" framing in
this doc's earlier "remaining work" section is retracted — the small-diff
script edit is blocked on the kernel-side boot-protocol gap in point 1 above.
No script was modified in this follow-up: forcing the migration onto a kernel
that cannot be Limine-chainloaded would either not boot (relegating the lane
to permanently red) or require silently weakening/deleting the very assertions
this lane exists to enforce, both of which this doc explicitly rules out.

## 2026-08-11 follow-up 2: the kernel-side gap is CLOSED — unified arm64 early boot now runs under real firmware

The re-scoped item 1 above ("give the unified arm64 kernel Limine
request/response support ... OR a PE/COFF EFI-stub header") is **implemented and
booted**, but by a **third option that neither of those two considered**, and
which is far smaller than both.

### Approach chosen: the arm64 Linux `Image` boot protocol

Neither of the two options previously on the table was necessary.
`vendor/limine/BOOTAA64.EFI` (Limine **10.8.5**, aarch64/UEFI — verified by
`strings`) implements the **`linux` boot protocol** as well as its own, complete
with device-tree handoff (`linux: device tree blob at %p`). The arm64 Linux
protocol's handover contract is **bit-for-bit what QEMU `-kernel` already
provides and what this kernel already assumes**:

| | QEMU `-kernel` (today) | Limine `protocol: linux` | Limine `protocol: limine` |
|---|---|---|---|
| exception level | EL1 or EL2 | EL1 or EL2 | EL1 |
| MMU / caches | **off** | **off** | **ON**, higher-half |
| address space | physical | physical | virtual + HHDM |
| boot arg | x0 = DTB | x0 = DTB | request/response markers |
| load address | link address | loader's choice | link address (mapped) |

So the Limine-protocol option (the one this doc previously assumed was the
path) is in fact the **expensive** one: it hands over with the MMU on in a
higher-half mapping, which would require rewriting the unified kernel's early
boot, every fixed physical MMIO address it uses (PL011 at `0x09000000`, the
virtio-mmio window, the ivshmem BAR), and `arm64_enter_user_virtual` in
`crt0.S`, which toggles `SCTLR_EL1.M` directly and would unmap itself the
instant it ran. The PE/COFF stub option remains rejected for the reason already
recorded — the Simple backend emits no PE.

The Linux-protocol option needs **no change to any of that**. The whole diff is
in the two files that define the boot contract.

### The early-boot adaptation that was actually needed

Only one property of the old contract is not guaranteed by the new one: the
**load address**. QEMU `-kernel` places the image at its link address
(`0x40000000`, the base of RAM on QEMU virt); a real bootloader places it
wherever it found free memory. Everything else — MMU off, physical addressing,
DTB in x0 (which this kernel ignores outright; `crt0.S` clobbers x0 on its first
instruction) — already matched.

`examples/09_embedded/simple_os/arch/arm64/boot/crt0.S` therefore gains exactly
two things:

1. **A 64-byte arm64 Linux `Image` header** at `_start` (`nop` / `b` over the
   header, `text_offset=0`, `image_size=_image_size`, `flags=0xa` = LE + 4 KiB
   pages + load-anywhere, `"ARM\x64"` magic at offset 56). It is inert under
   `-kernel`, which enters at the ELF entry point and simply executes the `nop`
   and the branch.
2. **A self-relocation stub.** It compares the PC-relative address of `_start`
   with the absolute (link-time) one. **Equal → it branches straight into the
   existing boot path, so the `-kernel` lane is byte-identically unaffected.**
   Unequal → it copies `[_start, _kernel_load_end)` down to the link address and
   jumps there.

   The one subtlety: the destination is the base of RAM, i.e. below any address a
   loader can pick, so the bulk copy is ascending and safe for the *data* — but
   the copy loop itself lives inside the source image and would be overwritten
   mid-flight whenever the ranges overlap. So the loop is first copied to a
   scratch page at `load_base + load_size + 4096`, which (since
   `load_base > link_base`) is strictly above `link_base + load_size` and thus
   outside both ranges, and is executed from there. `ic iallu` + `dsb`/`isb`
   follow the copy, since it is a code move with caches off.

`linker.ld` gains the two symbols the header and the stub need:
`_kernel_load_end` (end of the LOADED image, before the NOLOAD .bss/.stack/.heap)
and `_image_size = _kernel_end - _start` (the full in-memory footprint a loader
must reserve).

`scripts/os/build-simpleos-aarch64-efi-esp.shs` gains `BOOT_PROTOCOL=linux|limine`
(default `limine`, so the existing aarch64 lane is untouched). The ESP builder is
**not forked** — same script, same layout, same verification pass.

### Serial evidence — verbatim

Both boots use **one unmodified `crt0.S`**, and the probe payload's
`[probe] rodata-ok` line is printed through an **absolute** rodata pointer, so it
can only appear if the image genuinely ended up at its link address.

**Real firmware. EDK2/AAVMF pflash -> `BOOTAA64.EFI` -> `protocol: linux`. No
`-kernel`. No `isa-debug-exit`.**

```
UEFI firmware (version 2024.02-2ubuntu0.8 built at 10:08:54 on Dec 10 2025)
BdsDxe: starting Boot0001 "UEFI Non-Block Boot Device" from VenHw(837DCA9E-...)
linux: Loading kernel `boot():/boot/kernel.elf`...
[BOOT] ARM64 relocating to link address
[BOOT] ARM64 relocated
[BOOT] ARM64 crt0 entered
[BOOT] ARM64 sctlr ok
[BOOT] ARM64 stack ok
[BOOT] ARM64 bss ok
[BOOT] ARM64 vectors ok
[probe] c-start
[probe] bss-zeroed
[probe] data-ok
[probe] rodata-ok
[probe] SIMPLEOS-ARM64-REALFW-BOOT-OK
```

The relocation path **did** fire — the loader did not place the image at
`0x40000000` — so the stub is exercised, not merely present.

**Legacy `-kernel` ELF, same crt0.S — unchanged, and correctly does NOT relocate:**

```
[BOOT] ARM64 crt0 entered
[BOOT] ARM64 sctlr ok
[BOOT] ARM64 stack ok
[BOOT] ARM64 bss ok
[BOOT] ARM64 vectors ok
[probe] c-start
[probe] bss-zeroed
[probe] data-ok
[probe] rodata-ok
[probe] SIMPLEOS-ARM64-REALFW-BOOT-OK
```

### Scope of the evidence — stated honestly

The payload above is a **C probe linked against the real `crt0.S` and the real
`linker.ld`**, not the unified desktop/WM kernel itself. It proves the layer that
was blocking: the Image header, the MMU-off physical handover, and the
relocation (via .bss zeroing, .data, and an absolute rodata pointer). It does
**not** prove the unified kernel's own markers (`desktop-ready`, `wm-key-poll`,
`wm-frame host-gpu-device-evidence`, `virtio_snd`) fire under firmware, because
**no unified kernel ELF can be built in this session**: `bin/simple` is still the
Rust bootstrap seed (`WARNING: this Rust-built Simple binary is a bootstrap seed
only`), the unified lane refuses a seed by design, and the seed's aarch64 codegen
still fails on that kernel's virtio modules as recorded in follow-up 1. That is
blocker item 3 below, and it is not something this change can or should route
around.

### Gate

`scripts/check/check-simpleos-arm64-unified-boot-contract.shs` runs both boots
above on every invocation and is fail-closed: an empty serial log is `ERROR`, a
run that checks 0 markers is `ERROR`, a real-firmware boot that did **not**
relocate is `FAIL` (it would not have proven the stub), a legacy `-kernel` boot
that **did** relocate is `FAIL`, and the forbidden-flag check runs against the
**assembled argv** rather than against the script's prose. Fixture:
`scripts/check/fixtures/arm64_boot_contract_probe.c`.

Sabotage-verified, so the PASS is not tautological. Neutering ONE instruction —
turning the relocation stub's `b.eq .Lcrt0_at_link_addr` into an unconditional
`b`, i.e. never copying the image — flips it:

| variant | verdict | exit |
|---|---|---|
| unmodified crt0.S | `PASS — 10 marker(s) checked in each of 2 boot paths ...` | 0 |
| relocation stub neutered | `FAIL — real-firmware boot did not print every boot marker` (`missing marker in real-firmware boot: [probe] c-start`) | 1 |

The sabotaged serial log is itself the clearest statement of what the stub buys:

```
[BOOT] ARM64 crt0 entered
[BOOT] ARM64 sctlr ok
[BOOT] ARM64 stack ok
[BOOT] ARM64 bss ok
[BOOT] ARM64 vectors ok
<nothing further — never reaches _c_start>
```

crt0's own markers still print because that code is PC-relative and runs fine
wherever it lands; the boot dies the moment anything depends on a link-time
absolute address (the stack from `_stack_top`, the `_sbss`/`_ebss` window, the
jump into C). So the relocation is load-bearing, and a partial boot cannot be
mistaken for a passing one.

### Remaining work — renumbered

1. ~~Give the unified kernel a real-firmware-loadable boot protocol.~~ **DONE**
   (this entry).
2. Deploy a pure-Simple self-hosted `bin/simple`, build the unified kernel ELF,
   and confirm its own markers under firmware. **This is now the only thing
   between here and migrating the lane** — the boot contract is no longer the
   blocker.
3. Then migrate `check-simpleos-arm64-unified-live.shs` off `-kernel` onto
   `BOOT_PROTOCOL=linux` + the ESP builder, keeping every existing assertion.
   **NOT done here, deliberately**: with no buildable unified kernel there is no
   way to show its markers still fire, and this doc's own standing rule is that
   a migration must not be landed on unverified assertions.
4. Physical board bring-up for aarch64 remains filed as before. Note the change
   above moves *toward* it: an arm64 Linux `Image` is directly loadable by U-Boot
   and by any UEFI loader on real hardware, which QEMU `-kernel` never was.

**Status: kernel-side boot-protocol gap CLOSED. Lane migration STILL OPEN,
now blocked only on the self-hosted compiler (item 2).**

## Lane J re-verification 2026-08-17 (classified by CONTENT, not SHA ancestry)

**Verdict: STILL-OPEN, correctly described.** The doc's own split is accurate: the
EFI-application half is fixed and gated; the `-kernel` half of
`scripts/check/check-simpleos-arm64-unified-live.shs` is explicitly blocked on a
self-hosted `bin/simple` that can build the unified kernel. Not actionable by this
lane — a bootstrap is live at ~98% CPU and this lane is forbidden from running one.
