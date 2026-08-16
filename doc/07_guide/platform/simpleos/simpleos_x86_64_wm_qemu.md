# SimpleOS x86_64 WM QEMU Verification

This lane verifies the canonical Simple x86_64 Engine2D desktop entry under
`qemu-system-x86_64` with the BGA/`std` VGA linear framebuffer, booted through
**real firmware**: OVMF pflash → GRUB standalone EFI → multiboot1 ELF32 wrap.

It is the sibling of `simpleos_arm64_wm_qemu.md`. Read both as a pair: the ARM64
lane is currently the *convenience* lane and the x86_64 lane is the
*board-runnable* one.

## Why x86_64 Is the Board-Runnable Proxy

`.claude/rules/board-runnable.md` requires that QEMU-developed work stay runnable
on real hardware, and names the mechanism: boot via a real-firmware proxy, never
QEMU `-kernel` pass semantics and never `isa-debug-exit`.

The x86_64 WM lane satisfies that literally:

- **OVMF pflash.** Two `-drive if=pflash` images — a read-only `OVMF_CODE` and a
  per-run writable copy of `OVMF_VARS`. This is UEFI, the same firmware interface
  a physical x86_64 board presents.
- **GRUB standalone EFI.** `grub-mkstandalone --format=x86_64-efi` packages
  `grub.cfg` plus `/boot/kernel.elf` into a single `EFI/BOOT/BOOTX64.EFI` on a
  FAT ESP. The ESP is attached as an ordinary `virtio-blk-pci` boot device
  (`bootindex=0`), so the firmware performs a normal removable-media UEFI boot.
- **multiboot1 ELF32 wrap.** GRUB hands off with `multiboot /boot/kernel.elf`;
  the kernel arrives at the shared `crt0.s` `_start`. The ELF32 wrap step is why
  an `llvm-objcopy` must be on `PATH` for the build.
- **No `isa-debug-exit`.** The gate never uses a QEMU-only exit device; results
  come from the guest's own serial receipts and from host-side QMP.

The ARM64 lane, by contrast, boots with `-kernel build/os/simpleos_arm64_wm.elf`
and has no EFI stub, so it is *not* board-runnable today. That gap is exactly the
kind of thing the rule forbids leaving implicit — state it whenever an ARM64-only
result is reported.

## Guest Entry Point and Event Loop

| Piece | File |
|-------|------|
| Entry | `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl` |
| Event loop | `src/os/desktop/shell.spl` — `DesktopShell.run_baremetal(executor)` |
| PS/2 decode | `src/os/compositor/ps2_wm_key_decode.spl` (`ps2_wm_key_name`, `ps2_wm_character`) |
| Freestanding C stubs | `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c` |

`gui_entry_desktop.spl` prints `[desktop-gui] spl_start` as the very first
statement of `spl_start()` — that marker (not the generic `[boot] memory init OK`
used by other gates, which belongs to a different entry point) is what the
readiness script waits for. The entry then installs the generated Aetheric theme
snapshot, mounts the VFS, applies the boot theme CSS, constructs
`Engine2dWmFrameExecutor`, renders the canonical first frame, and enters
`run_baremetal`.

`run_baremetal` polls the PS/2 controller status port `0x64` directly; when a byte
is ready it calls `handle_input_baremetal_ps2()` on the compositor. Every accepted
input edge produces a serial receipt so the host harness can correlate injection
with guest-side effect.

### Serial receipt markers the gate correlates

| Marker | Meaning |
|--------|---------|
| `[desktop-gui] spl_start` | kernel entry reached (readiness script's boot marker) |
| `[BOOT64] call _start` | multiboot handoff into the shared crt0 |
| `[grub-uefi] multiboot loading` | GRUB's own echo — proves the EFI app ran |
| `[scanout-evidence]` | guest-reported framebuffer address/width/height/stride/pixel_format/generation plus BGA PCI decode. **The only accepted source of scanout metadata** — no host-side defaults |
| `[production-readiness]` | WM live, GUI object tree + Web content frame + engine2d renderer, with process-owned surface count and scanout generation |
| `[wm-input-irq]` | keyboard edge accepted: `input_seq=<n> scancode=87 kind=press` / `scancode=215 kind=release` |
| `[wm-state]` | resulting WM state for that `input_seq`: action, window, maximized, x/y/width/height |
| `[wm-frame]` | `input_seq=<n> generation=<positive>` — the render that the input caused |
| `[wm-pointer-irq]` | pointer edge: `input_seq`, x, y, `button_code`, `kind_code` |
| `[wm-pointer-state]` | pointer outcome: `input_seq`, window, and the `[simpleos-wm] loop-step` command marker |
| `[wm-pointer-frame]` | `input_seq=<n> generation=<n>` for the pointer-driven render |

The correlation rule is strict in both directions: for each injected edge the gate
requires a *complete* `irq → state → frame` chain, with a sequence number strictly
newer than the one before it and a positive frame generation. A frame without its
irq, or an irq without its frame, is not evidence.

`[wm-frame]` is also used for non-input render receipts (`host-gpu-fallback`,
`content-provenance-rejected`, `window-degraded`); only the `input_seq=`/
`generation=` form participates in input correlation.

## Host Prerequisites (macOS specifically)

The discovery ladders below matter most on macOS, where nothing lands on the
Linux paths the scripts originally hardcoded. **All of these are now
auto-discovered by the wrappers** (fixed 2026-08-04), so a stock Homebrew machine
should not need any env override.

| Tool | Where it actually is on macOS | Env override |
|------|-------------------------------|--------------|
| QEMU | `qemu-system-x86_64` from `brew install qemu` | `QEMU_SYSTEM_X86_64` (readiness script) |
| OVMF code | `/opt/homebrew/share/qemu/edk2-x86_64-code.fd` (Linux: `/usr/share/OVMF/OVMF_CODE_4M.fd`) | `OVMF_CODE` |
| OVMF vars | `/opt/homebrew/share/qemu/edk2-i386-vars.fd` — yes, the *i386* vars image is the shared one (Linux: `OVMF_VARS_4M.fd`) | `OVMF_VARS_SRC` |
| GRUB | `x86_64-elf-grub-mkstandalone`, from the **keg-only** `x86_64-elf-grub` formula, so usually **off `PATH`**; also at `/opt/homebrew/opt/x86_64-elf-grub/bin/` | `GRUB_MKSTANDALONE` |
| mtools | `mcopy` — used to extract `::/SYS/APPS/BROWSMF.SMF` back out of the staged FAT32 image to verify the browser-demo payload landed | — |
| llvm-objcopy | `/opt/homebrew/opt/llvm/bin` (also `/usr/local/opt/llvm/bin`, `/usr/lib/llvm-{20,19,18,17}/bin`); prepended to `PATH` for the ELF32 multiboot wrap | — |
| clang | any `clang` on `PATH` — checked by the preflight; used to build the browser-demo guest client. It must **not** be assumed to be `clang-20` (Homebrew ships 22) | `CLANG` in `scripts/os/build_browser_demo_client.shs` |

The compiler binary itself is resolved by the canonical gate and is **fail-closed
against the Rust seed**: paths under `src/compiler_rust/` or `compiler_rust/target/`
are rejected outright, and the binary's `--version` string is rejected if it
contains `rust-built`, `rust seed`, or `bootstrap seed`. With `SIMPLE_BIN` unset
the gate auto-selects the first non-seed candidate from
`build/bootstrap/stage3/*/simple`, `build/bootstrap/stage2/*/simple`,
`bin/release/*/simple`, `release/*/simple`, `bin/simple`.

## Commands, in Run Order

### 1. Preflight (static, never starts QEMU)

```bash
sh scripts/check/check-simpleos-x86-64-wm-qemu-preflight.shs
```

Checks that the canonical entry, the engine2d baremetal core, both wrappers, the
x86_64 freestanding stub C file, and the HDA audio service exist; that `clang` is
on `PATH`; and that `gui_entry_desktop.spl` installs the generated theme snapshot
and applies the boot theme CSS *before* it constructs `Engine2dWmFrameExecutor`,
and mounts the VFS before the CSS is applied. Ordering violations are named
failures, not warnings.

### 2. Readiness

```bash
sh scripts/check/check-simpleos-x86-64-wm-qemu-readiness.shs
```

With no `SIMPLEOS_KERNEL_ELF` this only proves QEMU can *parse* the q35/`std`-VGA
argument set (it runs QEMU with `-S`, paused) and reports
`x86_64_wm_qemu_readiness: skip` with an explicit
`boot_verification_skipped:` line — it will not claim `ready` off an arg-parse
check alone. Point `SIMPLEOS_KERNEL_ELF` at a built kernel to make it do a real
OVMF/GRUB boot and wait for `[desktop-gui] spl_start`:

```bash
SIMPLEOS_KERNEL_ELF=build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf \
  sh scripts/check/check-simpleos-x86-64-wm-qemu-readiness.shs
```

Env knobs: `X86_64_WM_QEMU_READINESS_TIMEOUT` (arg-parse dry run, default 3s),
`X86_64_WM_QEMU_BOOT_WAIT` (boot marker wait, default 60s), `OVMF_CODE`,
`OVMF_VARS_SRC`, `GRUB_MKSTANDALONE`, `QEMU_SYSTEM_X86_64`. The accelerator is
selected by host: `hvf` on Darwin/x86_64, `kvm` on Linux/x86_64 with `/dev/kvm`,
otherwise `tcg` with `-cpu qemu64`.

Note the memory setting is **2G, not 512M**: GRUB's EFI loader OOMs
(`error: out of memory`) loading the ~17MB multiboot desktop kernel under 512M.

### 3. Canonical gate

```bash
BUILD_DIR=build/simpleos_wm_fullscreen_evidence \
SIMPLE_BIN=build/bootstrap/stage3/aarch64-apple-darwin/simple \
SIMPLEOS_WM_READINESS_TIMEOUT_MS=900000 \
  sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

This is the owner of the lane. In order it: resolves and attests `SIMPLE_BIN`;
verifies the pinned font asset by exact byte count (1,708,408) and SHA-256;
locates QEMU / GRUB / OVMF; builds the browser-demo guest client; native-builds
the kernel; stages the FAT32 disk; packages the GRUB EFI app; launches QEMU;
waits for readiness; then injects input over QMP and correlates.

The kernel native-build invocation is:

```text
SIMPLE_BOOTSTRAP=1 SIMPLE_LIB=<root>/src SIMPLE_OS_LOG_MODE=off
SIMPLE_ALLOW_FREESTANDING_STUBS=1 PATH=<llvm-objcopy dir>:$PATH
  $SIMPLE_BIN native-build
    --source build/os/generated --source <entry>
    --timeout 870 --backend cranelift --cpu x86-64-v1 --opt-level=none --log off
    --cache-dir $BUILD_DIR/native-cache --mode dynload
    --entry-closure --entry <entry>
    --target x86_64-unknown-none -o <kernel>
    --linker-script <linker.ld>
```

The build is bracketed by a source-revision hash taken **before and after**; if a
concurrent session edits `src/os/**` mid-build the run fails
`wm-simple-web-build-source-changed` rather than shipping a mixed kernel. On
success it writes a `<kernel>.admission` record (`schema=simpleos-wm-kernel-admission-v1`)
carrying the wrapper SHA-256, the compiler SHA-256, the profile string
`cranelift|x86-64-v1|none|dynload`, the source-revision SHA-256, and the kernel
SHA-256. Timeouts: `SIMPLEOS_WM_NATIVE_BUILD_TIMEOUT_SECONDS` (900) and
`SIMPLEOS_WM_NATIVE_BUILD_WORKER_TIMEOUT_SECONDS` (870).

Disk staging runs `scripts/os/make_os_disk.shs` to produce
`$BUILD_DIR/fat32-x86_64-font.img` (overridable with `SIMPLEOS_WM_DISK_IMAGE`)
containing the pinned font at guest path `/SYS/FONTS/NOTOSANS` and the browser
demo at `::/SYS/APPS/BROWSMF.SMF`; the payload is re-extracted with `mcopy` and
hash-compared. The image is attached as an NVMe device
(`-device nvme,serial=deadbeef` over `snapshot=on`), which is how the guest
performs its font load.

The QEMU command line is:

```text
qemu-system-x86_64 -no-user-config -monitor none -net none
  -machine q35 -cpu max -m 2G
  -serial file:$SERIAL_LOG -display none -no-reboot
  -drive if=pflash,format=raw,readonly=on,file=$OVMF_CODE
  -drive if=pflash,format=raw,file=$OVMF_VARS
  -drive file=fat:rw:$ESP,format=raw,id=esp,if=none
  -device virtio-blk-pci,drive=esp,bootindex=0
  -vga std -global VGA.vgamem_mb=64
  -drive file=$DISK_IMAGE,if=none,id=nvm,format=raw,snapshot=on
  -device nvme,serial=deadbeef,drive=nvm
  -audiodev driver=none,id=simpleos-audio -device intel-hda
  -device hda-output,audiodev=simpleos-audio
  -qmp unix:$QMP_SOCKET,server,nowait
```

`vgamem_mb=64` is load-bearing: QEMU's 16MB `std`-VGA default cannot hold a
3840x2160x32bpp (~33.2MB) framebuffer, and BGA would silently clamp or reject the
mode.

`SIMPLEOS_WM_READINESS_TIMEOUT_MS` (default 60000) bounds the wait for
`[scanout-evidence]` + `[production-readiness]` + a font marker. **TCG hosts need
about 900000.** An x86_64 guest on an arm64 Mac has no hardware acceleration, and
the initial desktop bring-up performs a full 4K CPU-fallback layout with
pure-Simple glyf rasterization; 60s is nowhere near enough. The knob only extends
waiting for the *same* markers — no gate semantics change. The wait also breaks
early on a production fault or on a >1MiB serial fault storm.

After readiness the gate drives QMP `input-send-event` for key and pointer edges
and uses HMP `pmemsave` (through QMP) to pull the guest framebuffer region back to
the host, so a guest-computed font region can be independently re-derived from
device memory rather than trusted from the guest's own claim. Input correlation
budgets are 300s for a press (every step sets `need_render`, forcing a full 4K
re-render under TCG) and 30s for a release.

### 4. Hello-lifecycle lane

```bash
sh scripts/check/check-simpleos-x86-64-wm-hello-lifecycle-evidence.shs
```

A narrower, default-runnable lane over the glass WM entry
(`examples/09_embedded/simple_os/arch/x86_64/wm_entry.spl`), same real-firmware
boot path. It proves BOOT (desktop composited with the Hello window, window 3,
validated by real pixel counts for title ink, `Hello, SimpleOS!` vector-text ink,
and the rose close dot), RUN (a 4x zoom crop PNG of the body-text region), and
CLOSE (a QMP `input-send-event` click on the close button, adaptively aimed using
the WM's own `[wm-event] mouse_move` markers, then `[wm-event] type=window
detail=action=close,win=3`, `[WM] window closed: hello`, and a second screendump
showing the window gone with the rest of the scene intact). Env knobs:
`WM_HELLO_READY_TIMEOUT_MS` (120000), `WM_HELLO_CLOSE_TIMEOUT_MS` (30000). It
never silently skips — every missing tool or failed step prints a named blocker
and exits nonzero.

## Artifacts

Everything the canonical gate produces lands under
`build/simpleos_wm_fullscreen_evidence/` (`$BUILD_DIR`):

| File | Contents |
|------|----------|
| `native-build.out` | full kernel native-build log — first stop for a build failure |
| `simpleos_wm_production_desktop.elf` | the kernel |
| `simpleos_wm_production_desktop.elf.admission` | kernel admission record (wrapper/compiler/source/kernel hashes) |
| `build-browser-demo.out` | browser-demo client build log |
| `make-os-disk.out` | FAT32 disk staging log |
| `fat32-x86_64-font.img` | the staged NVMe disk image |
| `uefi/` | ESP tree, `grub.cfg`, per-run `OVMF_VARS_4M.fd`, `esp/EFI/BOOT/BOOTX64.EFI` |
| `serial.log` | guest serial — the primary evidence stream |
| `qemu.out` | QEMU's own stdout/stderr (an empty file during a guest hang is itself a finding) |
| `capture.out` | QMP driver output |
| `evidence.env` | machine-readable verdict: `simpleos_wm_fullscreen_status`, `_reason`, and every attested hash/status key |
| `*.ppm` / `*.raw` / `font-region.rgb` | screendumps and the `pmemsave`-derived font region |

The readiness script writes its own serial log to
`build/os/check_simpleos_x86_64_wm_qemu_readiness.serial.log` and its ESP to
`build/os/wm_qemu_readiness_uefi/`; the hello lane uses
`build/os/wm_hello_build.log` and `build/os/wm_hello_uefi/`.

Start at `evidence.env` for the verdict, then `serial.log` for what the guest
actually said, then `native-build.out` / `qemu.out` for anything that failed
before the guest spoke.

## Troubleshooting

Everything below is a failure that really happened on this lane.

### Link refuses to fabricate symbols — do not re-baseline

```text
would FABRICATE 3 symbol(s) not in the baseline:
  rt_find, rt_native_cmp, rt_string_partition
```

These are emitted by the pure-Simple stage3 codegen for erased-receiver method
calls (the `bare_rt_redirect` class); the Rust seed emits none of them, so they
appear only once you move to a stage3 driver. Real call sites include
`src/lib/log.spl` (`line.partition(" ")`), the `env/variables.spl` pair, and
`src/lib/common/ui/draw_ir_sdn.spl` (`part.find("=")`); `rt_native_cmp` comes from
erased `<`/`>` comparisons in nearly every module.

**The fix is a real implementation in
`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`, never an
entry in `config/freestanding_fabricated_stub_baseline.sdn`.** A fabricated weak
body returns 0 and silently corrupts every caller — the link refusal is doing its
job. The three now have real bodies (`rt_string_partition` with Python
`str.partition` semantics; `rt_find` dispatching on receiver heap type;
`rt_native_cmp` comparing heap strings via `rt_text_cmp_any` and otherwise doing a
signed word compare, which is correct for `ENCODE_INT`-tagged operands because the
tag is an order-preserving `<<3`). `S1(rt_array_sort)`'s fatal stub was likewise
replaced with a real stable insertion sort.

Latent parity gap: `src/runtime/runtime_native.c` and the Rust runtime still lack
all three.

### `missing browser-demo compiler: clang-20`

`scripts/os/build_browser_demo_client.shs` used to hardcode `CLANG=clang-20` with
no fallback; Homebrew ships clang-22, keg-only. It now has a discovery ladder.
If you still hit it, set `CLANG` explicitly.

### `invalid browser-demo ELF` on macOS

The script's ELF machine check
(`od -An -tu1 -j 18 -N 2 "$OUT" | awk '{print $1 + 256*$2}'`) produced `62` then a
spurious `0` on macOS, because BSD `od` emits a trailing address-only line. Fixed
with `awk 'NR == 1'`. Any similar `od`-based check in a script you add needs the
same guard.

### `grub-mkstandalone not found` / `ovmf-code-not-found` / `ovmf-vars-not-found`

Homebrew's cross-GRUB is keg-only and off `PATH`, and its OVMF images are edk2
files under `/opt/homebrew/share/qemu/`. Both discovery ladders are now in all
three wrappers; if a machine still misses, set `GRUB_MKSTANDALONE`, `OVMF_CODE`,
and `OVMF_VARS_SRC` explicitly (see the prerequisites table).

### Guest fault — `field access on nil receiver`

Symbolize it directly against the kernel ELF; you do not need to hunt address
ranges with `llvm-nm | sort | awk`:

```bash
llvm-symbolizer --obj=build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf 0x8073034
```

That named `lib__common__encoding__sfnt__parse_fvar_axes` immediately. The root
cause was a value-position `match` (`val table = match maybe_table: Some(value):
value / None: return []`) compiling to two discriminant-hash checks with a
fall-through default that loaded the nil sentinel `0x3`; the `Some` arm matched
neither check, so `table.offset` tripped the nil guard. Statement-form matches on
the same `Option<OtTable>` work — only the extraction-into-`val` shape
mis-discriminates on the freestanding lane. Worked around in
`src/lib/common/encoding/sfnt.spl` with an Option-free flat scan.
Bug: `doc/08_tracking/bug/sfnt_fvar_option_match_nil_baremetal_2026-08-04.md`.

### `[PANIC] heap exhausted`

```text
[PANIC] heap exhausted heap_off=0x1ffffa60 req=0x800 limit=0x20000000
```

Read the arithmetic: `limit=0x20000000` is 512MiB and `heap_off` is one 2KiB
request short of it. The baremetal allocator is a **no-free bump allocator**, so
every allocation any render ever makes is permanent for the session — initial
desktop bring-up alone (3 app surfaces plus web-content font/style layout at 4K
CPU fallback) exhausted 512MB. `BAREMETAL_HEAP_SIZE` in `baremetal_stubs.c` is now
1GiB (warn threshold 448MB → 896MB). That is a ceiling raise, not a fix; the real
fix is frame-arena mark/release —
`doc/08_tracking/bug/simpleos_bump_heap_no_free_interactive_session_2026-07-26.md`.

### Readiness times out on a TCG host

Set `SIMPLEOS_WM_READINESS_TIMEOUT_MS=900000`. The default 60000 was a hardcoded
loop until 2026-08-04; the default is unchanged, so an x86_64-guest-on-arm64-Mac
run must pass the knob. See §3 above for why.

### Grep trap: `fault` also matches `default-font`

Searching `serial.log` for `fault` hits `[rfm] at=default-font`. Always search for
the bracketed form:

```bash
grep -a '\[fault\]' build/simpleos_wm_fullscreen_evidence/serial.log
```

### Concurrent sessions

The gate hashes its sources before and after the build window; a peer editing
`src/os/**` mid-build fails the run with `wm-simple-web-build-source-changed`.
That is correct behaviour, not flakiness — re-run when the tree is quiet.

## Current Honest Status

As of 2026-08-04 the ladder gets much further than it did (it previously died at
BUILD, branch ~18 of 52) but **does not pass**. With
`SIMPLEOS_WM_READINESS_TIMEOUT_MS=900000` the run boots under OVMF, reads the font
chain from NVMe (1,708,408 bytes), parses the sfnt, reports

```text
[scanout-evidence] address=2147483648 width=3840 height=2160 generation=1
```

spawns Browser Demo / Hello World / Clang (`[desktop-gui]
process-owned-surfaces-ready count=3`, `launcher apps=15`), falls back to CPU
compositing (`[wm-frame] host-gpu-fallback reason=unavailable-or-readback-capacity
width=3840 height=2160`), lays out live web content — and then stops here:

```text
simpleos_wm_fullscreen_status=fail
simpleos_wm_fullscreen_reason=guest-render-fault
[wm-frame] content-provenance-rejected window_id=3 status=engine2d_rendered backend=software fallback=none material= theme=aetheric_dark source=e13114ec...
[wm-frame] window-degraded window_id=3 reason=unresolved-or-duplicate-content
```

Note `material=` is **empty**. This is a provenance *validation rejection*, not a
crash — there are no exception frames. `serial_has_production_fault` classifies
`content-provenance-rejected` as a production fault, which is what turns it into
`guest-render-fault`.

The retained post-blur run on 2026-08-10 narrows that empty receipt to the
material producer, before the WM validator. Its bounded diagnostic is:

```text
[web-style-producer] entry-rejected ... bg=3424591649 gf=4294967295 gt=4294967295 layers_len=0 backdrop_len=25 animation=none
```

The canonical Aetheric backdrop is the 25-byte
`blur(30px) saturate(170%)`. Two producer defects are covered in current source
after that run: the earlier `184aded7e3f` change parses nested
commas/parentheses in `rgba(...)` gradient stops at their real gradient depth;
the follow-up backdrop change uses an exact byte grammar and overflow-bounded
decimal parser instead of freestanding-unsafe text predicate, split/slice, and
numeric-conversion runtime calls. These changes have focused host tests, but
are **not live-QEMU evidence**; the status remains failed until a newly admitted
kernel emits a 64-hex material receipt and `content-presented`.

**QMP input delivery on the x86_64 WM lane has never been proven.** Input
injection is the branch immediately after readiness, and the run has never reached
it. Any claim that x86_64 WM input works is unsupported today.

Timing on an arm64 Mac under TCG: kernel native-build warm ≈ 45–75s (5 compiled /
726 cached); disk staging and GRUB EFI packaging are fast; QEMU boot to desktop is
several minutes.

### Open bugs for this lane

- `doc/08_tracking/bug/simpleos_wm_gate_provenance_reject_after_boot_chain_fixes_2026-08-04.md`
  — the current stopping point above. Documented rather than fixed because the
  relevant plumbing (`src/os/compositor/shared_mdi_framebuffer_scene.spl`,
  `simple_web_window_renderer.spl`) had another session's uncommitted edits.
- `doc/08_tracking/bug/sfnt_fvar_option_match_nil_baremetal_2026-08-04.md`
  — value-position `Option` match mis-discriminating on the freestanding lane.
- `doc/08_tracking/bug/simpleos_bump_heap_no_free_interactive_session_2026-07-26.md`
  — no-free bump allocator; the 1GiB bump is a stopgap.

Toolchain-side blockers that gate verification more broadly are tracked in
`doc/08_tracking/bug/parser_trailing_comparison_line_continuation_2026-08-04.md`
and
`doc/08_tracking/bug/deployed_binary_missing_rt_raw_i64_to_string_extern_2026-08-04.md`.

## See Also

- `simpleos_arm64_wm_qemu.md` — the ARM64 `virt`/`ramfb` sibling lane.
- `simpleos_dev_guide.md` §8.6 Entry Points, §8.7 QEMU Configuration.
- `.claude/rules/board-runnable.md` — why the real-firmware proxy is mandatory.
## Toolchain deployment desktop gate (source preflight implemented, 2026-08-16)

The canonical executable scenario and manual now fail closed through combined
owner `scripts/check/check-simpleos-toolchain-desktop-boot.shs`; that production
wrapper now implements canonical Stage-4 provenance admission, fail-closed
artifact/receipt preflight, and a hermetic 16-case validator self-test. It does
not claim live acceptance: the canonical fullscreen owner still uses
`-net none`, terminates QEMU after capture, and `gui_entry_desktop.spl` has no
cooperative SSHD poll. The remaining B-DESKTOP-LIVE implementation must preserve one
canonical `gui_entry_desktop.spl` OVMF CODE/per-run VARS/GRUB QEMU lifetime,
bind `[desktop-gui]`, `[production-readiness]`, `[scanout-evidence]`, and
framebuffer proof to the admitted kernel/image, then run the embedded toolchain
version/compile/link/execute commands in that same guest. The exact manifest,
receipt, command, transcript and failure contract is authoritative in
`doc/03_plan/os/simpleos/hw_qemu/x86_64_native_hello_world_plan.md`.

Run the non-live contract check with:

```sh
sh test/01_unit/scripts/simpleos_toolchain_desktop_boot_receipt_contract_test.shs
```

Its `platform_acceptance_claimed=false` marker is mandatory. Default wrapper
mode remains blocked until all real inputs and the same-run desktop/SSH owner
exist; never substitute a historical SSH entry or a second QEMU run.
