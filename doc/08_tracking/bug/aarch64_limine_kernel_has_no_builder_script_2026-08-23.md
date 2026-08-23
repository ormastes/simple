# aarch64 Limine kernel.elf has no builder script — the last reproducibility gap in the arm64 real-firmware lane

**Filed:** 2026-08-23
**Status:** OPEN — lane is GREEN today, but only because the kernel was built by
a hand-typed command recovered from a 2026-07-14 bug record.
**Severity:** medium (reproducibility, not correctness)

## Summary

`scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs` requires
`build/os/aarch64_limine/kernel.elf`. `scripts/os/build-simpleos-aarch64-efi-esp.shs`
deliberately does **not** build it (see its header, lines 54-62) and dies with
`missing kernel ELF ...` when it is absent. `build/` is gitignored, so a clean
clone has no kernel and the gate ERRORs.

This is the same class of hole that the ESP builder itself was written to close
(`doc/08_tracking/bug/arm64_efi_real_firmware_lane_unreproducible_and_unified_lane_uses_kernel_2026-08-11.md`),
one level further up the chain: the ESP is now reproducible, its payload is not.

## Evidence

Before the manual build, on this host:

```
$ ls build/os/aarch64_limine/
ls: build/os/aarch64_limine/: No such file or directory
```

No script anywhere produces it:

```
$ grep -rn "aarch64_limine" scripts/
scripts/os/build-simpleos-aarch64-efi-esp.shs   (consumes it)
scripts/check/check-simpleos-aarch64-limine-framebuffer.shs   (consumes it)
scripts/check/check-simpleos-arm64-efi-real-firmware-boot.shs (consumes it)
scripts/check/guard_wiring_optout.txt:360        (opt-out citing exactly this gap)
```

`grep -rn "linker_limine"` over `*.shs` returns **zero** build scripts — only the
linker script itself, `limine_entry.spl`, `freestanding_runtime.c`, and docs.

## The command that works (verified 2026-08-23, this host, macOS arm64)

Recovered verbatim from
`doc/08_tracking/bug/aarch64_real_firmware_boot_gap_and_seed_defects_2026-07-14.md:663-667`:

```sh
bin/simple native-build \
  --backend cranelift \
  --entry-closure \
  --entry examples/09_embedded/simple_os/arch/aarch64/limine_entry.spl \
  --target aarch64-unknown-none-elf \
  --linker-script examples/09_embedded/simple_os/arch/aarch64/boot/linker_limine.ld \
  -o build/os/aarch64_limine/kernel.elf
```

Output (verbatim, 6 lines):

```
Freestanding unresolved symbol check: 3 unexpected symbol(s)
Freestanding unresolved precheck deferred to linker: 2 candidate symbol(s)
Linked (freestanding): build/os/aarch64_limine/kernel.elf (103 KB) via clang --target=aarch64-none-elf
Build complete: 9 compiled, 0 cached, 0 failed
  Binary: build/os/aarch64_limine/kernel.elf (103 KB)
  Time: 0.3s compile + 1.0s link = 1.3s total
```

105,928 bytes. It boots end to end — see the PASS verdicts below.

## Why no script was written here

Every sibling builder (`scripts/os/simpleos-native-build-aarch64.shs`, etc.)
routes compiler selection through `scripts/lib/simple-compiler-select.shs`, which
**rejects the Rust bootstrap seed** and demands a Stage2 admission receipt. The
command above was run with `bin/simple`, which on this host reports
`simple-bootstrap 1.0.0-beta` — i.e. exactly the compiler that selection helper
is built to refuse. Writing a builder therefore means deciding one of:

  (a) this kernel lane is exempt from the self-hosted-builder policy, or
  (b) the lane waits for a deployed full-CLI Stage 4 binary.

That is a policy call, not a mechanical fix, so it is filed rather than decided.

## Secondary observation (UNVERIFIED)

The build reports `Freestanding unresolved symbol check: 3 unexpected symbol(s)`
without naming them, and defers 2 more to the linker. The link succeeds and the
kernel boots, so these are **not** currently harmful. **UNVERIFIED hypothesis:**
these are the same tolerated-undefined-symbol class as
`doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`,
where a NULL GOT slot became a SIGSEGV at run time. Not chased here. The message
not naming the symbols is itself a diagnosability gap.

## Current lane state (2026-08-23, after the manual kernel build)

All three verdicts are the last line of stdout, exit 0:

```
PASS — 4 boot-stage marker(s) checked, EDK2/AAVMF pflash real-firmware aarch64 boot verified via BOOTAA64.EFI on a FAT ESP (no -kernel, no isa-debug-exit), 90 serial line(s) captured; firmware /opt/homebrew/share/qemu/edk2-aarch64-code.fd
PASS — real-firmware (EDK2/AAVMF pflash + Limine BOOTAA64.EFI) aarch64 boot obtained a framebuffer: addr=0x18446462600284340224 800x600 bpp=32 pitch=3200; 3 refusal paths checked and none fired
PASS — 10 marker(s) checked in each of 2 boot paths, unified arm64 early-boot verified under EDK2/AAVMF pflash real firmware via Limine BOOTAA64.EFI `protocol: linux` (no -kernel, no isa-debug-exit, self-relocation exercised) and unchanged under legacy -kernel
```

## Stale claim this retires

`scripts/check/guard_wiring_optout.txt:360` says of
`check-simpleos-aarch64-limine-framebuffer.shs`: *"no script anywhere in
scripts/ or .github/workflows/ builds this ESP FAT image + Limine BOOTAA64.EFI +
kernel ELF assembly"*. **Half stale:** the ESP half now has a builder
(`scripts/os/build-simpleos-aarch64-efi-esp.shs`) and the gate PASSes on this
host. The kernel-ELF half is still true and is what this record tracks. The
opt-out row was left in place rather than edited, to avoid perturbing
`check-guard-wiring.shs` for concurrent sessions; re-triage it together with the
builder decision above.
