# Showcase cell #7 gate reaches branch 29/52 and fails closed on a missing `mcopy` (mtools) — 2026-08-01

## Status

OPEN. Host-provisioning gap in the gate's **verification** tooling, not a
product defect. The gate is correct to fail closed; it must not be weakened.

This supersedes the previously recorded blocker
(`simpleos_wm_freestanding_new_fabricated_symbols_2026-08-01`, 4 unbaselined
fabricated symbols) — see "The prior blocker is gone" below.

## Captured verdict (PROVED — transcript)

```
simpleos_wm_fullscreen_status=fail
simpleos_wm_fullscreen_reason=browser-demo-real-elf-not-staged
simpleos_wm_fullscreen_browser_demo_disk_status=mcopy-unavailable
simpleos_wm_fullscreen_kernel_build_status=current-source-built
simpleos_wm_fullscreen_kernel_sha256=66c063149e76cf2933edb08dffb67e593c943c8933f47a3ef2969dd23019b349
simpleos_wm_fullscreen_kernel_admission_sha256=af9e0081db8750c9d991c272146261ddb00cb792881298596ae6d180fd3995f4
simpleos_wm_fullscreen_kernel_source_revision_sha256=9f80f5e4df34696e5b521872652be3421c99428121244352c4974e5f137a9785
simpleos_wm_fullscreen_disk_image_status=pass
simpleos_wm_fullscreen_disk_image_provenance=built-from-admitted-kernel
simpleos_wm_fullscreen_disk_image_sha256=13f17067e41508f8e2a246968978913f83220dbabb596c934a1507a009082766
simpleos_wm_fullscreen_browser_demo_build_status=pass
simpleos_wm_fullscreen_browser_demo_binary_sha256=5f6088989e7305880c58699c7e73f51a3abf737ae342d83647a886bf414a5ee3
simpleos_wm_fullscreen_font_asset_sha256=2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081
simpleos_wm_fullscreen_serial_log_bytes=0
```

This is **branch 29 of 52** (`scripts/check/check-simpleos-wm-fullscreen-evidence.shs:709`).
The previous recorded run (2026-07-31) reached **branch 18**
(`wm-simple-web-build-failed`). Eleven walls cleared in one pass.

## Reproduction

```
Origin tip     55115a82411a596449060679a8c837cc63c48c01 (109,542 files, 57 under assets/fonts)
Worktree       fresh detached git worktree on tmpfs (never the shared WC)
SIMPLE_BIN     build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple
               sha256 c0d1ed629b18fc703bc2671c8a9d9043cd1c705e480d9bf511f03233843342b1
               --version "simple-bootstrap 1.0.0-beta"  (pure-Simple stage3; NOT the Rust seed —
               the gate's wall 2/5 seed rejection passed, simple_bin_status=pass)
wrapper sha256 e81fb6cc22c70a4c8350dab0f1bdc55f5cad8ff54feea8694c4c8844ebe7b7e5
               (byte-identical to the wrapper the 2026-07-31 run used — the gate itself did not change)
BUILD_DIR      tmpfs (btrfs is metadata-exhausted on this host; `dd` into build/ hangs in D state)
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

## Root cause (PROVED)

`browser_demo_disk_payload_status()` (wrapper lines 273-279) returns
`mcopy-unavailable` when `mcopy` is not on PATH, and line 708 turns any
non-`pass` into `reason=browser-demo-real-elf-not-staged`.

```
which mcopy mdir mtype   -> not found
apt-cache policy mtools  -> Installed: (none)   Candidate: 4.0.43-1build1
sudo -n true             -> "sudo: a password is required"
```

The verifier's job is to `mcopy` `::/SYS/APPS/BROWSMF.SMF` out of the FAT32
image and prove its first `binary_bytes` bytes hash-match the freshly built
`browser_demo.elf` — i.e. that the image carries the **real** ELF, not a stub.
Without mtools it cannot read the image, so it fails closed. That is correct
behaviour.

## The payload IS actually staged — this is verification-only (PROVED)

The 128 MiB image was built successfully (`disk_image_status=pass`,
`provenance=built-from-admitted-kernel`) by the in-repo staging path, which does
**not** need mtools. Reading the raw 8.3 directory entries out of the image
confirms the expected files are present:

```
strings -a fat32-x86_64-font.img | grep -E '^(BROWSMF|NOTOSANS|KERNEL)'
  BROWSMF SMF
  KERNEL  ELF
  NOTOSANS
  NOTOSANSOFL
  NOTOSANSPB
```

So the reason string `browser-demo-real-elf-not-staged` is, on this host,
**misleading**: the ELF is staged; the checker simply cannot open the image.
The byte-identity half of the claim (does the SMF really wrap the just-built
ELF?) remains **unverified** — only mtools can settle that, which is exactly
why the gate refuses to proceed.

## The prior blocker is GONE (PROVED)

`config/freestanding_fabricated_stub_baseline.sdn` ratchet output this run:

```
Freestanding unresolved symbol check: 120 unexpected symbol(s)
Fabricated freestanding stubs: 120 symbol(s) ... (baseline: 120 known, 0 new)
```

`0 new` — versus `120 known, 4 new` on 2026-07-31
(`rt_cuda_device_identity`, `rt_raw_i64_to_string`, `rt_string_byte_at`,
`rt_vulkan_accepted_compute_submit_count`). The baseline file is unchanged at
192 lines, so this was **not** absorbed by a baseline write; the entry closure
stopped reaching those four symbols. The kernel now links:

```
Linked (freestanding): simpleos_wm_production_desktop.elf.candidate (11796 KB)
  via clang --target=x86_64-unknown-elf
Build complete: 731 compiled, 0 cached, 0 failed
  Time: 72.1s compile + 168.9s link = 241.0s total
```

`doc/08_tracking/bug/simpleos_wm_freestanding_new_fabricated_symbols_2026-07-31.md`
should be marked RESOLVED on the strength of this run.

## Walls now known to pass (first time on this host)

1-17 as before, plus, newly: **18** build succeeds, **19** valid ELF, **20**
candidate sha256, **21** source manifest stable across the build, **22**
admitted-kernel sha256, **23** browser-demo client builds, **24** its hash,
**25** pinned font staged to the disk, **26** disk kernel == admitted kernel,
**27** FAT32 production disk valid, **28** disk image sha256. Blocked at **29**.

Never reached, still entirely unmeasured: **30** (`grub-mkstandalone` →
`BOOTX64.EFI`), all of phase B (**31-41**, QEMU/OVMF boot, scanout discovery,
QMP capture) and all of phase C (**42-52**, the browser/HDA/font-region oracle
ladder). `serial_log_bytes=0` — QEMU has still never been started by this gate
on this host.

## Fix

Install mtools (`apt-get install mtools`, candidate 4.0.43-1build1). Requires
root; **not available to the agent session that found this** (`sudo -n` refuses).
This is provisioning, not a gate change — supplying the tool the gate has always
required is intended usage, the same shape as the `assets/fonts` restore that
cleared wall 7 for cells #4-#6.

Secondary, optional and separable: `mcopy-unavailable` is a *host* fault being
reported through a *product* reason string. Splitting it out (e.g.
`reason=mtools-not-found`, alongside the existing
`qemu-system-x86_64-not-found` / `grub-mkstandalone-not-found` prerequisite
walls, which are checked up front at lines 446/461) would stop a missing host
package from reading as a staging defect, and would fail in 0 s instead of after
a 241 s kernel build. Not applied here — it changes gate semantics and is the
owner's call.

## Do not

- Do not stub, skip, or short-circuit `browser_demo_disk_payload_status()`.
- Do not set `SIMPLE_FABRICATED_STUB_BASELINE_WRITE=1` or add rows to
  `config/freestanding_fabricated_stub_baseline.sdn`.
- Do not fabricate the `FONT_REGION_EXPECTED_SHA256` region oracle (branch 50)
  or its deliberate-red calibration counterpart (branch 51).

## Next step

Provision mtools, then re-run. Expect the run to either pass branch 29 or
produce the first genuinely new information about the SMF payload; either way
the next unknown is branch 30 and then the **first QEMU boot** this gate has
ever performed on linux-x86_64. Budget ~4 min for the kernel build plus the
QEMU phase.
