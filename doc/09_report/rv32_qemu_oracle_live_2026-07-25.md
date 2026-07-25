# RV32 QEMU Media-Oracle Live Run (AC-9/AC-10)

- status: blocked
- reason: missing-pinned-media-prerequisites
- runner: scripts/os/check_riscv_linux_qemu.shs rv32
- runner_mtime: 2026-07-24 22:49 (fixed to bind provenance + pass exact DTB via -initrd)
- assets_dir: build/os/rv32_soc
- assets_dir_newest_mtime: 2026-07-24 (from an OLDER pre-provenance build pass, ~17h older than the runner it must satisfy)
- attempts_used: 1 of 3 (cap not further spent — failure is deterministic, not flaky)
- exit_code: 1
- decisive_line: "ERROR: missing media manifest: /home/ormastes/dev/pub/simple/build/os/rv32_soc/manifest.txt"
- missing_manifest: build/os/rv32_soc/manifest.txt (required, absent)
- missing_buildroot_dir: build/os/buildroot (required, absent entirely)
- missing_buildroot_manifest: build/os/buildroot/rv32/buildroot-manifest.txt (required, absent)
- missing_opensbi_src: build/os/rv32_soc/opensbi-src (required for provenance cmp, absent)
- missing_initrd_file: build/os/rv32_soc/initramfs.cpio.gz (required exact filename, absent)
- present_but_stale_asset: build/os/rv32_soc/initramfs_login.cpio.gz (older naming from a pre-manifest builder pass, not accepted by current runner)
- present_assets: fw_jump.bin, Image, linux-src/, kbuild/ (all present, all dated to the older pass)
- qemu_binary: qemu-system-riscv32 8.2.2 (present, never reached — gate fails before QEMU launch)
- login_prompt_seen: no
- shell_prompt_seen: no
- ls_root_output_seen: no

## Root cause

`scripts/os/check_riscv_linux_qemu.shs` was rewritten on 2026-07-24 to bind
`fw_jump.bin`/`Image`/`soc_virt.dtb`/`initramfs.cpio.gz` to independent pinned
build provenance via `build/os/rv32_soc/manifest.txt` and
`build/os/buildroot/rv32/buildroot-manifest.txt`, and to pass the exact DTB to
QEMU via `-initrd` (per the prior session's FDT-initrd panic fix). Neither
manifest was ever produced for RV32: `build/os/rv32_soc/` only holds artifacts
from an earlier, pre-provenance builder pass (evidenced by the presence of
`initramfs_login.cpio.gz` — a filename the current builder,
`scripts/os/build_riscv_linux_assets.shs`, no longer emits; it now writes
`initramfs.cpio.gz` + `manifest.txt` together at lines 100-170 of that script).
There is no `build/os/buildroot/` directory at all, and no `opensbi-src/`
clone under `rv32_soc/`, so Buildroot's rootfs/toolchain and OpenSBI's build
provenance were never generated in this tree.

The runner's very first prerequisite gate (`[ -f "$MANIFEST" ]`, line 85 of
the runner) fails immediately, before QEMU is ever launched. This is not a
boot-time or flakiness issue — it is a missing prerequisite-build issue. The
1-attempt result is fully deterministic; a 2nd/3rd retry of the same command
would reproduce the identical failure, so no further attempts were spent per
the "don't grind" rule.

Rebuilding the missing artifacts is out of scope for this bounded check-run
task: per `.spipe/riscv32_riscv64_fpga_simpleos_production/state.md`
(2026-07-24 entries), the Buildroot rootfs/toolchain build alone previously
consumed three full bounded cycles in an earlier session before completing,
and OpenSBI/Linux source clones + builds are a separate, non-trivial pass.
Producing `manifest.txt` + `buildroot-manifest.txt` + `opensbi-src/` for RV32
requires running `scripts/os/build_riscv_linux_assets.shs` and
`scripts/os/build_riscv_buildroot.shs` to completion — a distinct task from
exercising the QEMU oracle, and one that needs its own bounded session(s).

## Verdict

BLOCKED. AC-9/AC-10 cannot be evaluated live for RV32 until the pinned-media
build pipeline (`build_riscv_linux_assets.shs` + `build_riscv_buildroot.shs`)
is re-run to produce `build/os/rv32_soc/manifest.txt`,
`build/os/buildroot/rv32/buildroot-manifest.txt`, and
`build/os/rv32_soc/opensbi-src/`. No login prompt, shell, or `ls /` output was
observed because QEMU was never launched.
