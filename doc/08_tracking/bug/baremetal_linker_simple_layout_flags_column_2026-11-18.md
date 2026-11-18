# check-baremetal-efi-boot --linker simple: layout compare read the ES column, and the i686 gate rejected x86_64

- Status: verification-pending
- Found: 2026-11-18, Opus review of PR #10165. That PR was merged at its earlier head `1505e06` (merge `83a40c9ddbf`) before the fix landed.
- Where: `scripts/check/check-baremetal-efi-boot.shs`.

## Defects
1. `layout_of` tested `$6 ~ /A/`. After the `[Nr]` strip, `$6` is the ES column (hex, never `A`), so both layouts came out empty. Every `--linker simple` run failed with `layout-empty`, so the check could never pass.
2. `llvm-readelf` ran inside a pipeline whose status came from `sort`, so a readelf failure went unnoticed.
3. After the merge with the i686 lane, `[ "$a" = i686 ] || why=simple-linker-unsupported-arch` came before the elf_boot_link path, so `--linker simple` rejected x86_64/aarch64/riscv64.
4. x86_64 `--linker simple` still wrapped the image with lld-link: there was no `efi_stub_x86_64.S` for the in-house `pe_efi_blob` wrapper.

## Fix
- `layout_of <elf> <out>` writes readelf output to a file, checks readelf's status directly, and tests `$7` (Flg). Both layouts must be non-empty.
- The i686 path is gated on `linker=simple && a=i686`.
- New `efi_stub_x86_64.S`. x86_64/aarch64 link it first and are wrapped by `baremetal-efi-wrap.spl`.
- New `BM_QEMU_MEM` setting.

## Verification
- Repro: before the fix, `--linker simple --arch x86_64` stops with `simple-linker-unsupported-arch` / `layout-empty`.
- Pending: x86_64 OVMF exact transcript with `--linker simple`. It is queued in the WSL small slot (`C:/dev/wt/xc-wsl-scripts/sbm-x64_boot3.out`).
