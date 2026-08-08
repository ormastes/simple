# vendor/ Manifest

Declares allowed entries under `vendor/` (vendored third-party prebuilt
binaries checked into git — not compiler output, not source we maintain).
Enforced by `scripts/check-workspace-root-guard.shs`.

## Allowed Entries

| Entry | Description |
|---|---|
| `FILE.md` | This manifest |
| `limine` | Limine UEFI bootloader EFI applications (BOOTX64.EFI, BOOTAA64.EFI) — provisioned via `scripts/os/provision_limine_efi.shs`, consumed by `desktop_uefi_bootloader_path()` in `src/os/_QemuRunner/scenario_catalog.spl` |

**No other files at this level.**
