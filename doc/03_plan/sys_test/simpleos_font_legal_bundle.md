# SimpleOS Font Legal Bundle Test Plan

## Scope

Verify that every SimpleOS FAT32, initramfs, and installer staging owner consumes
one 53-file OS projection, preserves the 16 runtime font paths, carries required
provenance/licenses/notices, and rejects stale pinned companion bytes.

The six CLDR XML/source/ranking inputs are excluded from the guest because the
runtime consumes the compiled ranking only. Native font rendering and QEMU
pixel evidence remain covered by the parent shared-font plan.

## Traceability

| Requirement | Executable/manual evidence | Pass condition |
|---|---|---|
| REQ-004 | `test/01_unit/os/port/simpleos_font_bundle_spec.spl` / `doc/06_spec/01_unit/os/port/simpleos_font_bundle_spec.md` | 53 unique paths/aliases; 51 immutable pins; two nonempty root notices; missing/unpinned rejection |
| REQ-004, REQ-005 | `test/02_integration/os/port/simpleos_font_asset_staging_spec.spl` / `doc/06_spec/02_integration/os/port/simpleos_font_asset_staging_spec.md` | four staging owners share the OS projection; TTF registry paths stay unchanged; direct C checksum manifest matches all 35 pinned companions; mono overrides cannot redirect companion reads |
| NFR-001 | `scripts/os/simpleos_font_bundle_companion.sha256` plus the integration spec | every C-staged pinned companion matches `selected_font_bundle_asset_pins()` before image mutation |
| NFR-003 | integration spec, live bridge buffer declarations, and C directory guard | 53 payloads total; fixed FAT directory uses 91/128 entries; projection is 51,932,530 bytes; 25,125,512-byte maximum face fits each 32 MiB live path-read buffer |

## Checks

1. Run the focused unit spec, then the staging integration spec with the admitted
   pure-Simple runner.
2. Run `sha256sum --check scripts/os/simpleos_font_bundle_companion.sha256`.
3. Compile `scripts/os/make_os_disk.c` with warnings enabled.
4. Confirm `find doc/06_spec -name '*_spec.spl'` returns no files.

Any missing, empty, unpinned, hash-mismatched, duplicate, non-8.3 companion, or
directory-capacity mismatch is a failure. The manuals show the three primary
unit flows; static owner details stay folded in the integration source.
