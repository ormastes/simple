# SimpleOS Font Asset Staging Specification

> Static integration contract for packaging all selected SimpleOS fonts through
> every Simple image builder and loading exact bytes under canonical identities.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 2 | 2 | 0 | 0 |

## Scenario

### SimpleOS pinned font asset staging

The selected SimpleOS candidate is Noto Sans Mono at the canonical repository
path, exactly 1,708,408 bytes, with SHA-256
`2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`.

Installer, initramfs, and legacy pure-Simple FAT32 construction iterate and
validate all 16 selected candidates, then store them under readable
registry-owned VFAT long names in `/SYS/FONTS`, with unique 8.3 compatibility
aliases. The guest uses each path only as a byte source and registers it under
the canonical registry identity. Pure-Simple FAT32 readers
use a bounded 32 MiB ceiling, large enough for the largest pinned
25,125,512-byte candidate; the C compatibility reader remains bounded at 4 MiB.
The pure-Simple disk writer emits checksummed ASCII VFAT slots, collision-safe
short aliases, and multi-cluster directory chains; the shared reader resolves
the long path first and preserves the raw short-name reader as boot fallback.
Before the canonical WM DrawIR frame, the desktop enables registered-only font
resolution and registers the exact VFS bytes; it has no private post-frame text draw.
The Simple Browser independently iterates the same 16-candidate registry, reads
each readable long path with its short alias as the only fallback, registers
bytes under the canonical repository identity, and refuses to render when the
registered count differs from the selected catalog count.

Every Simple builder validates the exact returned byte array before staging.
The still-live C compatibility wrapper mirrors the 16 readable VFAT names and
short aliases only after validating every pinned length and hash with
`sha256sum` or `shasum`; direct C
invocation fails when any required asset is absent. The canonical catalog and
guest mapping remain owned by pure Simple. These are source and packaging
assertions, not retained QEMU pixel evidence.

## Executable source

`test/02_integration/os/port/simpleos_font_asset_staging_spec.spl`
