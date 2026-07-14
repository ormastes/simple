# SimpleOS Font Asset Staging Specification

> Static integration contract for packaging the pinned SimpleOS font through
> every image builder and loading its bytes under the canonical font identity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 2 | 2 | 0 | 0 |

## Scenario

### SimpleOS pinned font asset staging

The selected SimpleOS candidate is Noto Sans Mono at the canonical repository
path, exactly 1,708,408 bytes, with SHA-256
`2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`.

Installer, initramfs, legacy bake, and direct FAT32 construction all stage that
candidate. The direct builder uses `/SYS/FONTS/NOTOSANS.TTF`; the guest may use
that 8.3-compatible path as a byte source but calls `load_font_bytes` with the
canonical registry path. Both VFS implementations read through the existing
4 MiB ceiling, so the selected payload is complete rather than truncated.

The shell wrapper validates exact length and SHA-256 with `sha256sum` or
`shasum`; direct C invocation fails when the asset is absent. These are static
source and packaging assertions. They do not promote SimpleOS pixel evidence,
which still requires the retained QEMU framebuffer oracle.

## Executable source

`test/02_integration/os/port/simpleos_font_asset_staging_spec.spl`
