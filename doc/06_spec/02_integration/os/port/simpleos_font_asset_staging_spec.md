# SimpleOS Font Asset Staging Specification

> Static integration contract for packaging the selected SimpleOS font/legal
> bundle through every image builder and loading exact font bytes under
> canonical identities.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 2 | 2 | 0 | 0 |

## Scenario

### SimpleOS pinned font asset staging

The selected SimpleOS candidate is Noto Sans Mono at the canonical repository
path, exactly 1,708,408 bytes, with SHA-256
`2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`.

One OS-owned projection maps exactly 53 files: all 50 pinned Google Fonts files
(16 TTFs, 16 `METADATA.pb`, 16 adjacent licenses, Roboto Slab copyright, and
`CORPUS.sdn`), the CLDR license, root `LICENSE`, and
`THIRD_PARTY_NOTICES.md`. The six CLDR XML/source/ranking inputs remain
build-time-only. Installer, initramfs, and legacy pure-Simple FAT32 construction
iterate this projection. The 16 TTFs retain their readable registry-owned VFAT
long names and unique 8.3 compatibility aliases; companions use collision-free
8.3 siblings in `/SYS/FONTS`. The guest uses TTF paths only as byte sources and
registers them under canonical identities. Pure-Simple and live C FAT32 readers
use a bounded 32 MiB ceiling, leaving 8,428,920 bytes above the largest pinned
25,125,512-byte candidate.
The pure-Simple disk writer emits checksummed ASCII VFAT slots, collision-safe
short aliases, and multi-cluster directory chains; the shared reader resolves
the long path first and preserves the raw short-name reader as boot fallback.
One shared desktop bootstrap enables registered-only font resolution, reads the
default face from its registry-owned long VFS path and then its 8.3 alias, and
registers the exact bytes under the canonical identity. The shared VFS reader
attempts the pure NVMe/FAT32 boot path before requiring a mounted VFS, so early
desktop font bootstrap can read validated media without weakening later mounted
filesystem checks. The
x86_64 and AArch64 canonical entries call it before creating Engine2D; neither
owns a private font loader or post-frame text draw. AArch64 first resets and
mounts the existing VirtIO-BLK FAT32 initializer. Its canonical desktop QEMU
targets attach the existing ARM filesystem image arguments, and the scenario
media gate builds that image before launch. Existing ARM images are accepted
only when `mtype` plus `sha256sum`/`shasum` prove `/SYS/FONTS/NOTOSANS` is
exactly 1,708,408 bytes with the pinned SHA-256; hosts without those tools fail
closed instead of trusting image manifest text. Successful registration
selects the VFS face; only failed mount or validation selects bitmap fallback.
The ARM initializer clears VFS state both before probing and after a failed
post-mount executable probe, so a rejected image cannot remain marked ready.
RV64 is intentionally unchanged: its current driver path is ARM-only and its
64 KiB runtime heap cannot support this vector-font bootstrap, so the existing
bitmap lane makes no vector-font claim.
The Simple Browser independently iterates the same 16-candidate registry, reads
each readable long path with its short alias as the only fallback, registers
bytes under the canonical repository identity, and refuses to render when the
registered count differs from the selected catalog count.

Every Simple builder validates the exact returned byte array before staging.
The still-live C compatibility wrapper mirrors the same 53 files: its shell
preflight validates all 16 TTF hashes and a 35-entry companion checksum
manifest through `sha256sum` or `shasum`; root notices remain nonempty
transport-owned inputs. Its `/SYS/FONTS` directory uses 91 of 128 available
entries, including TTF LFN slots. `SIMPLEOS_FONT_ASSET` may relocate only the
exact hash-validated Noto Sans Mono TTF bytes; metadata and license reads remain
anchored to the canonical pinned repository directory, so altered override
siblings cannot enter the image. The shell rejects stale pinned bytes and the C
writer rejects missing or empty required inputs.

Each architecture's live bridge grows one static path-read buffer from 4 MiB to
32 MiB: a 28 MiB `.bss` increase in the selected kernel image, not 28 MiB per
font and not both architectures in one image. This fits the normal 512 MiB x86
guest budget and leaves the maximum face below the buffer cap; retained x86/ARM
guest boot evidence remains pending. The canonical catalog and guest mapping
remain owned by pure Simple. These are source and packaging assertions, not
retained QEMU pixel evidence.

## Executable source

`test/02_integration/os/port/simpleos_font_asset_staging_spec.spl`
