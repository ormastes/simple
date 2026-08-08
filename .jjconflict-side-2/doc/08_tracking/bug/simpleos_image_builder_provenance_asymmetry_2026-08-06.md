# Install-image provenance guards disagree — the Simple layer was fail-open

- **ID:** simpleos-image-builder-provenance-asymmetry-2026-08-06
- **Status:** FIXED (2026-08-06)
- **Severity:** MEDIUM — a seed-built payload could be staged into an install
  image rootfs; only the shell layer stopped it reaching the FAT image.
- **Owner path:** `src/os/installer/image_builder.spl`

## What happened

Two guards protect the SimpleOS install image against embedding a payload built
by the **Rust bootstrap seed** rather than the self-hosted compiler. They did
not agree:

| layer | function | checks |
|---|---|---|
| shell | `validate_simple_payload_provenance()` — `scripts/os/make_os_disk.shs:52` | stamp freshness (`-nt`), `target=`, `entry=`, `entry_closure=`, `backend` ∈ {llvm, cranelift}, and **rejects `compiler` matching `*compiler_rust*` or `*simple_seed*`** |
| Simple | `_validate_simple_binary()` — `src/os/installer/image_builder.spl:886` (call site `:218`) | `target=`, `entry=`, `entry_closure=`, ELF magic/class/machine — **and nothing about `compiler=`, `backend=`, or stamp freshness** |

So the Simple staging layer **embedded a seed-built payload into the rootfs
tree**, and only the later shell step refused to build the FAT32 image around
it. The weaker guard ran first and passed.

## How it surfaced (the guard working is the good news)

Lane S2 ran `sh scripts/os/build_simpleos_install_image.shs disk --arch=x86_64`
against the freshly-linked `bin/release/x86_64-unknown-simpleos/simple`, which
is currently built by the Rust seed as a deliberate route-around for
`deployed_selfhost_env_set_miscompile_segv_2026-07-14.md`. Result:

```
invalid SimpleOS Simple payload build stamp compiler: bin/release/x86_64-unknown-simpleos/simple.build_stamp
Error: FAT32 disk generation failed; refusing non-bootable descriptor fallback
```

That is the anti-seed contract **firing correctly on its first real adversarial
input** — the right outcome. The defect is only that the Simple layer had
already staged all 12 role files (each hashing exactly to the seed-built
artifact) before the shell layer objected.

## Fix

Mirror the shell rule in `_validate_simple_binary`: reject a stamp whose
`compiler` mentions `compiler_rust` or `simple_seed`, and require
`backend=llvm` or `backend=cranelift`. Both layers now fail closed on the same
input, and the comment points at the shell function so the two stay in sync.

## Consequence to respect

The current payload is seed-built, so it is **STAGING evidence only** and now
correctly cannot be turned into an install image by either layer. Getting a
legitimate image needs a self-hosted target build — which is itself blocked by
the deployed-self-hosted `native-build` SEGV. That dependency chain is real and
should not be worked around by hand-writing a build stamp; Lane S2 was offered
that shortcut and correctly refused it.

## Related, found in the same pass

- The staged `.smf` role files are raw ELF with no trailer, while
  `make_os_disk.c:460` appends a 128-byte `SMF` trailer. Whether the guest
  loader accepts a bare ELF at a `.smf` path is untested — that belongs to the
  SMF-loader lane.
- FAT32 subdirectory creation for the image is done **host-side** by
  `scripts/os/make_os_disk.c` (`alloc_directory`, `put_named_dir_entry`), so the
  absent kernel FAT32 *write* path does not block the seven-path contract.
