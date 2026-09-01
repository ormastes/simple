# `scripts/os/make_os_disk.c` did not compile or link on `origin/main` (2026-08-31)

**Status:** FIXED in the same change that filed this record.

## Symptom
`sh scripts/os/make_os_disk.shs 128 <img>` — the sanctioned SimpleOS FAT32 disk
builder, used (directly or transitively) by every SimpleOS disk lane — failed at
`cc`:

```
make_os_disk.c:165:38: error: invalid initializer          # read_bounded_public_file
make_os_disk.c:166:35: error: invalid initializer
make_os_disk.c:167:36: error: invalid initializer
make_os_disk.c:575:29: error: 'DIR_SIZE' undeclared
...then, after those:
make_os_disk.c:(.text.startup+0x4845): undefined reference to 'require_cluster_bytes'
```

## Root cause — three half-landed edits, all in the same class
A change added call sites without their definitions, and a rename slipped:

1. `read_bounded_public_file(path, max_bytes)` — called at `:165-167` for the
   three `SIMPLEOS_SIMPLEBOX_*` signed-media inputs. **Defined nowhere.**
2. `require_cluster_bytes(first, payload, message)` — called at `:439-443` to
   verify each signed-media member really landed in its cluster chain.
   **Defined nowhere** (compiled as an implicit decl, failed at link).
3. `DIR_SIZE` at `:575-576` — the constant is spelled `DIRECTORY_BYTES`
   everywhere else in the file; the two new locals also used `size_t` counts
   where `put_named_dir_entry` takes `int *`.

This is the same defect class as the Rust-seed incidents
(`origin_main_unbuildable_missing_half_1e40de916bb_2026-08-18.md`): a tree that
is structurally clean, correctly sized and forward-moving, and still complete
nonsense to a compiler. No pre-push guard covers it —
`check-c-runtime-compiles-push.shs` is scoped to `src/runtime/**` and never
looks at `scripts/os/`.

## Fix
- `DIR_SIZE` -> `DIRECTORY_BYTES`, `size_t` counts -> `int` (matching every
  sibling directory buffer).
- `read_bounded_public_file` restored in `make_os_disk_support.inc.c`: rejects
  a non-regular file, rejects a symlink (`lstat`), rejects anything over the
  bound outright rather than truncating, and returns an empty `struct bytes` on
  every rejection — which the caller turns into a hard `die()`.
- `require_cluster_bytes` restored in the same file: walks the identical
  contiguous chain `alloc_clusters()` wrote, `memcmp`s each cluster, and
  `die()`s on a zero cluster, an empty payload, an out-of-range offset, or any
  byte mismatch.

Both are reconstructions from their call sites, written fail-closed. If the
original intent was stricter, tighten them — but do not loosen them.

## Follow-up (NOT fixed here — separate defect, separate owner)
`scripts/os/make_os_disk.shs` additionally verifies the Google font companion
license manifest, and that verification is RED on this branch for reasons
unrelated to disk building:

```
assets/fonts/google-fonts/ofl/bungee/OFL.txt: FAILED
assets/fonts/google-fonts/ofl/pixelifysans/OFL.txt: FAILED
sha256sum: WARNING: 2 computed checksums did NOT match
```

Two license texts no longer match their recorded SHA-256. This is a SHIPPING
media provenance question (is the manifest stale, or did the licence files
drift?) and must be answered by whoever owns the font bundle — NOT by
regenerating the checksums to make a build pass. Filed here so it is not lost;
it still blocks the wrapper even though the C writer itself now builds.
