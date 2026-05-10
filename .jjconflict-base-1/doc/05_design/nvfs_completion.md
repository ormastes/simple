# NVFS Completion Design

Feature set: remaining unchecked NVFS tracker criteria.

## Design

MountTable tests now use real `Path`, `MountOptions`, and `RamFsDriver`
objects, and assert that `/data/foo/bar.txt` resolves to `/foo/bar.txt`.

Compression uses `[u32 decompressed_len | repeated (run_len, byte)]` RLE frames
for compressible fixtures and falls back to raw bytes when the frame is not at
least 10% smaller. SLO helper functions expose deterministic acceptance values
for the in-repo codec model.

Dedup exposes DEDUP tree id 12, a 56-byte entry encoding contract, 256 MB
default cache configuration, module-level stats, encrypted DHK-keyed hashing,
and a refcount consistency check for `nvfs check --dedup`.

The spostgre integration test now writes encoded WAL bytes through a
MountTable-resolved RamFs path under `/db/wal/segment0`.
