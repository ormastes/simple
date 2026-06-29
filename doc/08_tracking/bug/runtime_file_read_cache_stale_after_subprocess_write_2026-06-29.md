# Runtime: file read cache returns stale content after out-of-process writes

**Status:** FIXED in seed source; pending seed rebuild + deploy to default `bin/simple`
**Found:** 2026-06-29 (noise sweep → simpleos_nvme_serial_check_spec)
**Area:** runtime / file IO (`rt_file_read_text`, `rt_file_mmap_len`)

## Symptom

A process that reads a file via `rt_file_read_text`, then the file is rewritten
by a **subprocess** it spawned, then reads it again — gets the **old** content.
`rt_file_mmap_len` returns a stale length the same way.

Surfaced in `test/01_unit/app/simpleos_nvme_serial_check_spec.spl` ("requires
serial identity to match the host preflight report when supplied"): the checker
subprocess wrote the correct result (`duplicate-field:serial`) to disk, but the
parent test process read back a stale `duplicate-field:model` from an earlier
checker run on the same output path — so the assertion failed even though the
on-disk file and the checker logic were both correct.

## Root cause

`src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs` keeps a one-slot
read cache (`ReadTextCache`) and an mmap-length cache (`MmapLenCache`). Each
stores a `FileStamp { len, modified }`, but the cache **lookups returned the
cached value on a path match alone and never compared the stamp**:

```rust
if cached.path == path_str {
    return cached.value;   // stale if the file changed on disk
}
```

The in-process write path calls `invalidate_file_caches`, but a subprocess
writing the file is invisible to the parent's cache, so the parent serves stale
content indefinitely.

## Fix

Validate the on-disk stamp (len + mtime) before trusting the cache in both
lookups:

```rust
if cached.path == path_str && file_stamp(Path::new(path_str)) == Some(cached.stamp) {
    return cached.value;
}
```

(`FileStamp` already derives `Copy, PartialEq, Eq`.) On a stamp mismatch the
code falls through to a fresh read and refreshes the cache. Cost: one extra
`stat()` per cached read — negligible vs. returning wrong data.

## Verification

Combined with the wrapper `ROOT_DIR` fix and the test `mkdir` fix,
`simpleos_nvme_serial_check_spec.spl` went from 19 failures to 1 (31/32). This
read-cache fix specifically cleared the `duplicate-field:serial` assertion that
was reading a stale prior `duplicate-field:model` result. `interpreter_bdd`
regression tests still pass.

**Residual (not this fix):** one assertion deep in the 40-step
"requires serial identity to match the host preflight report" mega-`it` still
reads stale content (a later `multi_preflight` check observes the prior
`duplicate` check's output). With unique per-step report paths the single-slot
read cache always misses, so the remaining staleness is NOT the path-cache —
it points to a deeper runtime string-value lifetime/aliasing interaction across
many sequential `val text = rt_file_read_text(p) ?? ""` reads in one function.
Tracked separately; needs runtime memory investigation, not a path-cache change.

## Deploy gate

Seed-side runtime fix; effective for `bin/simple` after a seed rebuild + deploy.
