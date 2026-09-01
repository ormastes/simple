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

## Hardening also applied

`rt_process_run` / `rt_process_run_timeout` / `rt_process_run_with_limits` now
call `invalidate_all_read_caches()` on entry. A spawned subprocess can rewrite
any file without going through this process's write path, and a same-length
rewrite landing in the same mtime tick could still satisfy the stamp check;
clearing the single-slot read caches around a subprocess removes that window.
Negligible cost vs. a process spawn.

## Residual (UNRESOLVED — ruled OUT as the read cache)

One assertion deep in the "requires serial identity to match the host preflight
report" mega-`it` still reads stale content (a later `multi_preflight` check
observes the prior `duplicate` check's `duplicate-field:model` output).
**Adding the subprocess cache invalidation above did NOT change it** — every
nvme read is preceded by a cache-clearing subprocess, so the read cache is now
effectively bypassed for this test, yet the symptom persists. So this is NOT the
file read cache. Evidence remaining unexplained: the on-disk output file is
correct (`:serial`), and the checker on the exact dumped inputs reports `:serial`
standalone, yet the in-test parent read returns `:model`. This points to a
deeper runtime string-value lifetime/aliasing or arena-reuse issue across the
~40 sequential `val text = rt_file_read_text(p) ?? ""` reads in one function.
Needs runtime memory investigation; tracked, not yet root-caused.

## Deploy gate

Seed-side runtime fix; effective for `bin/simple` after a seed rebuild + deploy.
