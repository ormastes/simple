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

## Residual (UNRESOLVED — runtime read returns a PRIOR file's content)

After the checker's own logic was corrected (see
`simpleos_nvme_checker_multiple_devices_ordering_2026-06-29.md`), one assertion
in the "requires serial identity…" mega-`it` still fails. Definitive evidence
collected this session:

- The `multi` step's checker child computes the right reason and **writes the
  correct report to disk**: `/tmp/…_multi.sdn` =
  `reason: …multiple-devices` / `preflight_identity_match: false` (verified by
  reading the file directly, and by in-checker logging `devcount=2
  reason=…multiple-devices`).
- Yet the **parent test process** `rt_file_read_text(multi_report)` returns the
  content of the *previously read* report (`…_match.sdn` =
  `reason: ready` / `preflight_identity_match: true`).
- The subprocess cache-invalidation above clears the read caches before that
  read, so it is a *fresh* read of a *correct* on-disk file — and it still
  returns the prior file's content. Adding the stamp check and the
  subprocess-invalidation did NOT resolve it.

So the parent's `rt_file_read_text` of path B returns the value previously read
for path A, even though B on disk is correct and the cache was cleared. The
mechanism is NOT explained by the single-slot path-keyed cache (path A ≠ path B
is a miss). It points to a runtime string-value / arena-reuse aliasing across
the ~40 sequential `val text = rt_file_read_text(p) ?? ""` reads in one
function. A minimal 2-read standalone repro could not reproduce it (the harness's
reads returned empty for unrelated reasons), so it needs the full sequence.
Needs runtime-memory-level investigation (value lifetime / arena, or the mmap
read path); deliberately NOT blind-fixed.

## Deploy gate

Seed-side runtime fix; effective for `bin/simple` after a seed rebuild + deploy.
