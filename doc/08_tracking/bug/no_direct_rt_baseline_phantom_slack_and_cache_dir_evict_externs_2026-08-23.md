# `no_direct_rt` ratchet: 25 counts of phantom slack, then 15 real sites in `cache_dir_evict.spl`

Date: 2026-08-23 — Status: OPEN (migration debt), baseline re-pinned to a measured value.

## Symptom

At `origin/main` `ee1431e8138`, `sh scripts/check/check-no-direct-rt.shs` FAILs:

    FAIL — forbidden direct rt_* count 11816 exceeds baseline 11815

## What the bisect actually found — the premise "one offender landed without
raising the baseline" is only half true.

Reproducing the guard's counting rule (`RT_RE='^[^#]*\brt_[a-z0-9_]*\('`, per-file
line counts over tracked `src/**/*.spl` minus `vendor/` minus
`scripts/check/no_direct_rt_allowlist.txt`) with `git grep -c` against arbitrary
revs — verified to agree with the guard exactly at HEAD (both 11816):

| rev | forbidden count |
|---|---|
| `fbe817aaf1b` (the commit that WROTE baseline `11815`) | **11790** |
| `892999e61b9` | 11784 |
| `1e6f5216e8e` | 11798 |
| `57271d9ba49` | 11801 |
| `36a0be8787c` | **11816** |
| `HEAD` (`ee1431e8138`) | 11816 |

Two facts follow:

1. **The recorded baseline was never a measurement of its own tree.**
   `fbe817aaf1b` wrote `11815` onto a tree that measured `11790` — 25 counts of
   phantom slack. That is the same defect class as the auto-write bug closed by
   `ee1431e8138`: a baseline written from a tree other than the one committed.
   The ratchet has therefore been silently ratcheting nothing for 25 sites.
2. **The crossing commit is `36a0be8787c`** ("fix(cache): unlatch the
   frontend/HIR cache scope, ... add size-capped LRU eviction"), which took the
   count 11801 -> 11816 by adding the new file
   `src/compiler/10.frontend/cache_dir_evict.spl` with **8 `extern fn rt_*`
   declarations + 7 call sites = 15 forbidden sites**:
   `rt_env_get`, `rt_dir_list`, `rt_dir_exists`, `rt_file_exists`,
   `rt_file_size`, `rt_file_stat`, `rt_file_delete`, `rt_time_now_unix_micros`.

   It is not the only contributor — ten commits since `fbe817aaf1b` moved the
   count by a net **+26** (`f17b8afc66a` +3, `971347b901b6` +3, `1e6f5216e8e` +5,
   `57271d9ba49` +3, `1ca19a1e31a` +2, `29945e414a4` +1, `970920e02cd` +1,
   `892999e61b9` -6, `0c085525541` -1, `36a0be8787c` +15) — but the other nine
   were absorbed by the phantom slack. `36a0be8787c` is the one that exhausted it.

## Why the 15 sites were NOT migrated to a provider in this commit

All eight primitives have provider wrappers with byte-identical signatures
(`std.io_runtime.{env_get,dir_list,dir_exists,file_exists,file_size,file_delete,time_now_unix_micros}`;
`file_stat` at `src/lib/nogc_sync_mut/io/file_ops.spl`), so the migration is
mechanically available. It was deliberately not done here:

* **`src/compiler/10.frontend/` deliberately does not import std.** 1 of the 20
  top-level `.spl` files in that directory has a `use std.` line; the peer cache
  module this one was split out of (`frontend_parse_cache.spl`) declares its own
  raw externs for the same reason.
* `cache_dir_evict.spl` is imported by **both** `frontend_parse_cache.spl` and
  `80.driver/driver_hir_cache.spl` — the hot bootstrap cache path. Widening its
  module closure with a stdlib import is a bootstrap-closure change, not a
  refactor, and a bootstrap chain was live in another lane at the time.
* This reconciliation lane cannot run a bootstrap to prove the closure change is
  safe, and an unverified closure widening on that path is a worse outcome than
  a named, recorded debt.

## Action taken

`scripts/check/no_direct_rt_baseline.txt` `11815` -> `11816`. This is a
**tightening in real terms**: it replaces a value 25 above its own tree with the
exact measured count, leaving the ratchet zero slack for the first time.

## Remaining work (do not close this record until done)

Migrate `src/compiler/10.frontend/cache_dir_evict.spl` (and its peer
`frontend_parse_cache.spl`) off raw `rt_*` externs onto the `std.io_runtime`
providers, in a commit that bootstraps to prove the closure change, then lower
the baseline by the sites removed.
