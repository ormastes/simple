# `std.hash` facade shadows the noalloc hash package and drops its API

- **Status:** OPEN
- **Severity:** Medium (latent — no in-tree caller today; breaks baremetal callers)
- **Found by:** adversarial review of `30697f688ed` ("make `use std.hash` actually export the Hash trait")

## What the commit did

`30697f688ed` added `src/lib/hash.spl` as a facade re-exporting the `Hash` trait
from `src/lib/nogc_sync_mut/src/hash.spl`. That part works: `use std.hash.{Hash}`
now resolves and `impl Hash for P` dispatches (verified empirically), and the
previously-inert `use std.hash.Hash` in `map.spl` is now live with no behavior
change (`test/shared/collections/map_spec.spl` 16/16).

## The defect

`src/std` is a symlink to `src/lib`, so the new `src/lib/hash.spl` now **wins**
the module path `std.hash`. The noalloc hash package documents that exact import
form as its intended entry point:

- `src/lib/nogc_async_mut_noalloc/hash/mod.spl:17-18`
- `src/lib/nogc_async_mut_noalloc/hash/__init__.spl:7-8`

Its API is no longer reachable through it:

```
use std.hash.{fnv1a_hash_i64}
  -> semantic: function `fnv1a_hash_i64` not found
  -> [use-warning] 'fnv1a_hash_i64' is named in `use std.hash.{...}` but module
     'src/std/hash.spl' does not provide it
```

Dropped symbols: `fnv1a_hash_bytes`, `fnv1a_hash_i64`, `crc32_byte`,
`crc32_bytes`.

No in-tree caller uses that form today, which is why it landed green — an
unresolved `use` is only a WARNING here, so a clean build proves nothing about
resolution. Submodule paths (`std.hash.adler32`, `std.hash.djb2`) still resolve
past the facade file and their specs pass (11/11, 4/4).

## Why this matters beyond the symbol list

This is the second facade re-export ambiguity in the same review window (the
first being `mailbox_actor.Mailbox`). A facade file placed at a package's own
module path silently shadows the package rather than merging with it, and the
only signal is a non-fatal warning at the call site.

## Fix

Add the four noalloc symbols to the `src/lib/hash.spl` re-export list, and add a
spec that imports both `Hash` and `fnv1a_hash_i64` from `std.hash` so the
shadowing cannot regress silently.
