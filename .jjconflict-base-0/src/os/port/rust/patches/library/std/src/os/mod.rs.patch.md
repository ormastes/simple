# `library/std/src/os/mod.rs` — expose `std::os::simpleos`

This file is the public entry point for `std::os::<platform>` modules.
Upstream lists every supported OS alphabetically with a matching
`#[cfg(target_os = "...")]` guard.

Wave 3 did **not** touch this file. The new `library/std/src/os/simpleos/`
subtree (written in the same PR as this patch note) needs a one-line
addition here so `use std::os::simpleos::ffi::OsStrExt` resolves when
building for `*-unknown-simpleos`.

## Insertion point

Alphabetical order among existing guarded `pub mod` lines. Insert
**after `redox`** and **before `solaris`** (note: `solid_asp3` is
handled under `pal`, not here).

## Context anchors (before edit)

```rust
#[cfg(target_os = "redox")]
pub mod redox;
#[cfg(target_os = "solaris")]
pub mod solaris;
```

## After edit

```rust
#[cfg(target_os = "redox")]
pub mod redox;
#[cfg(target_os = "simpleos")]
pub mod simpleos;
#[cfg(target_os = "solaris")]
pub mod solaris;
```

## Notes

- No `doc(cfg(...))` attribute is needed — upstream does not gate any of
  the sibling entries that way and `rustdoc` builds host docs only.
- This exposure is independent of the `sys/pal` dispatch (see
  `library/std/src/sys/pal/mod.rs.patch.md`). Both edits are required.

## Validation

```bash
grep -n 'target_os = "simpleos"' library/std/src/os/mod.rs
# expect exactly one hit
```
