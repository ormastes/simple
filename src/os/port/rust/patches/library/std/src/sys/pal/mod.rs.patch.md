# `library/std/src/sys/pal/mod.rs` — SimpleOS dispatch arm

This file selects the platform-abstraction-layer (PAL) backend based on
`target_os`. The existing file uses a `cfg_if!` chain that dispatches to
one of the per-OS modules (`unix`, `windows`, `hermit`, `wasi`, `redox`,
`solid_asp3`, `sgx`, `teeos`, `uefi`, `unsupported`, …).

Wave 3 landed the new `sys/pal/simpleos/` tree. This patch adds the arm
that actually picks it up when building for `*-unknown-simpleos`.

## Insertion point

Upstream (as of nightly ≥ 1.82) keeps the arms **alphabetically** inside
the `cfg_if::cfg_if! { … }` block. Insert the SimpleOS arm **after the
`redox` arm and before the `solid_asp3` arm**.

## Context anchors (before edit)

```rust
    } else if #[cfg(target_os = "redox")] {
        mod redox;
        pub use self::redox::*;
    } else if #[cfg(target_os = "solid_asp3")] {
        mod solid;
        pub use self::solid::*;
```

## After edit

```rust
    } else if #[cfg(target_os = "redox")] {
        mod redox;
        pub use self::redox::*;
    } else if #[cfg(target_os = "simpleos")] {
        mod simpleos;
        pub use self::simpleos::*;
    } else if #[cfg(target_os = "solid_asp3")] {
        mod solid;
        pub use self::solid::*;
```

## Notes

- Keep the `mod simpleos;` / `pub use self::simpleos::*;` form so the
  submodule tree laid down by Wave 3 is picked up automatically.
- Do **not** gate on `#[cfg(any(target_os = "simpleos", …))]`; SimpleOS
  does not share a PAL with any other OS today. If that changes (for
  example, a hypothetical shared-Unix-ish arm), refactor later.
- `std::sys::os_str`, `std::sys::path`, and other non-PAL dispatch files
  do **not** need a SimpleOS arm — they fall through to the generic
  UTF-8 implementation already used by `hermit`/`wasi`.

## Validation

```bash
grep -nE 'target_os = "simpleos"' library/std/src/sys/pal/mod.rs
# expect exactly two hits — the `cfg` guard and its matching `cfg`
```
