# cargo 1.100.0-nightly moved per-crate artifacts out of deps/ — seed tuple projection failed closed

**Status:** FIXED (projection is now layout-agnostic; Windows find-authority
walk still deps/-based, see Consequence 3)

**Found:** 2026-09-16 ~12:37 local, full bootstrap (`--full-bootstrap
--jobs=full`) on merged main (7d4cdddd41f), immediately after four successful
Cargo builds, at:

```
bootstrap_stage3_copy_seed_tuple: failed check 4
bootstrap_stage3_prepare_seed_generation: failed check 4
error: could not prepare immutable Rust authority generation
```

## Symptom

Every full bootstrap aborts in step 1 the moment the Rust seed needs a
rebuild. The four Cargo builds (seed, native-all, runtime-nolto,
compiler-backfill) all print `Finished`, then the immutable-authority
publication fails check 4: `$CARGO_TARGET_DIR/<triple>/bootstrap/deps` is
not a directory. `deps/` no longer exists AT ALL — no rlibs, no `.d` files,
no archive slot.

## Cause

The repo pins `channel = "nightly"` in `src/compiler_rust/rust-toolchain.toml`
— a FLOATING channel. On 2026-09-16 at 12:31:35 local, rustup refreshed the
host's `nightly-aarch64-unknown-linux-gnu` toolchain (cargo 1.100.0-nightly,
`7941be6fb 2026-09-11`). That cargo changed the per-crate artifact layout:
intermediate crate outputs (rlibs, rmetas, the runtime archive variants) moved
from `deps/` to `build/<crate>/<metadata>/out/`, and `deps/` is never
created. Verified on disk: 363 rlibs under
`target/<triple>/bootstrap/build/*/out/`, zero under any `deps/`; the hosted
runtime rlib at `build/spl_hosted_runtime/<meta>/out/`, the runtime
staticlib variants at `build/simple-runtime/<meta>/out/` plus the
last-build-wins copy at the profile root.

The previous authority generation on this host (built 2026-09-15 22:49 with
the older nightly) has the classic layout — this is purely a toolchain
layout change, not a repo change.

## Fix (this change)

`bootstrap_stage3_copy_seed_tuple` now discovers the hosted-runtime rlib in
BOTH layouts (`deps/libspl_hosted_runtime-*.rlib` and
`build/spl_hosted_runtime/*/out/libspl_hosted_runtime-*.rlib`, newest-wins
regardless of layout, non-symlink discipline unchanged) and falls back to
the profile-root `libsimple_runtime.a` when the `deps/` archive slot is
absent. A source-alias channel (`BOOTSTRAP_STAGE3_TUPLE_SOURCE_ALIASES`)
tells the O_NOFOLLOW perl projection where to READ each aliased member; the
FROZEN GENERATION layout is unchanged (`deps/<basename>` spellings), so
`bootstrap_stage3_verify_hosted_runtime_authority` and every downstream
receipt keep working unmodified.

## Consequences

1. Any host whose floating nightly refreshed to >= 2026-09-11 hit this on
   the next seed rebuild; CI images pinning a dated nightly did not.
2. `rust-toolchain.toml` still floats. A dated pin would prevent recurrence
   but is a release-policy decision, not made here.
3. The Windows find-authority walk (`bootstrap_stage3_hosted_find` over
   `<walk_root>/deps`) is still deps/-based; Windows lanes will need the
   same treatment when their toolchain floats.
