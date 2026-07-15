# Bug: native-build incremental object cache key omits the compiler/seed version

**Status (2026-07-15):** source implemented; fresh executable cache proof was
not run in the source-only audit.

- **ID:** native_object_cache_key_omits_seed_version_2026-06-15
- **Severity:** P2 (silent: stale `.o` from an older compiler are reused after a
  codegen change, so the new codegen never reaches the link)
- **Area:** `pipeline/native_project/mod.rs` (`object_cache_key`) +
  `.simple/native_cache/<triple>/objects/`

## Symptom

After changing the codegen backend (e.g. adding `__module_init_*` emission to
the LLVM backend) and rebuilding the seed, `bin/simple os build
--scenario=rv64-base` reused cached `.o` files compiled by the *previous* seed.
Only files whose source changed were recompiled; the rest kept their old object
code, so the new codegen (module-init functions) was missing from most modules.
`SIMPLE_DEBUG_MODINIT=1` showed `generate_module_init` running for only 2 of ~30
modules — the rest were cache hits.

Workaround that unblocked: `rm -rf .simple/native_cache` forces a full
recompile.

## Root cause

`object_cache_key(source, is_entry, backend, no_mangle, module_prefix)` hashes
the *source* and build config but NOT the compiler/seed binary version. When the
seed's codegen changes but the source does not, the key is unchanged → stale hit.

## Fix options

- Mix a compiler build identity into the key: e.g. the seed binary's mtime/hash,
  or a `const CODEGEN_CACHE_EPOCH: u64` bumped on codegen-affecting changes, or
  `env!("CARGO_PKG_VERSION")` + a git short hash.
- Cheapest robust: hash the seed executable's own bytes (or its mtime) once and
  fold into every object key.

## Impact

Any future codegen change to the Rust seed silently no-ops on cached modules
until the cache is manually cleared — easy to mistake for "my change didn't
work."

## Resolution (2026-07-15)

The seed object-cache key now includes a cached fingerprint of the running
compiler executable. Source and build options may remain unchanged, but a
different compiler executable selects a different object key.
