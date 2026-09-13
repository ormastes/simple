# Bug: native-build incremental object cache key omits the compiler/seed version

## Closed 2026-09-13 — already fixed: the object cache key folds the compiler fingerprint
- **measured** — in `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs`,
  `fn compiler_fingerprint()` is defined at `:1494` and
  `compiler_fingerprint().hash(&mut hasher)` appears inside `object_cache_key` (`:1589`,
  hash call at `:1607`), plus a second fold at `:1547`.
- **inferred** — `compiler_fingerprint` hashes the running `current_exe`'s bytes, so a
  rebuilt seed yields a different key and cannot reuse a stale `.o`. `.claude/rules/commands.md`
  documents the same mechanism plus a per-lane cache scope layered on top. Not re-executed
  against a real seed rebuild.

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
