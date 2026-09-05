# SmfManifest written but never verified on load

**Filed:** 2026-08-17
**Status:** PARTIALLY FIXED (source_hash verification landed; options/config check still open)
**Area:** compiler / cache consistency

## Claim audit vs `.claude/rules/commands.md`

| documented claim | status 2026-08-17 |
|---|---|
| `interface_digest_of` has zero callers | **HOLDS in `src/`** — `src/compiler/80.driver/cache/action_key.spl:199` is the only definition and the only `src/` occurrence besides two doc comments. It IS exercised by `test/01_unit/compiler/cache/action_key_spec.spl`, so "never computed" is true of the product but not of the test tree. |
| `DependencyEntry.needs_recompile` is one-hop and never called | **HOLDS**; line number moved to `driver_build/incremental.spl:280`. Other `needs_recompile` hits are unrelated symbols in `incremental.spl`, `incremental_builder.spl`, and the Rust seed. |
| `action_key.spl` / `cas_store.spl` not exported from `cache/__init__.spl` | **HOLDS** — `__init__.spl` exports only `cache_types`, `cache_validator`, `compile_options_hash`, `lazy_section`. |
| path `driver_build/cache/action_key.spl` | **CHANGED** — the cache package is `src/compiler/80.driver/cache/`, not under `driver_build/`. |
| `SmfManifestEntry` carries `source_hash`, no interface digest | **HOLDS**. |
| "`SmfManifest` is written but never verified on load" | **CHANGED, and understated.** A validator *is* called — but not on the manifest. |

## What was actually wrong

`driver_api_interpret.try_load_smf_cached` is the only consumer. It loaded
`build/smf/manifest.sdn`, found the row for the source, and used **only
`smf_path`** from it. Every other recorded field — `source_hash`, `backend`,
`opt_level`, `release`, `debug_info`, `gc_off`, `profile`, `allowed_families` —
was parsed by `parse_manifest_entry_line` and discarded. The only freshness
evidence was `validate_smf`, which checks the hash stored *inside* the .smf that
the possibly-stale manifest row pointed at.

Two consequences:

1. **The manifest row itself was unverified.** A row is trusted to name the
   right artifact, and the artifact then vouches for itself.
2. **The recorded build configuration is never compared.** The call passes
   `compile_options_hash_zero()`, and `validate_smf` skips its Level-3 options
   comparison entirely when the supplied hash is zero. An SMF compiled
   `--release` on the LLVM backend is executed unchanged for a plain interpret
   run.

Also fixed in passing: `var smf_entry = manifest.entries[0]` — an integer index
into a `Dict<text, SmfManifestEntry>`, evaluated unconditionally as a placeholder
before the real lookup was assigned over it.

## Why this is reachable, not theoretical

`rt_hash_text` returns 0 for every input on the JIT/native path (see
`rt_hash_text_returns_zero_under_jit_cache_freshness_vacuous_2026-08-17.md`),
which makes `validate_smf`'s source-hash comparison vacuously true. With the
manifest unverified and the artifact's self-check degenerate, **nothing at all
stood between a stale .smf and execution**.

## Fix landed

`smf_manifest_entry_matches_source(entry, source_text)` in
`src/compiler/80.driver/watcher/smf_manifest.spl` — fail-closed:

- `entry.source_hash == 0` (the sentinel both writers record when the source
  could not be read) is never trusted;
- empty/unreadable live source is never trusted;
- any mismatch rejects.

`try_load_smf_cached` now reads the live source and rejects the cache hit unless
the manifest row verifies, falling back to a full interpret.

Runnable check (verdict is the last stdout line, exit 0 = PASS):

```
bin/simple run scripts/check/check-smf-manifest-source-hash-verification.spl
```
Measured 2026-08-17: `PASS — 4 case(s) checked, 0 failed`.
Spec: `test/01_unit/compiler/cache/smf_manifest_source_hash_verification_spec.spl`.

## Still open

- The recorded build configuration (`backend`, `opt_level`, `release`,
  `debug_info`, `gc_off`, `profile`, `allowed_families`) is still never compared
  at load. Closing it means plumbing the requested `CompileOptions` into
  `try_load_smf_cached` and passing a real `CompileOptionsHash` to
  `validate_smf` instead of `compile_options_hash_zero()`.
- Writer/reader path mismatch: `driver_aot_pipeline.spl:166` records the
  manifest at `<native_build_cache_dir>/manifest.sdn`, while the reader always
  loads `SMF_MANIFEST_DEFAULT_PATH` = `build/smf/manifest.sdn`. Only the
  watcher lane's entries are ever seen.
- Dependency-aware / partial rebuild (`interface_digest_of`, `simple.sdn`
  traversal) remains out of scope and unimplemented.
