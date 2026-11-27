# std.common.crypto.xxh3 and std.common.hash.xxh3 both export xxh3_64 et al. — name collision on dual import

Status: FIXED (commit included).

## Symptom
Importing both `std.common.crypto.xxh3` and `std.common.hash.xxh3` in the same file (directly or transitively) results in a name collision when both export `xxh3_64`, `xxh3_64_seeded`, `xxh3_128`, `xxh3_128_seeded`, and other public names. The interpreter fails with "already defined" or similar during resolution. Files like `src/lib/nogc_sync_mut/hash/xxh3_dual.spl` worked around this by importing with `as pure_*` aliases, which is fragile and breaks on future changes to either module.

## Cause
`std.common.crypto.xxh3` was the original, single provider of all xxh3 functions (64-bit kernel functions and 128-bit kernel functions returning `[u64]`). Later, `std.common.hash.xxh3` was added as a wrapper module that provides higher-level facades (struct-typed `Xxh3Hash128`, streaming state, public API). Both modules exported the same public function names without a module ownership distinction, violating the single-owner principle.

## Resolution
`std.common.hash.xxh3` is now the sole public owner of xxh3 functions. `std.common.crypto.xxh3` retains only internal kernel implementations (renamed with `_k_` prefix for clarity):
- `xxh3_64`, `xxh3_64_seeded`, `xxh3_64_with_secret` → `_k_xxh3_64`, `_k_xxh3_64_seeded`, `_k_xxh3_64_with_secret` (definition; used internally by hash module)
- `xxh3_128`, `xxh3_128_seeded`, `xxh3_128_with_secret`, `xxh3_128_hex` → `_k_xxh3_128`, `_k_xxh3_128_seeded`, `_k_xxh3_128_with_secret`, `_k_xxh3_128_hex` (definition; used internally by hash module)

`std.common.hash.xxh3` re-exports the public API (unchanged signatures):
- `pub fn xxh3_64(data: [u8]) -> u64` — calls `_core64`
- `pub fn xxh3_64_seeded(data: [u8], seed: u64) -> u64` — calls `_core64` conditionally
- `pub fn xxh3_64_with_secret(data: [u8], secret: [u8]) -> [u64]` — wraps `_k_xxh3_64_with_secret`
- `pub fn xxh3_128(data: [u8]) -> Xxh3Hash128` — wraps `_core128` with struct packing
- `pub fn xxh3_128_seeded(data: [u8], seed: u64) -> Xxh3Hash128` — wraps `_core128` with struct packing
- `pub fn xxh3_128_with_secret(data: [u8], secret: [u8]) -> [u64]` — wraps `_k_xxh3_128_with_secret`
- `pub fn xxh3_128_hex(data: [u8]) -> text` — wraps `_k_xxh3_128_hex`

All callers switch imports:
- Return-type `u64` (xxh3_64, xxh3_64_seeded) and `_with_secret`/`_hex` functions: import from `std.common.hash.xxh3`
- Return-type `[u64]` (xxh3_128, xxh3_128_seeded) in test/internal code only: import from `std.common.crypto.xxh3` with `_k_` prefix (or alias to plain names in tests for readability)
- Dual-run shadow (`xxh3_dual.spl`) removes `as pure_*` aliases and calls the plain names directly (no conflicts, since the file defines `xxh3_*_checked`, not `xxh3_*`)

## Files changed
- `src/lib/common/crypto/xxh3.spl`: Rename all public-facing functions to `_k_` prefix; keep bodies and internal kernels unchanged
- `src/lib/common/hash/xxh3.spl`: Add public wrappers for `xxh3_64_with_secret`, `xxh3_128_with_secret`, `xxh3_128_hex`; import `_k_` functions from crypto module
- `src/compiler/00.common/cache_contract/hash_algorithm_compute_v1.spl`: Switch import from `crypto.xxh3` to `hash.xxh3`
- `src/compiler/80.driver/driver_parse_shard_hash.spl`: Switch import from `crypto.xxh3` to `hash.xxh3`
- `src/lib/nogc_sync_mut/sffi/runtime.spl`: Switch import from `crypto.xxh3` to `hash.xxh3`
- `test/01_unit/compiler/driver/parse_shard_hash_xxh3_spec.spl`: Switch import from `crypto.xxh3` to `hash.xxh3`
- `test/01_unit/compiler/frontend/supplied_source_cache_key_spec.spl`: Switch import from `crypto.xxh3` to `hash.xxh3`
- `test/01_unit/lib/common/crypto/xxh3_kat_spec.spl`: Split import (hash for u64-return; crypto for `_k_` prefixed [u64]-return), with aliases to hide the `_k_` prefix
- `test/01_unit/lib/common/crypto/xxh3_reference_vectors_spec.spl`: Same as KAT spec
- `src/lib/nogc_sync_mut/hash/xxh3_dual.spl`: Remove `as pure_*` aliases and use plain names directly; no behavior change
