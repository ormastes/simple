# Native `_hex64` makes `xxh3_128_hex` return all zeros (2026-10-27)

**Status:** OPEN
**Severity:** P1. A native build that falls back to pure-Simple XXH3 gives every input the same cache key.
**Found by:** XXH3 lane native benchmark, using stage2 `C:/dev/p3new/stage2.exe` (sha `e4746b05…`) on Windows x64.

## Symptom
In a natively compiled program, `std.common.hash.xxh3.xxh3_128_hex(data)` returns
`00000000000000000000000000000000` for a 1024-byte input. The runtime
`rt_xxh3_128_text` returns `28241db6188879c215fd608b6d002700` for the same input.
The u64 halves themselves are correct natively: `.low` equals `xxh3_64`, and
`.high` = 2892469528611551682 = `0x28241db6188879c2` matches the runtime digest.
So the failure is in hex formatting, not in the hash. Under the interpreter
(`bin/simple.exe test`) the same function returns the correct hex; this is pinned
by `xxh3_kat_spec` and `hash_algorithm_registry_v1_spec`.

## Affected paths
- `src/lib/common/crypto/xxh3.spl` `_hex64` → `_k_xxh3_128_hex` → `std.common.hash.xxh3.xxh3_128_hex`.
- **The fallback inside `std.nogc_sync_mut.sffi.runtime.xxh3_128_text`**, which is taken when
  `rt_xxh3_128_text` does not return 32 hex characters. In a native build without the runtime symbol,
  every text hashes to the same all-zero digest. DigestV1 `xxh3-128` keys and
  in-process cache keys then collapse to one value. Lookups that verify hits, such as #4949,
  degrade to wrong-slow; any unverified consumer would be wrong-result.
- `src/lib/nogc_sync_mut/hash/xxh3_dual.spl` has its own `_hex64` of the same shape. Its
  mismatch logging would print zeros natively. The comparison itself uses
  `xxh3_128_text_runtime_only`, which has no fallback.

## Suspected cause (not yet bisected)
`_hex64` does `digits[((v >> (4u64 * i.to_u64())) & 0xFu64).to_i64()]` over a
`[text]` array literal and concatenates. Under native codegen, the variable-amount u64
shift, the `.to_i64()` of the masked nibble, or the indexing of a text-array literal
yields nibble 0 or "0" every time.

## Next steps
1. Reduce the repro to a minimal native program: print `_hex64(0x28241db6188879c2u64)`.
2. Fix the codegen bug, or as a stopgap rewrite `_hex64` without the text-array index.
3. Add a native-lane check that `xxh3_128_hex([0x61,0x62,0x63])` == `06b05ab6733a618578af5f94892f3950`.
