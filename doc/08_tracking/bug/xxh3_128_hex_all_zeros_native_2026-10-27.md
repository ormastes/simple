# Native `_hex64` makes `xxh3_128_hex` return all zeros (2026-10-27)

**Status:** FIXED (workaround in _hex64; codegen bug open)
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

## Resolution (2026-10-27)
Bisected natively with stage2 (`C:/dev/p3new/stage2.exe`). Miscompiled construct:
`.to_i64()` called on a parenthesised u64 binary-op result evaluates to 0.
Variable u64 shifts, `[text]` literal indexing, text concatenation, and `v.to_i64()`
on a plain variable are all correct.

Minimal repro (native prints `t1=2 t2=0 t3=<v> t4=<v>`; expected `t2=2`):
```
fn t1(v: u64) -> i64:
    (v & 0xFu64) as i64        # 2 (ok)
fn t2(v: u64) -> i64:
    (v & 15u64).to_i64()       # 0 (WRONG)
# main: val v = 0x28241db6188879c2u64; print "{t1(v)} {t2(v)}"
```
Also seen: `v.to_i64()` directly on a `val v = 0x...u64` local in `main` inside string
interpolation segfaulted the binary (not isolated further).

Fix: `_hex64` in `src/lib/common/crypto/xxh3.spl` uses `as i64`. The `_hex64` in
`xxh3_dual.spl` already used `as i64` and was verified correct natively, so it is unchanged.
`xxh3_128_text` now returns "" (the existing failure sentinel; `digest_v1_new` rejects it)
when the fallback yields the all-zero digest. Native check: abc ->
06b05ab6733a618578af5f94892f3950, empty -> 99aa06d3014798d86001c324468d497f.
Open: fix the `.to_i64()`-on-binary-op codegen bug itself.
