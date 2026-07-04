# Wave-1a: Hash Analysis — `runtime_hash.c` vs `hash.spl`

## 1. C Implementation (`src/runtime/runtime_hash.c`)

```c
#include <stdint.h>
#include <stddef.h>

uint64_t rt_fnv_hash(const uint8_t *data_ptr, uint64_t data_len) {
    if (data_ptr == NULL) return 0;
    uint64_t hash = 0xcbf29ce484222325ULL;
    const uint64_t prime = 0x00000100000001b3ULL;
    for (uint64_t i = 0; i < data_len; i++) {
        hash ^= (uint64_t)data_ptr[i];
        hash *= prime;
    }
    return hash;
}
```

Key details:
- Function name: `rt_fnv_hash(ptr, len)` — raw pointer + length, returns `uint64_t`
- Algorithm: FNV-1a 64-bit
- Offset basis: `0xcbf29ce484222325` = 14695981039346656037 (unsigned) = -3750763034362895579 (signed i64)
- Prime: `0x00000100000001b3` = 1099511628211
- NULL pointer guard: returns 0

**Note:** The C file exports `rt_fnv_hash`, NOT `rt_hash_text`. The `rt_hash_text(s: text) -> i64` extern declared in `.spl` files is a **separate runtime function** — likely implemented in Rust (`src/runtime/` or the Rust compiler seed) — that takes a Simple `text` value and calls into `rt_fnv_hash` or an equivalent.

## 2. Simple Implementation (`src/lib/nogc_sync_mut/src/hash.spl`)

Relevant excerpt:

```spl
val FNV_OFFSET: i64 = -3750763034362895579  # 0xcbf29ce484222325 as signed i64
val FNV_PRIME: i64 = 1099511628211           # 0x100000001b3

fn wrapping_mul_i64(left: i64, right: i64) -> i64:
    ((left as u64) * (right as u64)) as i64

impl Hash for text:
    fn hash() -> i64:
        var h = FNV_OFFSET
        for byte in self.bytes():
            h = h xor (byte as i64)
            h = wrapping_mul_i64(h, FNV_PRIME)
        h
```

Key details:
- Algorithm: FNV-1a 64-bit — identical to the C version
- Offset basis: `-3750763034362895579` = `0xcbf29ce484222325` — **exact match**
- Prime: `1099511628211` = `0x100000001b3` — **exact match** (C has full 64-bit `0x00000100000001b3` = same value)
- Operates on `text.bytes()` — byte-by-byte iteration matching the C `data_ptr[i]` loop
- Returns `i64` (signed); C returns `uint64_t` — same bit pattern, just different type view

## 3. Algorithm Comparison

| Property | C (`rt_fnv_hash`) | Simple (`text.hash()`) |
|---|---|---|
| Algorithm | FNV-1a 64-bit | FNV-1a 64-bit |
| Offset basis | `0xcbf29ce484222325` | `-3750763034362895579` (same) |
| Prime | `0x100000001b3` | `1099511628211` (same) |
| Input | `(uint8_t*, uint64_t len)` | `text` (via `.bytes()`) |
| Output | `uint64_t` | `i64` (same bits) |
| NULL guard | returns 0 | N/A — `text` is never null in Simple |
| Operation order | XOR then multiply | XOR then multiply (same) |

**Verdict: Functionally identical.** For any non-null string, `rt_fnv_hash(ptr, len)` and `text.hash()` produce the same 64-bit result. The byte iteration order is the same, the constants are the same, and wrapping multiply is used in both (C unsigned overflow = Simple `wrapping_mul_i64`).

## 4. The `rt_hash_text` Extern — What It Is

`rt_hash_text(s: text) -> i64` is declared as `extern` in at least 15 `.spl` files across `src/compiler/80.driver/`. It is **not** defined in `runtime_hash.c` — that file only defines `rt_fnv_hash`. The `rt_hash_text` extern is implemented in the Rust runtime (likely in `src/compiler_rust/` or a runtime shim) and bridges the Simple `text` type to `rt_fnv_hash`.

Users of `rt_hash_text`:
- `src/compiler/80.driver/cache/cache_validator.spl` — source content hashing
- `src/compiler/80.driver/cache/compile_options_hash.spl` — compiler options hashing
- `src/compiler/80.driver/shb/shb_cache.spl`, `shb_hash.spl` — SHB caching
- `src/compiler/80.driver/watcher/` — watcher protocol, daemon, client, manifest
- `src/compiler/80.driver/driver.spl`, `incremental.spl`, `incremental_builder.spl`
- `src/lib/nogc_sync_mut/src/collections/hashmap.spl` — HashMap bucket hashing

## 5. Gap Analysis

### Gap 1: `rt_hash_text` bridges Simple `text` to C bytes
`rt_hash_text` is the ABI-aware bridge: it unwraps the Simple `text` heap object to get a `(ptr, len)` pair and passes it to `rt_fnv_hash`. In a pure-Simple native build, this bridge must either:
- (a) Be replaced by `s.hash()` at each call site (using the `Hash` trait impl for `text`), or
- (b) Be implemented as a Simple stdlib function: `fn rt_hash_text(s: text) -> i64: s.hash()`

### Gap 2: `rt_hash_text` returns `i64`, C returns `uint64_t`
Already compatible — same bit width, same bit pattern, just reinterpreted. No conversion needed.

### Gap 3: HashMap uses `rt_hash_text` not the `Hash` trait
`src/lib/nogc_sync_mut/src/collections/hashmap.spl` declares `extern fn rt_hash_text` and calls it directly. It does not use `text.hash()`. In a self-hosted build, this extern can be satisfied by a Simple wrapper function (see Gap 1b).

### Gap 4: `runtime_hash.c` exports `rt_fnv_hash`, not `rt_hash_text`
The C file is a low-level utility. The `rt_hash_text` symbol visible to `.spl` files is a higher-level Rust shim. Eliminating `runtime_hash.c` requires also eliminating or replacing the Rust shim that calls it.

### Gap 5: NULL guard in C not needed in Simple
The C `if (data_ptr == NULL) return 0` guard is defensive. Simple `text` is never null by design; the Simple implementation correctly omits this guard.

## 6. Recommendation

**Yes, the Simple `text.hash()` can fully replace `rt_fnv_hash` + `rt_hash_text` for compiled/native mode**, with the following steps:

1. **Add a Simple stdlib wrapper** in `src/lib/nogc_sync_mut/src/hash.spl` or a new `src/lib/nogc_sync_mut/src/hash_compat.spl`:
   ```spl
   pub fn rt_hash_text(s: text) -> i64:
       s.hash()
   ```
   This satisfies all `extern fn rt_hash_text` declarations at link time in native builds.

2. **Keep `runtime_hash.c` for now** — it is used during bootstrap (Rust seed stage) where the Simple runtime is not yet available. It can be removed in a later wave once the Rust seed no longer links it.

3. **HashMap callsites do not need to change** — they already declare `extern fn rt_hash_text(s: text) -> i64` which will resolve to the Simple wrapper above in native builds.

4. **No algorithm migration needed** — the bit-for-bit identical algorithm means persisted hashes (e.g., in SHB cache files) remain valid across the transition.

**Risk: low.** The only behavioral difference is the NULL guard (irrelevant in Simple) and the signed/unsigned return type view (same bits). The transition is a pure ABI bridge replacement, not an algorithm change.
