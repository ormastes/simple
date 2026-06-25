# Wave-1b: Base64 Analysis — C Runtime vs Simple Library

## C Runtime Implementation (`src/runtime/runtime_base64.c`, 80 LOC)

### Function Signatures

```c
int64_t __c_rt_base64_encode(const uint8_t *input, uint64_t input_len,
                              uint8_t *output, uint64_t output_cap);
int64_t __c_rt_base64_decode(const uint8_t *input, uint64_t input_len,
                              uint8_t *output, uint64_t output_cap);
```

Both return the number of bytes written on success, or `-1` on error (null input, output buffer too small).

### Algorithm

- **Encode**: Standard RFC 4648 base64. Table `A–Z a–z 0–9 + /`. Processes 3-byte chunks into 4 chars. Pads with `=` for 1- or 2-byte remainder. Output length = `ceil(input_len/3) * 4`.
- **Decode**: Skips whitespace (`\s \t \n \r`). Ignores invalid chars (silent skip). Handles `=` padding. Writes 1–3 bytes per 4-char chunk depending on pad count. Buffer-overflow guarded.

### Low-level ABI

These are C functions called via the Rust runtime linker. No Simple `extern fn` declarations expose them directly. They are internal to `runtime_base64.c` only.

---

## Related Runtime C Functions (in `src/runtime/runtime.c`)

Two additional base64url functions are defined in `runtime.c`:

```c
const char* rt_base64url_encode(const char* input, int64_t len);
const char* rt_base64url_decode(const char* input);
```

These use `+` → `-` and `/` → `_` substitution with padding stripped (RFC 4648 §5). They return heap-allocated `char*` strings managed by the runtime.

---

## Simple Library (`src/lib/common/base64/`)

### Files Present

```
decode.smf   encode.smf   mod.smf   types.smf
utilities.smf   validation.smf   variants.smf
```

**All files are pre-compiled `.smf` binaries — no `.spl` source is present in the repository.**

The `strings` output of `mod.smf` only shows `code` and `main`, confirming it is a compiled artifact without embedded source symbols.

### Callers of the Simple Base64 Library

31 files import `use std.base64` or equivalent across:
- `src/lib/nogc_sync_mut/` — oauth, http/auth, tls, terminal, web_framework, oidc
- `src/lib/gc_async_mut/` — oauth, http/auth, web_framework, websocket
- `src/lib/nogc_async_mut/` — oauth, http/auth, web_framework, websocket
- `src/app/itf/`, `src/os/crypto/`, `src/os/apps/shell/`
- `src/compiler_rust/lib/std/src/host/common/net/http.spl`

The Simple base64 library is **widely used** across the codebase.

---

## Direct `extern fn` Callers of C Base64

Only 2 files call C base64 functions via `extern fn`:

| File | Extern |
|---|---|
| `src/app/ui.web/ws_handler.spl` | `rt_sha1_finish_base64(handle: i64) -> text` (SHA-1 + base64 combo, not pure base64) |
| `src/lib/nogc_sync_mut/oidc/id_token.spl` | `rt_base64url_decode(encoded: text) -> text` |

Neither file calls `__c_rt_base64_encode` or `__c_rt_base64_decode` directly.

---

## Compatibility Assessment

| Dimension | C Runtime | Simple Library |
|---|---|---|
| Alphabet | Standard `A–Za–z0–9+/` | Unknown (SMF only) |
| URL-safe variant | `rt_base64url_encode/decode` in `runtime.c` | `base64url_encode` in `oauth/utilities.spl` (mock — does char substitution only, no real encode) |
| API style | Raw byte buffer + length | Unknown (SMF), but callers use `text` return types |
| Padding | `=` pad on encode, tolerates pad on decode | Unknown |
| Whitespace skip on decode | Yes | Unknown |

The Simple library's source was lost (only SMF artifacts remain). The `oauth/utilities.spl` `base64url_encode` is a **stub** that only does char substitution (`+`→`-`, `/`→`_`, strip `=`) on an already-encoded string — it does not perform real base64 encoding.

---

## Gap Analysis

1. **`__c_rt_base64_encode` / `__c_rt_base64_decode`**: Defined in C but not exposed to Simple via any `extern fn`. They appear to be internal runtime helpers. No Simple code calls them directly. **No migration blocker here.**

2. **`rt_base64url_decode`** (`runtime.c`): Called from `oidc/id_token.spl` via `extern fn`. This is a proper URL-safe base64 decode. The Simple library has no verified equivalent; `oauth/utilities.spl`'s `base64url_encode` is a mock.

3. **`rt_sha1_finish_base64`**: Part of SHA-1 + base64 pipeline in `ws_handler.spl`. This is a composite function (SHA-1 finalization + base64 encode). Separate from pure base64.

4. **Simple library source missing**: The `.smf`-only state means the Simple base64 library cannot be audited, extended, or verified for algorithm correctness without decompilation or regeneration from source.

---

## Recommendation

### Migration Path

1. **`__c_rt_base64_encode` / `__c_rt_base64_decode`** — These C functions are not called from Simple. They may be used internally by other C runtime functions (e.g., `rt_sha1_finish_base64`). **Do not migrate these independently.** Audit `runtime.c` and `runtime_crypto.c` for internal callers first.

2. **`rt_base64url_decode`** (used by `oidc/id_token.spl`) — Implement a pure Simple `base64url_decode(encoded: text) -> text` function in `src/lib/common/base64/` (or `src/lib/nogc_sync_mut/crypto/`). Algorithm: replace `-`→`+`, `_`→`/`, re-pad to 4-char boundary, then standard base64 decode. Replace the `extern fn` declaration in `id_token.spl` with a `use` import.

3. **`oauth/utilities.spl` mock** — The `base64url_encode` stub is incorrect for production. It must be replaced with a real implementation that base64-encodes the raw bytes first, then applies URL-safe substitution. This is a pre-existing bug independent of the Wave-1b migration.

4. **Simple library source recovery** — Before Wave-1b can be considered complete, the `.spl` source for `src/lib/common/base64/` must be recovered or rewritten. The `.smf` files are not portable across compiler versions. Rewrite from scratch using the C algorithm as reference (standard RFC 4648, same table).

### Priority Order

| Priority | Action |
|---|---|
| High | Recover/rewrite `src/lib/common/base64/*.spl` source |
| High | Implement `base64url_decode` in Simple; replace `extern fn` in `oidc/id_token.spl` |
| Medium | Fix `oauth/utilities.spl` `base64url_encode` mock |
| Low | Audit `runtime.c` internal use of `__c_rt_base64_*`; defer removal until all callers confirmed |
