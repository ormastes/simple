# `crypto.types.text_to_bytes` silently loses to `base_encoding.text_to_bytes` — every digest wrong

- Date: 2026-08-21
- Status: **product mitigated** (crypto auth path); **compiler defect OPEN**
- Severity: high — produced *wrong cryptographic digests*, silently, with no error

## Symptom

`test/01_unit/lib/nogc_sync_mut/http/auth/digest_spec.spl` was RED with 5 of 14
failing: the RFC 7616 §3.9.1 KATs for **all three** algorithms (SHA-256, MD5,
SHA-512-256) plus both `verify` accept cases.

The spec's expected values were **independently confirmed correct** before any
product change, by recomputing them from the RFC's own parameters with
`openssl dgst`:

| alg | HA1 | HA2 | response |
|---|---|---|---|
| SHA-256 | `7987c64c…4794232` | `9a3fdae9…ad450b04` | `753927fa0e85d155564e2e272a28d1802ca10daf4496794697cf8db5856cb6c1` |
| MD5 | `3d78807defe7de2157e2b0b6573a855f` | `39aff3a2bab6126f332b942af96d3366` | `8ca523f5e9506fed4657c9700eebdbec` |

Both match the spec's assertions exactly, so the **spec was right and the
product was wrong**. (Note the spec's header comment quotes RFC 7616's *printed*
MD5 HA1 `12af87f3…`, which is a known erratum in the RFC text; the `response`
value the spec actually asserts is correct.)

## Root cause

`bin/simple test` runs the tree-walk interpreter. Under it,
`std.crypto.types.text_to_bytes` did **not** resolve to the definition
`digest.spl` imported.

There are two co-compiled public functions with this name and *different
element types*:

- `src/lib/common/crypto/types.spl:12` — `fn text_to_bytes(s: text) -> [i64]`
- `src/lib/common/base_encoding.spl:85` — `fn text_to_bytes(s: text) -> [u8]`
  (and a third in `src/lib/common/base_encoding/utilities.spl`)

The compiler *itself* diagnoses this, and even prescribes the fix:

```
warning: public function `text_to_bytes` has 2 co-compiled definitions with 2
differing signatures ((text)->[i64] vs (text)->[u8]); JIT call sites resolve by
exact arg-type match ..., falling back to the last definition when types are
ambiguous — a fallback hit may still dispatch to the wrong one. Rename the
conflicting helper(s) to a unique name.
[compiler_cross_module_private_symbol_collision]
```

The `[u8]` definition wins, so every crypto module receives a byte-array whose
`[i64]` contract is violated. It does not fail — it produces a **wrong digest**.

### Minimal reproducer

```
# tmpprobe/e.spl
use std.crypto.types.{text_to_bytes, bytes_to_hex}
use std.crypto.sha256.{sha256_bytes}
fn main():
    print("lit=" + bytes_to_hex(sha256_bytes([97, 98, 99])))   # literal [i64]
    print("t2b=" + bytes_to_hex(sha256_bytes(text_to_bytes("abc"))))
```

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run tmpprobe/e.spl
lit=ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad   # correct
t2b=000000d90000007000000080000000a9000000f8000000ff000000e000000045   # WRONG
```

The `000000XX` pattern is the tell: the digest words come out below 256, i.e.
the packing read a byte-array through the `[i64]` word path.

Confirmed **not** to be a defect in the hash algorithms or the bit helpers: a
byte-for-byte copy of `sha256_bytes` compiled into a probe file, and
`add_mod32` / `rotr32` / `shr32` / `>>` / `&` / `[0; n]` index-assign, all
produce correct values under the interpreter. Only the *name resolution*
differs.

## Product fix applied (this change)

Renamed the canonical `[i64]` implementations to collision-proof, tree-unique
names, and left thin delegators behind so all ~112 existing `crypto.types`
importers keep resolving:

- `src/lib/common/crypto/types.spl:12` — `fn crypto_text_to_bytes(s: text) -> [i64]`
- `src/lib/common/crypto/types.spl:52` — `fn crypto_bytes_to_text(bytes: [i64]) -> text`
- `src/lib/common/crypto/types.spl:38,41` — `text_to_bytes` / `bytes_to_text`
  retained as delegators (with the explanatory comment)
- `src/lib/crypto/types.spl:3-4`, `src/lib/crypto.spl:11` — new names re-exported

Switched the affected auth modules onto the unique names:

- `src/lib/nogc_sync_mut/http/auth/digest.spl:36,51,52,78`
- `src/lib/nogc_async_mut/http/auth/digest.spl:36,51,52,78`
- `src/lib/nogc_sync_mut/http/auth/basic.spl:16,172,180`
- `src/lib/nogc_async_mut/http/auth/basic.spl:16,172,180`

Verified: `Results: 14 total, 14 passed, 0 failed`.

## What is still OPEN

The mitigation fixes the HTTP auth path. It does **not** fix the underlying
defect, and the other ~110 `crypto.types` importers still call through the
ambiguous bare name — any of them that feeds `text_to_bytes` output into a hash
is producing wrong bytes today. Candidates to audit: `hmac.spl`,
`constant_time.spl`, `tls12_prf.spl`, `sha256_core.spl`,
`structural/resolve/resolve_core.spl`, `security/types.spl`,
`web_framework/password_reset.spl`.

**The real fix belongs in the compiler**: an explicit
`use std.crypto.types.{text_to_bytes}` must bind to *that module's* definition.
Resolving an explicitly-imported symbol by bare name across co-compiled modules
is wrong regardless of how the collision is spelled. Because `bin/simple` is
currently the Rust seed, that fix is a seed change and was deliberately not
attempted here (no seed builds). It lives in the interpreter's function-lookup
path alongside `compiler_cross_module_private_symbol_collision` in
`src/compiler_rust/compiler/src/`.

Until then, the collision-warning should arguably be an **error** for
differing-signature public collisions rather than a warning, since the failure
mode is silent wrong crypto rather than a crash.

## Class census (2026-08-21)

`scripts/check/check-duplicate-pub-fn-names.shs` (ratchet, baseline
`scripts/check/duplicate_pub_fn_baseline.txt`, `--selftest` fatal with 5
fixtures, ~5s) censuses every top-level `fn` / `pub fn` in `src/lib`,
`src/compiler`, `src/app` (vendored excluded) and reports names defined in >= 2
modules with >= 2 *distinct* signatures. Parameter names are stripped before
comparison — only types dispatch — and same-signature duplicates are counted
only under `--strict`.

**Measured baseline: `PASS — 78325 pub fn(s) checked, 1423 colliding name(s)
(baseline 1423)`.** (78327 after the utilities rename below; the *name* set is
unchanged, so the ratchet stays green.)

Ten riskiest (crypto / hash / encode / parse first), via `--top`:

| name | defs | sigs | signatures |
|---|---|---|---|
| `text_to_bytes` | 12 | 4 | `(text)->List<i64>` \| `(text)` \| `(text)->[u8]` \| `(text)->[i64]` |
| `_text_to_bytes` | 9 | 3 | `(text)->list` \| `(text)->[i64]` \| `(text)->[u8]` |
| `string_to_bytes` | 11 | 2 | `(text)->List` \| `(text)->[u8]` |
| `sha1` | 3 | 3 | `([i64])->[i64]` \| `(text)->List<i64>` \| `(text)->list` |
| `sha1_update` | 2 | 2 | `(Sha1Context,[i64])->Sha1Context` \| `((list,list,i64,i64),list)->(...)` |
| `sha1_finalize` / `sha1_final` | 2 | 2 | `(Sha1Context)->[i64]` \| `((list,list,i64,i64))->list` |
| `sha256` | 2 | 2 | `(data)` \| `(ByteSpan)->Digest` |
| `xor_bytes` | 4 | 2 | `(List,List)->List` \| `(i64,i64)->i64` |
| `pb_encode_varint` / `_fixed32` / `_fixed64` | 2 | 2 | `->[i64]` \| `->[u8]` |
| `read_bytes` | 6 | 5 | incl. `(text)->Result<[i64],IoError>` vs `(text)->[u8]` vs `(i64)->text` |
| `to_hex` | 5 | 3 | `(i32)->text` \| `(i64)->text` \| `(Color)->text` |

The whole SHA-1 family being split between an `[i64]`/`Sha1Context` and a
`list`-tuple implementation is the same shape as this bug and should be
audited next.

## The three browser specs are NOT this collision

`test/01_unit/lib/common/web/{browser_renderer_protocol,browser_session_http_status,browser_session_loading_history}_spec.spl`.
Only the first one's *subject* (`src/lib/common/web/browser_renderer_protocol.spl:3`)
imports `base_encoding.utilities.{bytes_to_text, text_to_bytes}`, and it uses
`text_to_bytes` only for `.len()` — a byte count that is identical whichever
variant wins. The collision IS live in that run (the log carries
``public function `text_to_bytes` has 3 co-compiled definitions``), so the
hypothesis was tested rather than assumed:

- before: `Results: 12 total, 9 passed, 3 failed`
- after switching the module onto the tree-unique
  `base_encoding_text_to_bytes` / `base_encoding_bytes_to_text`:
  `Results: 12 total, 9 passed, 3 failed` — **unchanged**

So those 3 failures are a different defect (frame/receipt round-trip), and the
other two specs' failures (`expected  to equal text/plain`, `expected
https://example.com/app to equal RedirectedModule`, `expected 24 to equal 25`)
never touch `text_to_bytes` at all. Their logs do show the *class* form of this
same defect class (`class Logger` / `class Pair` each with 2 co-compiled
definitions), which is worth its own record.

Kept anyway, as defect-class hardening, behaviour verified neutral:
`src/lib/common/base_encoding/utilities.spl` now defines
`base_encoding_text_to_bytes` / `base_encoding_bytes_to_text` with thin
delegators under the historical bare names. Re-verified green:
`base_encoding_facade_text_to_bytes_spec` 6/6,
`base_encoding_utf8_guard_spec` 5/5, `base32_rfc4648_kat_spec` 39/39.
No test file was edited, so the `test/unit` mirrors stay byte-identical.

## Compiler defect: where the warning could become fatal

This IS a compiler defect. The diagnostic already exists in the seed:

- `src/compiler_rust/compiler/src/pipeline/module_loader.rs:1687-1699` —
  the **differing-signature** warning quoted above ("Rename the conflicting
  helper(s) to a unique name"). This is the exact site to promote to a hard
  error under the `robust` / `critical` profiles: it is unconditional (no
  feature gate), it already has the full `entries` / `distinct` signature list
  in scope, and it fires precisely on the silent-wrong-value case.
- `src/compiler_rust/compiler/src/pipeline/module_loader.rs:1661-1675` — the
  **same-signature** sibling, gated off by default via
  `same_signature_diag_enabled()` (`:1543`), with an in-source comment stating
  it is "deliberately NOT promoted to an error here".
- `src/compiler_rust/compiler/src/pipeline/module_loader.rs:1727-1740` — the
  class/type form (`Logger`, `Pair` above).

Recommended shape: keep warn-by-default for `default`, deny at `:1687` for
`robust` and `critical`, since the failure mode is a wrong cryptographic digest
rather than a crash. **Not changed here** — `bin/simple` is the Rust seed and no
seed build was attempted (see the note above). The deeper fix remains that an
explicit `use std.crypto.types.{text_to_bytes}` must bind to *that module's*
definition regardless of collisions.

## RESOLVED (product surface) 2026-08-21 — `bytes_to_text` collision eliminated

The sibling half of the `text_to_bytes` collision. `bytes_to_text` had 8
co-compiled definitions across **3 distinct signatures** — `([u8])->text`,
`([i64])->text`, `(List<i64>)->text` and `([u8],i64,i64)->text` — and was
carried in `scripts/check/duplicate_pub_fn_baseline.txt`.

Every non-`[u8]` definition was renamed to a tree-unique name and every caller
switched to the unique name **directly, not via `X as bytes_to_text`**: an
import alias binds the *colliding* name locally and is hijacked exactly like a
bare call. That was proved, not assumed — the first pass used aliases and
`websocket_facade_spec` went RED (`ws_bytes_to_text` resolved to
`string_core`'s `[u8]` variant, dropping the out-of-range byte and returning
`""` instead of `"ABCD?"`). Dropping the aliases turned it green.

Renamed: `aes_bytes_to_text`, `cbor_bytes_to_text`, `codec_bytes_to_text`,
`ws_bytes_to_text`, `compression_bytes_to_text`, `gzip_stream_bytes_to_text`,
`zip_reader_bytes_to_text`. Remaining definitions all share `([u8])->text`.

Note that `websocket_facade_spec` was **passing by accident** before this
change: the collision made it call string_core's variant. A green spec is not
evidence that the intended function ran.

Gate verdicts (the 5 NEW names are another session's in-flight edits under
`src/lib/editor`, `src/compiler/35.semantics`, `src/compiler/99.loader`, not
this change):

- before: `FAIL — 78738 pub fn(s) checked, 1407 colliding name(s) (baseline 1402); NEW: activation_from_text _opt_bool _opt_int _opt_text _required_text`
- after rename: `... 1406 colliding ...; NEW: <same 5>; STALE (no longer colliding, baseline out of date): bytes_to_text`
- after lowering the baseline by exactly that one name (1402 -> 1401):
  `FAIL — 78738 pub fn(s) checked, 1406 colliding name(s) (baseline 1401); NEW: <same 5>` — STALE cleared.

Specs: new `test/01_unit/lib/nogc_sync_mut/websocket/ws_bytes_to_text_collision_spec.spl`
(2/2, mirrored). Neighbours green: `websocket_facade_spec` 1/1,
`cbor_bytes_to_text_invalid_guard_spec` 2/2, `codec_byte_text_guard_spec` 3/3,
`cbor_decode_spec` 94/94, `cbor_quick_spec` 4/4,
`zip_writer_negative_offset_guard_spec` 1/1, `upx_byte_text_spec` 1/1,
`gzip_validate_crc_isize_spec` 6/6, `http/auth/digest_spec` 14/14.

**Still open, unchanged:** the compiler-side fix (an explicit
`use std.crypto.types.{text_to_bytes}` must bind to *that module's*
definition), which is a Rust-seed change. **New, and worth its own attention:**
several modules still spell `use ....{crypto_bytes_to_text as bytes_to_text}`
(and the `base_encoding_*` equivalents). Those aliases re-bind a name that
other modules still define, which is the same hazard in a different spelling.
