# Untyped `list` function-parameter census — classification and fix order (2026-07-29)

## Background

Passes 7 and 8 root-caused and fixed three independent default-engine
(JIT/native codegen) miscompile triggers for the same `<<3` tag-box family
in `base58.spl`, the last one being **any function parameter typed as the
untyped `list` type corrupts bracket-index/`.get()` reads of its argument
inside the callee** — regardless of whether the caller passes a typed
array or a genuine untyped `list`. That fix caught a real, previously
undetected bug: `base58_encode([32])` silently returned `""` instead of
`"Z"`, and the repo's own pre-existing canonical Bitcoin-wiki P2PKH test
vector encoded to a **wrong address** under the default engine while
showing green under `bin/simple test` (which forces interpret mode and
therefore never exercises the default engine this bug lives in).

This is a fail-open surface: every untyped `: list` parameter with an
indexed read inside is a candidate for silent, engine-dependent
corruption that the standard test lane cannot see.

## Census methodology

```
grep -rlE ':\s*list\s*[,)]' src/ --include='*.spl' | grep -v 'compiler_rust/vendor'
```

Independently re-run this pass (not trusting the coordinator's count
without reproducing it): **148 files, 1257 sites** (coordinator's figures
of 149/1259 are within normal noise of a live repo — the tip moved
several times during this pass; treat both as "~150 files, ~1260 raw
`: list` parameter declarations").

**Not every raw site is equally dangerous.** The proven trigger requires
an *indexed read* (`param[i]` or `.get(i)`) on the `list`-typed parameter
inside the function body — a parameter only ever `.push()`ed into,
`.len()`ed, or passed through untouched does not exercise the bug. A
follow-up regex/AST triage across the 66-file crypto/wire/encoding/money
tier (below) found **750 of ~997 sites (~75%) have this indexed-read
shape** — the overwhelming majority are live risk, not just declared
risk.

## Risk classification (4 tiers, per the assigned methodology)

| Tier | Files | Raw `: list` sites | Status this pass |
|---|---|---|---|
| 1. CRYPTO / wire / encoding / money | **70** | **997** | Complete enumeration below. 1 file's dangerous shape (`os/crypto/hotp.spl`) confirmed PROVED by pattern match; verification blocked by an unrelated `os.*`-namespace JIT-linking issue (see "What was attempted" below). No new fixes landed this pass. |
| 2. Protocol codecs (http/websocket/tcp/stomp/game_net/etc.) | **54** | **182** | Listed, not fixed. |
| 3. Data-processing / CLI / MCP tooling | **24** | **78** | Listed, not fixed. |
| 4. (UI/internal) | 0 identified as a distinct bucket — see note | — | — |

Note: no files in this census matched a distinct "UI" bucket (this
codebase's UI layer is largely typed-array/struct based already); the
4th tier collapsed into tier 3 (general data-processing/CLI/tooling).

## Tier 1: CRYPTO / wire / encoding / money — complete enumeration (70 files, 997 sites)

Includes 4 files the keyword grep initially missed and had to be
reclassified up from tier 3 on manual review: `aws_sigv4.spl` (x3,
identical across the `gc_async_mut`/`nogc_async_mut`/`nogc_sync_mut`
layout tiers — AWS request-signature generation, a direct signature-
correctness risk) and `os/tls13/hkdf.spl` (TLS 1.3 key-schedule HKDF —
compromises session key material if wrong).

By raw site count, descending (files with 0 shown were below the
per-file cutoff for this table; full list in
`scratchpad/crypto_tier_counts.txt`, not committed):

```
54  src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/kafka/types.spl   (byte-identical x3)
47  src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/kafka/protocol.spl (byte-identical x3)
46  src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/kafka/consumer.spl (byte-identical x3)
39  src/os/crypto/ml_dsa.spl                  (NIST FIPS 204 post-quantum signatures)
39  src/os/crypto/ml_dsa_sample.spl
36  src/os/crypto/ml_kem_kpke.spl              (NIST FIPS 203 post-quantum KEM)
28  src/os/crypto/ed448.spl                    (EdDSA signature curve)
27  src/os/crypto/curve25519_bigint.spl        (X25519/Ed25519 field arithmetic)
21  src/lib/common/aes/cipher.spl
18  src/os/crypto/ml_dsa_ntt.spl
18  src/os/crypto/ffdhe.spl                    (finite-field Diffie-Hellman)
17  src/os/crypto/ml_kem.spl
15  src/lib/common/crypto/sha1.spl
14  src/os/crypto/rsa_fallback.spl
14  src/lib/common/crypto/rsa_pkcs1.spl
13  src/os/crypto/scrypt.spl                   (password KDF)
12  src/os/crypto/whirlpool.spl
12  src/os/crypto/rsa_pss.spl                  (RSA signature padding)
12  src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/kafka/producer.spl (x3)
11  src/os/crypto/streebog.spl                 (GOST hash)
11  src/lib/common/crypto/sha3.spl
11  src/lib/common/crypto/sha256_simd.spl
10  src/lib/common/aes/utilities.spl
9   src/os/crypto/ml_kem_ntt.spl
9   src/os/crypto/hotp.spl                     (RFC 4226/6238 OTP — see below)
9   src/os/crypto/cshake.spl
9   src/lib/common/encoding/ini.spl
9   src/lib/common/crypto/tls12_prf.spl
8   src/lib/common/jwt/sign.spl                (auth tokens)
6   src/os/crypto/sm3.spl
6   src/os/crypto/ripemd160.spl                (Bitcoin HASH160 partner to SHA-256)
6   src/lib/common/aes/key_expansion.spl
5   src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/kafka/serialization.spl (x3)
5   src/lib/common/jwt/types.spl
4   src/os/crypto/bip39.spl                    (wallet mnemonic)
4   src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/kafka/utilities.spl (x3)
4   src/lib/common/jwt/encode.spl
4   src/lib/common/crypto/sha256_core.spl
4   src/lib/common/aes/types.spl
3   src/os/crypto/jwt.spl, hkdf_ripemd160.spl, cose.spl
3   src/lib/common/encoding/yaml.spl
3   src/lib/common/aes/sbox.spl
2   src/os/crypto/slh_dsa_wots.spl (NIST FIPS 205 post-quantum, stateless hash sig), kmac.spl
2   src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/aws_sigv4.spl (x3)
2   src/lib/common/aes/padding.spl
1   src/os/tls13/hkdf.spl, scram_common.spl, pem.spl, pbkdf2.spl, pbkdf1.spl, mgf1.spl, hmac_ripemd160.spl
1   src/lib/common/jwt/utilities.spl
```

## What was attempted this pass (PROVED vs INFERRED)

**PROVED (pattern match, not yet both-engine-verified in place):**
`src/os/crypto/hotp.spl`, `_dynamic_truncate(hmac_bytes: list) -> i64`
reads `hmac_bytes.get(...)`. Its only callers (`hotp_sha1_bytes` /
`_sha256_bytes` / `_sha512_bytes`) pass the return value of
`hmac_sha1_bytes`/`hmac_sha256_bytes`/`hmac_sha512_bytes` from
`src/lib/common/crypto/hmac.spl`, which are **already typed**
`(key: [i64], data: [i64]) -> [i64]`. So `_dynamic_truncate` receives a
concrete `[i64]` value through an untyped `list` parameter — structurally
identical to the exact `_b58_list_get_byte(l: list, ...)` shape proven
broken in pass 8. This is a real, live, exploitable-by-pattern risk for
every HOTP/TOTP code the default engine ever computes.

**INFERRED, not verified — blocked, not fixed:** attempted to reproduce
this live via a probe (`hotp_sha1_bytes` against the independently
re-derived RFC 4226 Appendix D vectors, computed via python3
`hmac`+`struct`, matching the well-known published constants
755224/287082/359152/969429/338314/254676/287922/162583/399871/520489 for
counters 0-9). The probe hit an **unrelated** issue before it could
exercise the real default-engine path: calling into `os.crypto.hotp`
from a standalone top-level script triggered `[jit-fallback] unresolved
external symbol 'hotp_sha1_bytes': whole module dropped to the
interpreter` — i.e. the JIT silently fell back to the interpreter for
*this whole call*, so both "default" and "interpret" runs in the probe
actually executed the interpreter and matched the RFC vectors identically
(not because the bug is absent, but because the probe never reached the
JIT path that would expose it). `src/os/crypto/**` is flagged in this
repo's own CLAUDE.md as carrying an independent landmine (`W1006` `mut`
demotion) and is baremetal/freestanding-adjacent with its own linking
model — different enough from `src/lib/common/**` (where base58/sha256
live) that landing a fix here without first understanding *why* the JIT
silently declines this module would risk shipping an unverified change
into flagged-sensitive territory. Not fixed this pass; the shape-match is
PROVED, live confirmation is not.

**No other tier-1 files were touched this pass.** Given the scale
discovered (70 files / 997 sites in crypto/wire alone, not the handful
implied by "fix them this pass"), attempting a rushed retype across dozens
of files without the same both-engine/vacuity/independent-reference-vector
rigor already established for base58/sha256 would risk introducing new,
unverified breakage into cryptographic code — a worse outcome than leaving
the census as the deliverable. This is an explicit, disclosed scope
decision, not a silent shortfall.

## Recommended fix order for tier 1 (follow-up passes)

1. **Kafka (types/protocol/consumer/producer/serialization/utilities x3
   layout tiers)** — the 3 layout-tier copies are **byte-identical**
   (verified via `diff -q`), so one fix + a mechanical sync covers all 3;
   effectively 6 distinct files' worth of work, not 18. Wire-protocol
   parsing of untrusted network bytes — high exploitability.
2. **Post-quantum signature/KEM family** (`ml_dsa*`, `ml_kem*`,
   `slh_dsa_wots`) — largest raw site counts after kafka, NIST-standardized
   schemes where a silently wrong signature/ciphertext is exactly the
   base58 failure mode reproduced at much higher stakes.
3. **Classical asymmetric/signature** (`ed448`, `curve25519_bigint`,
   `rsa_pkcs1`, `rsa_pss`, `rsa_fallback`, `ffdhe`).
4. **Hash/HMAC/KDF primitives** (`sha1`, `sha3`, `sha256_simd`,
   `sha256_core`, `whirlpool`, `streebog`, `sm3`, `scrypt`, `pbkdf1/2`,
   `mgf1`, `cshake`, `kmac`, `ripemd160` + its `hmac_`/`hkdf_` wrappers,
   `tls12_prf`, `os/tls13/hkdf.spl`) — building blocks for everything
   above; fixing these narrows the risk surface fastest per file.
5. **Auth/token/wallet** (`jwt/*`, `hotp.spl`, `bip39.spl`, `cose.spl`,
   `pem.spl`, `jwt.spl` (os), `scram_common.spl`) — user-facing artifacts
   (tokens, OTP codes, mnemonics) where wrong output is directly
   exploitable or directly loses funds/access.
6. **AES** (`cipher`, `key_expansion`, `sbox`, `types`, `utilities`,
   `padding`) — symmetric cipher; a wrong round key/state is more likely
   to be self-evidently broken (ciphertext that never decrypts) than
   silently-wrong, lower relative priority within tier 1 despite
   `cipher.spl` having the single highest AES site count.
7. **`ini.spl`/`yaml.spl`** (config parsing) and `aws_sigv4.spl` (x3,
   request signing) — lower raw counts, include last within tier 1.

## Tier 2: Protocol codecs (54 files, 182 sites) — not fixed, listed only

HTTP client/server (`http_client/*`, `http_server/*`, `http/*` —
request/response/headers/url/auth basic+digest), TCP
(`nogc_sync_mut/tcp/{connect,listen,socket,types}.spl`), STOMP
(`stomp/message.spl`), game networking (`game_net/server.spl`), and the
remainder of the keyword-matched 48-file protocol/websocket/grpc/dns/etc.
set. Full file list in `scratchpad/proto_files.txt` (not committed —
regenerable via the grep in "Census methodology" filtered by protocol
keywords). Same risk mechanism as tier 1 (parsing untrusted wire bytes
through `list`-typed parameters) but not directly money/signature-bearing.

## Tier 3: Data-processing / CLI / MCP tooling (24 files, 78 sites) — not fixed, listed only

`cli_util.spl`/`cli/{formatting,utilities,flags}.spl` (x3 layout tiers),
`devhub/cmd_{bb,tasks,wiki}.spl`, `mcp/jj/tools_git_{branch,misc}.spl` (x2
tiers), `runtime/value.spl` (x2 tiers), `test/scaffold.spl`,
`test_runner/test_runner_args.spl`,
`slang/model_executor/model_loader/tensor_pack.spl`. Lowest priority:
internal tooling and CLI ergonomics, not externally-facing security
artifacts. A wrong value here is more likely to be a visible CLI/test
malfunction than a silent security defect.

## Compiler-side fix direction (for the seed lane — one paragraph, not an implementation)

Three independent trigger shapes for the same underlying `<<3` defect are
now on record (empty-list-first-assignment-then-rebind, loop-carried
push-realloc spill, and this pass's parameter-type-mismatch/erasure), all
rooted in how the default engine's JIT/native codegen represents and
(un)boxes elements of the untyped `list` type. Given the scale this
census exposes (~150 files, ~1260 declared sites, ~75%+ with the live
indexed-read shape, right at the coalesce campaign's scale), a per-call-
site source fix is not a durable strategy — new `: list` parameters will
keep being written faster than they can be swept. Two compiler-side
directions are worth the seed lane's judgment: (a) make untyped `list`
element reads simply correct under the default engine (fix the
unboxing/representation bug at its root, likely in the parameter-passing/
representation-inference path shared by all three trigger shapes) so the
type stops being a landmine; or (b) if (a) is not tractable soon, promote
a lint/error for `: list`-typed function parameters (steering all new and
existing code toward concrete element types like `[i64]`/`[u8]`, which
are proven safe in every shape tested across passes 7 and 8) — the
`W1006`-style demotion-detection precedent in `src/os/crypto` shows this
codebase already has infrastructure for exactly this kind of static
landmine gate.
