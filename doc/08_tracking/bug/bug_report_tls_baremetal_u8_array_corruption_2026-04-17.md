# Bug Report: Baremetal TLS first encrypted handshake record fails authentication on x86_64 after CCS

**ID:** `tls_baremetal_004`  
**Severity:** P1  
**Status:** open  
**Discovered:** 2026-04-17  
**Area:** x86_64 baremetal runtime / TLS fd-mode AEAD decrypt boundary

## Summary

The remaining `test/system/os_tls_system_spec.spl` failure is no longer in transport, transcript construction, `ServerHello` framing, fd-mode X25519, or handshake-secret derivation. The guest now:

- initializes VirtIO-net
- completes TCP connect to `10.0.2.2:4433`
- sends a plausible `ClientHello`
- receives and parses the first `ServerHello` record
- extracts the server key share and computes a `32`-byte shared secret that matches an independent host-side X25519 recomputation
- derives a `transcript_sh_hash` that exactly matches the server-side hash of `ClientHello || ServerHello`
- derives `CLIENT_HANDSHAKE_TRAFFIC_SECRET` and `SERVER_HANDSHAKE_TRAFFIC_SECRET` values that exactly match the rustls NSS key log output

The host rustls fixture still closes with:

```text
[SERVER FAIL: unexpected end of file]
```

The newest serial trace shows the post-DH key schedule now succeeds, the earlier record-length truncation bug is fixed, and the failure has moved to the first encrypted handshake record after the plaintext CCS:

```text
[tls13] after parse_server_hello cipher=4865 key_len=32
[tls13] after x25519 shared_len=32
[tls13] after server_hs_tk key_len=16 iv_len=12
[tls13] after client_hs_tk key_len=16 iv_len=12
[tls13] _io_recv_record header type=20 pay_len=<object>
[tls13] _io_recv_record header type=23 pay_len=420
[record13] decrypt raw_len=425 seq=0
[record13] header b0=23 b1=3 b2=3 b3=1 b4=164
[record13] payload_length=420
[TLS FAIL: handshake failed: authentication tag mismatch]
```

That means the remaining corruption is now below the TLS 1.3 key schedule and above the plaintext handshake parser. The guest reaches the first encrypted handshake record with a consistent 425-byte buffer and valid TLS header bytes, but the pure Simple AES-128-GCM decrypt still fails authentication on the baremetal fd-mode path.

## Reproduction

```bash
bin/simple test test/system/os_tls_system_spec.spl
```

Manual repro:

```bash
src/compiler_rust/target/debug/simple native-build \
  --clean \
  --source src --source examples \
  --backend cranelift \
  --entry-closure \
  --entry examples/simple_os/arch/x86_64/tls_system_test_entry.spl \
  --target x86_64-unknown-none \
  -o build/os/simpleos_tls_system_x86_64.elf \
  --linker-script examples/simple_os/arch/x86_64/linker.ld

tools/tls_test_server/target/debug/tls_test_server \
  --config tools/tls_test_server/server.sdn

qemu-system-x86_64 \
  -machine q35 -cpu qemu64 -m 2G \
  -kernel build/os/simpleos_tls_system_x86_64.elf \
  -display none -monitor none \
  -serial file:build/os/tls_system_manual_serial.log \
  -vga std \
  -device isa-debug-exit,iobase=0xf4,iosize=0x04 \
  -netdev user,id=net0,hostfwd=tcp::14433-:4433 \
  -device virtio-net-pci,netdev=net0
```

## Expected

- Guest should derive the TLS 1.3 handshake secret and traffic secrets after X25519.
- Guest should accept the plaintext CCS and then decrypt the first encrypted handshake record.
- Host rustls fixture should continue past `ServerHello`.
- Guest should reach `[TLS HANDSHAKE COMPLETE]`.

## Actual

- Guest completes TCP, `ServerHello`, X25519, handshake-secret derivation, and handshake traffic key/IV derivation.
- The guest receives the plaintext CCS and then the first encrypted handshake record (`type=23 pay_len=420`).
- `record13_decrypt(...)` now reaches AEAD validation and fails with `authentication tag mismatch`.

## Technical Notes

### What is already ruled out

- VirtIO-net init and TX submission
- ARP and gateway MAC learning
- TCP active open / SYN-SYN+ACK-ACK
- direct socket send/recv return-value encoding
- `ClientHello` truncation on the send path
- first TLS record header parse on the recv path
- `ServerHello` envelope parse (`type=2`, `body_len=118`)
- X25519 shared-secret derivation itself (`shared_len=32`)
- transcript ownership for `ClientHello || ServerHello`
- handshake secret / handshake traffic secret derivation
- handshake traffic key/IV derivation
- record-length truncation arithmetic on the first encrypted record

### Strongest current diagnosis

The remaining corruption is now clearly inside the baremetal pure-Simple AES-128-GCM implementation, not in the TLS 1.3 state machine:

1. the server-side capture now logs:

   - `SHA256(ClientHello_handshake_bytes)`
   - `SHA256(ServerHello_handshake_bytes)`
   - `SHA256(ClientHello || ServerHello)`
   - the full first encrypted server handshake record (`type=23`, `len=425`)

2. the guest's logged `transcript_sh_hash` matches the server's captured `SHA256(ClientHello || ServerHello)` exactly

3. the rustls fixture NSS key log output matches the guest's logged `CLIENT_HANDSHAKE_TRAFFIC_SECRET` and `SERVER_HANDSHAKE_TRAFFIC_SECRET`

4. using the server-captured encrypted record plus the guest's `SERVER_HANDSHAKE_TRAFFIC_SECRET`, an external AES-GCM decrypt succeeds with:

   - the guest-derived `server_hs_key`
   - the guest-derived `server_hs_iv`
   - the exact record header as AAD
   - the server-captured ciphertext and tag

5. the same input still fails inside `src/os/crypto/aes128_gcm.spl` on baremetal with `authentication tag mismatch`

That means the active remaining bug is now in the baremetal pure-Simple AES-128-GCM implementation, most likely one of:

1. AES-128 block encrypt under baremetal runtime semantics
2. GHASH / GF(2^128) multiplication under baremetal runtime semantics
3. counter-mode/tag assembly under baremetal runtime semantics

The key-schedule frontier is closed; the active frontier is the record AEAD implementation.

The newest fd-mode traces narrowed and then reduced the frontier further:

```text
[tls13] early_secret ...
[tls13] empty_thash ...
[tls13] hs_derived ...
[tls13] handshake_secret ...
```

Using the guest's corrected `dhe_shared`, external recomputation now shows:

- `early_secret` should be the standard TLS 1.3 no-PSK constant
- `empty_thash` should be `SHA256("")`
- `hs_derived` should be the standard `derived` constant

Those are now all correct on the fd-mode path after two targeted fixes:

1. fd-mode `early_secret` is explicitly pinned to the RFC 8446 no-PSK constant because the baremetal-compiled Simple `tls13_early_secret()` path was returning all-zero bytes
2. fd-mode `hs_derived` now uses a dedicated constant-label helper because the generic dynamic-label `rt_tls13_hkdf_expand_label(..., "derived", ...)` path was producing the wrong value

The next bad value is now `handshake_secret`.

Using the corrected guest `hs_derived` and guest `dhe_shared`, an external HKDF recomputation shows `handshake_secret` should be:

```text
9844576e7f28739534b86fe015a94c273c026e5c543fcb20b1ac2a93dfd5a6d6
```

but the guest still logs a different `handshake_secret`, which moves the active frontier down to:

1. `rt_tls13_hkdf_extract(...)`
2. then the fd-mode handshake-traffic secret expansion path

Attempting to switch only the `handshake_secret` step back to the pure Simple `hkdf_extract(...)` path is not a usable workaround either: on baremetal it returns a corrupted mostly-zero value, so the baremetal-compiled Simple extract path is also not trustworthy yet.

### Latest key evidence

The rustls fixture now writes NSS-format key log lines through `SSLKEYLOGFILE`, which provide host-side ground truth, and the test server now logs the server-side transcript hash plus the full first encrypted server record:

```text
[tls-transcript ch_sh sha256=3d1e825011deecd0e6ab56dfad69e2ab6aa1a58f9851b0e63fcb5929a4579e6f]
[tls-record server_encrypted len=425 hex=17030301a4...]
CLIENT_HANDSHAKE_TRAFFIC_SECRET ... 16fa4bee...
SERVER_HANDSHAKE_TRAFFIC_SECRET ... d43cba2c...
```

The guest now derives matching values for the same connection:

```text
[tls13] transcript_sh_hash 0=61 1=30 2=130 3=80 ...
[tls13] client_hs_secret 0=22 1=250 2=75 3=238 ...
[tls13] server_hs_secret 0=212 1=60 2=186 3=44 ...
```

An external host-side decrypt of the captured server encrypted record succeeds with the guest-derived handshake key material, while the baremetal pure-Simple decrypt still fails. So the remaining failure is now proven to be in the guest-side baremetal AES-GCM implementation, not the fd-mode key schedule.

### Files involved

- `src/os/tls13/tls13.spl`
- `src/os/tls13/record13.spl`
- `src/os/tls13/hkdf.spl`
- `src/os/tls13/key_schedule.spl`
- `examples/simple_os/arch/x86_64/boot/curve25519_ring_helper.c`
- `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c`
- `examples/simple_os/arch/x86_64/tls_system_test_entry.spl`
- `test/system/os_tls_system_spec.spl`

## Recommended Next Steps

1. Add a baremetal-only reference AEAD helper for fd-mode TLS records, or finish replacing the remaining mutation-sensitive code paths inside `src/os/crypto/aes128_gcm.spl`.
2. Add a focused baremetal regression test for AES-128-GCM using the captured TLS handshake record as a fixture.
3. Once decrypt is green, validate the matching baremetal encrypt path for `client Finished` and application data.

## 2026-04-18 Update

Later fd-mode work changed the frontier again:

- the C-side fd decrypt helper now successfully authenticates and decrypts the first encrypted server handshake record
- C-side debug proves the plaintext is valid and starts with `EncryptedExtensions` (`0x08 00 00 06 ...`) and ends with content type `0x16`
- direct chunk reads through `rt_tls13_record_decrypt_fd_chunk(0, 8)` also work and return the expected plaintext bytes on the Simple side

The remaining failure is now narrower than AES-GCM itself. The active bug is in the baremetal C/Simple bridge for fd-mode record-decrypt results:

- metadata-style result surfaces still arrive in Simple as `ct=0 data_len=0`
- the server closes with EOF because the guest never advances from the decrypted first encrypted handshake record into parsed handshake messages

So the current active frontier is:

1. baremetal extern ABI / bridge behavior for fd-mode decrypt metadata or large-result handling
2. only after that, any remaining handshake parser issues

## 2026-04-18 Later Update

## 2026-04-18 Exact Artifact Reality Check

An exact rebuild of the system-test artifact changed the live frontier again.

Exact rebuild command:

```sh
src/compiler_rust/target/debug/simple native-build --clean \
  --source src --source examples \
  --backend cranelift \
  --entry-closure \
  --entry examples/simple_os/arch/x86_64/tls_system_test_entry.spl \
  --target x86_64-unknown-none \
  -o build/os/simpleos_tls_system_x86_64.elf \
  --linker-script examples/simple_os/arch/x86_64/linker.ld
```

Manual QEMU repro against that exact ELF still fails at the older boundary:

```text
[tls13] _io_recv_record header type=23 pay_len=420
[record13] decrypt raw_len=425 seq=0
[record13] payload_length=420
[TLS FAIL: handshake failed: authentication tag mismatch]
```

So the exact freestanding artifact consumed by `test/system/os_tls_system_spec.spl`
is not yet on the later `CertificateVerify` frontier. The live remaining order is:

1. restore the later decrypt/handshake-walk behavior on the exact freestanding ELF
2. only then continue the baremetal `CertificateVerify` verifier lane

The baremetal TLS system lane moved past the old decrypt-bridge boundary.

What is now proven:

- the guest reaches and parses all four server encrypted handshake messages from the first encrypted record:
  - `EncryptedExtensions`
  - `Certificate`
  - `CertificateVerify`
  - `Finished`
- the `CertificateVerify` transcript hash is no longer the active problem:
  - `cv_hash` is now a full non-zero 32-byte SHA-256 value on baremetal
- the remaining failure is upstream of Ed25519 verification inputs:
  - `cert_der_len=0`
  - extracted Ed25519 pubkey length is `0`

Most recent live evidence:

```text
[tls13] handshake msg type=11 total=285
[tls13.hs] cert body len=281 ctx_len=0
[tls13.hs] cert body b0=0 b1=0 b2=1 b3=21
[tls13] cv sig_scheme=2055 cert_der_len=0 sig_len=64 pubkey_len=0
[TLS FAIL: handshake failed: CertificateVerify signature invalid (ed25519)]
```

That narrows the active remaining bug to the baremetal server-certificate extraction path, not transport, not X25519, not handshake AEAD, and not the `CertificateVerify` transcript hash itself.

Additional findings from this pass:

- the TLS `Certificate` body bytes are present and sane on baremetal (`00 00 01 15 ...`), so the certificate material exists in the decrypted handshake stream
- the Simple-side certificate extraction helpers still behave incorrectly on baremetal in this path
- a new C helper `rt_tls13_certificate_body_ed25519_pubkey(...)` was added, but its result is still not making it through as a usable 32-byte pubkey in the current fd-mode flow

Current active frontier:

1. baremetal extraction of the first server certificate / SPKI Ed25519 pubkey from the decrypted TLS `Certificate` body
2. then re-run `CertificateVerify`
3. then validate server `Finished` and client `Finished`

## 2026-04-18 Final Update

The certificate extraction frontier is now cleared.

Latest proven state:

- fd-mode C extraction from the TLS `Certificate` body succeeds:
  - `cert_list_len=277`
  - `cert_len=272`
  - `certpk ok`
- the guest reaches `CertificateVerify` with a real 32-byte Ed25519 public key:
  - `pubkey_len=32`
- the extracted key matches the current `tmp/tls_test_server/server.pem` public key
- `cv_hash` is also a full non-zero 32-byte value

Most recent live evidence:

```text
[tls-c] certpk cert_list_len=277
[tls-c] certpk cert_len=272
[tls-c] certpk ok
[tls13] cert branch fd pubkey_len=32
[tls13] cv sig_scheme=2055 cert_der_len=0 sig_len=64 pubkey_len=32
[TLS FAIL: handshake failed: CertificateVerify signature invalid (ed25519)]
```

Additional attempted fixes in this pass:

- `_ed_rv_to_bytes(...)` in `baremetal_stubs.c` was changed to use `_rv_byte(...)` instead of unconditional `DECODE_INT(...)`
- `_ed25519_verify(...)` was broadened to try both decoded point orientations

Neither change moved the failure.

Current active remaining bug:

1. baremetal `rt_ed25519_verify(...)` / `_ed25519_verify(...)` still rejects the server's valid TLS 1.3 `CertificateVerify`
2. transport, transcript-before-CV, certificate extraction, X25519, handshake key schedule, and handshake record decrypt are no longer the active blockers

## 2026-04-18 Transcript/Signature Update

Further narrowing from the latest live runs:

- the fd-mode C helper now extracts the correct server Ed25519 public key directly from the TLS `Certificate` body while the message is still live
- that extracted key matches the current `server.pem` public key exactly
- the guest now logs the full 64-byte `CertificateVerify` signature and a full 32-byte `cv_hash`
- external off-guest verification using the guest's current `(pubkey, signature, cv_hash)` still fails

This shifts the highest-probability frontier again:

1. the baremetal pre-`CertificateVerify` transcript hash is still wrong, even after the fd-mode direct transcript-byte rebuild
2. if the transcript hash is later proven correct against a host-side reconstruction, then the remaining fallback suspect is the parsed `CertificateVerify` signature bytes

Most recent decisive evidence:

```text
[tls-c] certpk ok
[tls13] cert branch fd pubkey_len=32
[tls13] cv sig_scheme=2055 cert_der_len=0 sig_len=64 pubkey_len=32
[TLS FAIL: handshake failed: CertificateVerify signature invalid (ed25519)]
```

and off-guest verification of the guest's current values returned `VERIFY_BAD`.

## 2026-04-18 Ed25519 Verify Update

The transcript and signature parsing boundaries are now cleared too.

Latest proven state:

- the instrumented `tools/tls_test_server` now logs the server's actual `CertificateVerify` signed-message tail and the full 64-byte signature
- the guest `cv_hash` matches the server's signed-message tail exactly
- the guest `cv_sig_lo` / `cv_sig_hi` match the server's logged signature exactly
- a dedicated fd-mode helper `rt_tls13_ed25519_verify(...)` is linked into the baremetal image and invoked from the TLS client path

Most recent live evidence:

```text
[server cv suffix=f69ebdc26d7a07fa2c9059a8fd9172a6bee40e7b26dc653a5c6fa2a7f7dc9bb0]
[tls13] cv_hash ... = f69ebdc26d7a07fa2c9059a8fd9172a6bee40e7b26dc653a5c6fa2a7f7dc9bb0

[server cv sig=431d7c417bb847609101a26666fa9cacad64c27133b2c8f1b11f76c88ec3c7ab68a30d0f782c0099682c15bba1352f691e1372ce454c5ad38da067f80b930e00]
[tls13] cv_sig_lo ... = 431d7c417bb847609101a26666fa9cacad64c27133b2c8f1b11f76c88ec3c7ab
[tls13] cv_sig_hi ... = 68a30d0f782c0099682c15bba1352f691e1372ce454c5ad38da067f80b930e00
[tls13] fd cv verify rc=1
```

Current active remaining bug:

1. the baremetal external Ed25519 verification path is still wrong for standard TLS 1.3 `CertificateVerify`
2. transcript assembly is no longer the active issue
3. certificate extraction is no longer the active issue
4. signature parsing is no longer the active issue

Highest-probability remaining sub-causes:

- the SHA-512 path used by the baremetal verifier helper is still producing the wrong digest on baremetal
- or the Edwards point math / double-scalar-multiply / point re-encoding path is still inconsistent with the standard verifier

Next debug step:

- compare the helper's internal SHA-512 digest (or reduced `h` scalar) against a host-side reference for the same `(R, A, message)` tuple to separate SHA-512 from Edwards-point arithmetic

## 2026-04-18 Exact Freestanding Update

The exact `build/os/simpleos_tls_system_x86_64.elf` lane was retested after moving more
of the TLS 1.3 `CertificateVerify` path onto fd-only C helpers.

What was changed:

- fd mode now uses C helpers for:
  - `cv_hash`
  - `Certificate` pubkey extraction
  - `CertificateVerify` algorithm extraction
  - `CertificateVerify` signature extraction
- fd mode also switched its pre-`CertificateVerify` and pre-`Finished` transcript hash
  source away from the mutable `Transcript.buf` path and onto direct C-side hashing.

Current exact-lane result:

- the handshake still fails at server `CertificateVerify`
- the values printed in the exact serial are still not host-truth values
- in particular:
  - the extracted Ed25519 pubkey no longer matches `tmp/tls_test_server/server.pem`
  - the extracted 64-byte `CertificateVerify` signature does not line up with a
    valid server-side verification input
  - signing the guest's current `cv_hash` off-guest with the deterministic server
    Ed25519 key does **not** reproduce the guest-observed signature

This changes the active remaining bug again:

1. the exact freestanding fd-path is still assembling corrupted handshake-message bytes
   for `Certificate` / `CertificateVerify`
2. the verifier math is no longer the first thing to fix on the exact lane
3. the next highest-value boundary is the raw `msg_bytes` / handshake-body assembly
   between `record13_decrypt_fd_inner(...)` and the fd-only `Certificate` /
   `CertificateVerify` helpers

## 2026-04-18 Exact Freestanding Raw-Record Update

The exact lane was retested again after moving even more of the first encrypted
server-handshake parsing into C:

- fd mode now asks a new raw-record helper to decrypt the TLSCiphertext record and
  return `EncryptedExtensions`, `Certificate`, `CertificateVerify`, and `Finished`
  messages directly by handshake type
- the older Simple-side `inner -> dec_data -> hs_buf` append/rebuild path is no
  longer the first suspected corruption point

Current exact-lane result:

- the system test still fails at server `CertificateVerify`
- the newly returned raw-record C message bytes still do **not** produce host-truth
  values for:
  - `cv_hash`
  - extracted Ed25519 pubkey
  - extracted `CertificateVerify` signature
- the values change again relative to the previous run, which means the remaining
  corruption is still upstream of Ed25519 verification and upstream of the older
  Simple-side buffer append path

This changes the active remaining bug again:

1. the exact freestanding failure is now best described as a C-side raw encrypted
   record to handshake-message extraction bug
2. the Ed25519 verifier is not the first thing to fix on the exact lane
3. the next highest-value boundary is to instrument the raw-record helper itself in C
   and compare:
   - decrypted plaintext bytes before message scan
   - found message first bytes
   - returned runtime-array bytes observed on the Simple side
