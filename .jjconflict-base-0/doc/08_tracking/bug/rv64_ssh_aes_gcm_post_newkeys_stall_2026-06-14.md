# RV64 SSH AES-GCM Post-NEWKEYS Stall

Date: 2026-06-14
Status: Open
Severity: P0 for RV64 live SSH

## Summary

The RV64 live SSH gate now passes OpenSSH host-key verification and reaches
post-NEWKEYS encrypted I/O, but the first server-to-client encrypted packet
does not complete. The server enters `send_packet` for `SSH_MSG_EXT_INFO`
with `cipher.active=true` and `encrypted_io=true`, then stalls inside the
AES-GCM encryption path before producing the encrypted packet bytes.

## Evidence

- Command:
  `SIMPLE_LIB=src SIMPLEOS_RV64_SSH_LIVE=1 bin/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl --mode=interpreter --no-cache`
- Memory-captured run:
  `build/qemu-memory-check/rv64-ssh-live-encrypted-gate-20260614T115907Z.log`
  timed out at 120s, max RSS 145340 KB.
- Short rerun after switching `ssh_cipher_live` to `os.crypto.aes256_gcm`:
  `build/qemu-memory-check/rv64-ssh-live-aes256fast-20260614T120220Z.log`
  failed after 12.67s when the host probe timed out, max RSS 155120 KB.
- Serial markers:
  - `cipher activated c2s_seq=0 s2c_seq=0`
  - `send_packet msg_type=7 force_plain=false active=true encrypted_io=true`
  - `send_packet branch=encrypted`
  - no `encrypted s2c packet ...` marker follows.

## Cleared Earlier Blockers

- OpenSSH now accepts `SSH_MSG_KEX_ECDH_REPLY` and receives server NEWKEYS.
- The live Ed25519 signature verifies against the logged exchange hash.
- The RV64 enum-state gate bug was bypassed by using `cipher.active` as the
  post-NEWKEYS encryption gate.

## Required Fix

Add a freestanding RV64 native SSH AES-GCM packet helper, or otherwise make
`rt_tls13_aes256_gcm_encrypt/decrypt` real on the RV64 live image. Keep a
dual-backend alpha comparison against the pure Simple AES-GCM implementation
on bounded fixtures, and fail closed if C/native and pure Simple disagree.

## Update: 2026-06-14 12:16 UTC

The post-NEWKEYS stall is cleared after adding the freestanding
`tls13_aes256_gcm_helper.c` helper and routing `ssh_cipher_live.spl` directly to
the runtime externs instead of importing the pure/SIMD AES module.

New memory-captured run:
`build/qemu-memory-check/rv64-ssh-live-directsign-aes256c-20260614T121608Z.log`
failed after 46.86s, max RSS 169728 KB.

Current status:

- Ed25519 alpha direct/component/pure signing now agrees for the live exchange.
- OpenSSH accepts `SSH_MSG_KEX_ECDH_REPLY` and the Ed25519 server host key.
- Server emits encrypted EXT_INFO:
  `encrypted s2c packet seq=0 len=68`.
- OpenSSH rejects that packet with
  `message authentication code incorrect`.

Packet comparison:

- AES-CTR ciphertext bytes match Python `cryptography` for the reconstructed
  EXT_INFO plaintext.
- The GCM authentication tag differs on RV64.
- A host harness calling `aes256_gcm_encrypt_raw` in
  `tls13_aes256_gcm_helper.c` produces the Python/OpenSSH-expected tag for the
  same key, nonce, AAD, and plaintext.

The remaining blocker is therefore RV64 live helper/wrapper divergence for the
GCM tag path, not SSH framing, key derivation, Ed25519 signing, or AES counter
encryption.

## Update: 2026-06-14 12:48 UTC

Further live runs narrowed and fixed several packet-layer issues:

- `ssh_build_ext_info_server_sig_algs` now builds the live `ssh-ed25519`
  EXT_INFO payload with explicit byte pushes. The previous helper path produced
  heap-looking bytes in the encrypted plaintext on RV64.
- `_make_nonce` now avoids indexed array mutation and builds OpenSSH-style
  AES-GCM nonces as `iv[0..4] || uint64(seq)`.
- The first encrypted EXT_INFO packet can now be reproduced byte-for-byte with
  Python `cryptography` from the logged key, nonce, AAD, and body.

Current blocker moved back to Ed25519 alpha signing:

- For some live exchange hashes, monolithic direct runtime Ed25519 and
  component runtime/pure Simple Ed25519 produce the same `R` but different `S`.
- Component runtime and pure Simple agree with each other, but OpenSSH rejects
  that signature for at least one captured exchange.
- Alpha mode fails closed on the mismatch, so the host signature becomes empty
  and KEX stops with `host key signing failed`.

Next required fix: make the pure/component Ed25519 scalar path match the
OpenSSH-accepted direct runtime signature, or prove the direct helper is wrong
with an external verifier and fix the direct helper. Do not disable the alpha
mismatch guard as a release fix.

## Update: 2026-06-14 12:59 UTC

Ed25519 alpha signing is cleared for the captured RV64 live mismatch:

- Added `test/01_unit/os/crypto/ed25519_ssh_exchange_hash_spec.spl` coverage
  for the previous live mismatch hash.
- `src/os/crypto/sha512.spl` now performs SHA-512 additions with explicit
  modulo-2^64 32-bit-limb carries so the pure Simple path does not depend on
  interpreter overflow behavior.
- `src/os/crypto/ed25519.spl` now uses the OS byte-array pure SHA-512 path for
  non-live pure signing, matching the live pure-check backend.
- `src/os/crypto/ed25519_scalar.spl` now propagates scalar multiplication
  carries through 32-bit limbs without overflowing checked `u64` additions.

Focused evidence:

- `SIMPLE_LIB=src bin/simple test test/01_unit/os/crypto/ed25519_ssh_exchange_hash_spec.spl --mode=interpreter --no-cache`
  passes 2/2.
- `SIMPLE_LIB=src bin/simple check src/os/crypto/sha512.spl src/os/crypto/ed25519.spl src/os/crypto/ed25519_scalar.spl src/os/apps/sshd/ssh_transport.spl src/os/apps/sshd/ssh_cipher_live.spl src/os/apps/sshd/ssh_session.spl src/os/apps/sshd/ssh_session_kex.spl`
  passes 7/7.
- QEMU memory run
  `build/qemu-memory-check/rv64-ssh-live-alpha-ed25519-fixed-20260614T125833Z.log`
  failed after 47.02s with max RSS 169520 KB.

The live serial log now shows runtime and pure Ed25519 alpha agree:

- `ed25519 alpha runtime done len=64`
- `live pure sig=4407180fd13e2a6d158b1c871c9f463d98347d570a8f38b7d204344dddde8554d9792a7394bbf535ad919cc67a3d0d9e3fbc38d4e6c6de0a67f73fad950a5801`
- `host ed25519 sig raw=4407180fd13e2a6d158b1c871c9f463d98347d570a8f38b7d204344dddde8554d9792a7394bbf535ad919cc67a3d0d9e3fbc38d4e6c6de0a67f73fad950a5801`

The remaining blocker is post-NEWKEYS AES-GCM packet handling:

- OpenSSH accepts the Ed25519 host key and receives server NEWKEYS.
- Server activates cipher at `c2s_seq=3 s2c_seq=3`.
- Server sends encrypted EXT_INFO with nonce
  `94976bf50000000000000003`.
- OpenSSH then fails with
  `message authentication code incorrect`.

Next required fix: determine whether OpenSSH expects the first encrypted
server-to-client packet sequence to use the reset read sequence (`0`) or the
pre-reset transport sequence (`3`), and keep the AES-GCM helper under
direct-runtime vs pure/backend evidence while correcting packet counters.

## Update: 2026-06-14 13:07 UTC

Two additional live probes refined the AES-GCM blocker:

- `build/qemu-memory-check/rv64-ssh-live-strictseq0-20260614T130204Z.log`
  used strict-KEX reset packet counters (`seq=0`) and still failed at
  `message authentication code incorrect`, max RSS 169288 KB.
- `build/qemu-memory-check/rv64-ssh-live-rfc5647-nonce-20260614T130352Z.log`
  used RFC 5647 nonce construction from the full derived 12-byte IV
  (`fixed || invocation_counter`) and still failed at
  `message authentication code incorrect`, max RSS 169804 KB.

The RFC 5647 nonce packet was checked against Python `cryptography`:

- key:
  `88e4831260f908a353d0752a94d7f850b5ba48b9a8457cf4f26addddcec35938`
- nonce:
  `f5821ca44caf3aa5c35632cb`
- AAD:
  `00000030`
- body:
  `0807000000010000000f7365727665722d7369672d616c67730000000b7373682d656432353531390000000000000000`
- RV64 output matched Python exactly:
  `00a13f3d96c3e5d15a1f298a3abb0b43765356e002c5cf0524e33732caabaf930af1abbf0c1ccda2a8d9ad6e0743aa423336c08b884bc5b20989370f7230d4e4`

That moves the current blocker away from AES-GCM primitive/tag generation and
toward SSH transcript alignment: key material, sequence reset semantics, or
which encrypted packet OpenSSH expects first.

A temporary no-`ext-info-s` diagnostic run
`build/qemu-memory-check/rv64-ssh-live-no-server-extinfo-20260614T130625Z.log`
was reverted. It changed the exchange hash and correctly failed closed on a
new Ed25519 runtime/pure alpha mismatch before reaching AES-GCM, max RSS
169556 KB. Keep the alpha guard enabled; do not use optional KEX changes to
mask signature disagreement.

The pre-reset sequence branch was also checked:

- `build/qemu-memory-check/rv64-ssh-live-rfc5647-seq3-20260614T130903Z.log`
  used RFC 5647 full-IV nonce construction with transport sequence offset
  `seq=3`.
- OpenSSH still failed with `message authentication code incorrect`.
- Max RSS was 170552 KB.

Both `seq=0` and `seq=3` are therefore insufficient explanations for the MAC
failure. Next required fix: compare the server's derived `K`, `H`, KEXINIT
transcripts, and KDF inputs against an independently instrumented OpenSSH/libssh
trace or a deterministic local harness. The AES-GCM primitive output is
currently byte-for-byte correct for the server's logged key/nonce/AAD/body.

## Update: 2026-06-14 13:21 UTC

The latest cautious QEMU memory gate was run after restoring OpenSSH-compatible
AES-GCM nonce construction to append-only `IV + seq` with strict encrypted
packet counters reset to zero:

- `build/qemu-memory-check/rv64-ssh-live-openssh-gcm-iv-append-20260614T132045Z.log`
  failed after 47.25s with max RSS 170208 KB.
- No `qemu-system*` process remained after the wrapper exited.
- Focused source check passed first:
  `SIMPLE_LIB=src bin/simple check src/os/apps/sshd/ssh_cipher_live.spl src/os/apps/sshd/ssh_session_kex.spl`

This run did not reach the prior post-NEWKEYS MAC failure. The live serial log
shows a fresh exchange hash and the Ed25519 alpha guard correctly refused a
runtime/pure signature mismatch:

- exchange hash:
  `4fc2235b8e250bddf378a99746eb381ce98d37fe546697f7435960d3da7d77eb`
- OpenSSH good transcript received disconnect packet type 1 after KEX init.
- Serial trace:
  `ed25519 alpha mismatch: refusing runtime signature`

Keep the alpha comparison fail-closed. The next fix is to make runtime C-backed
Ed25519 and pure Simple Ed25519 agree for this new live exchange hash before
continuing AES-GCM/KDF debugging.

## Update: 2026-06-14 13:40 UTC

The Ed25519 alpha lane was hardened with two more deterministic regressions:

- `test/01_unit/os/crypto/ed25519_scalar_muladd_spec.spl` now checks the
  scalar reductions and `S = r + k*a mod L` value for the RV64 diagnostic
  exchange hash.
- `test/01_unit/os/crypto/ed25519_ssh_exchange_hash_spec.spl` now covers four
  RFC8032-seed SSH exchange hashes, including
  `4fc2235b8e250bddf378a99746eb381ce98d37fe546697f7435960d3da7d77eb` and
  `86160706af75af6a1265f3157862dc14c201fca9f121afb163effc0b395d3dd3`.
- `src/os/crypto/ed25519_scalar.spl` now uses bit-serial modulo-L reduction
  and modular double-and-add multiplication for `sc_muladd`, avoiding the
  previous wide schoolbook carry-loss path.

Focused evidence:

- `SIMPLE_LIB=src bin/simple test test/01_unit/os/crypto/ed25519_scalar_muladd_spec.spl --mode=interpreter --no-cache`
  passes 3/3.
- `SIMPLE_LIB=src bin/simple test test/01_unit/os/crypto/ed25519_ssh_exchange_hash_spec.spl --mode=interpreter --no-cache`
  passes 4/4.
- `SIMPLE_LIB=src bin/simple check src/os/crypto/ed25519_scalar.spl src/os/crypto/ed25519.spl src/os/apps/sshd/ssh_session_kex.spl test/01_unit/os/crypto/ed25519_scalar_muladd_spec.spl test/01_unit/os/crypto/ed25519_ssh_exchange_hash_spec.spl`
  passes 5/5.

The latest QEMU memory gate:

- `build/qemu-memory-check/rv64-ssh-live-ed25519-four-vectors-20260614T134005Z.log`
  failed after 45.65s with max RSS 169624 KB.
- Ed25519 alpha cleared again; serial shows a non-empty host signature for
  exchange hash `f0e7e4ba2251d9fd8ffe328561ee089cc182242fb9580af2029026c982a89afa`.
- The first encrypted EXT_INFO packet still fails in OpenSSH with
  `message authentication code incorrect`.
- The logged AES-GCM packet independently matches Python `cryptography`:
  key `4bc0de4f40e9be06d4f294b42c2718d6f85bfce70167eda2c39acea563c50714`,
  nonce `b7202085ba07188ec9454efc`, AAD `00000030`, body
  `0807000000010000000f7365727665722d7369672d616c67730000000b7373682d656432353531390000000000000000`,
  output
  `96987f64cebcc8b5a98c715eca45f3100b82a99391fdc6bb9de07498992855d8d824cfe3d762e3fea609c88040990b5eb04404582e120401e438275956c73704`.

Current blocker: KEX/key stream alignment with OpenSSH after NEWKEYS. Ed25519
and the AES-GCM primitive are no longer the active explanation for this run.

## Update: 2026-06-14 13:58 UTC

The post-NEWKEYS MAC failure now has a concrete KDF explanation:

- Added a live KDF alpha check in `src/os/apps/sshd/ssh_session_kex.spl` that
  derives server-to-client IV/key using both pure `ssh_derive_keys` and the
  runtime SHA-256 helper.
- Fresh QEMU build
  `build/qemu-memory-check/rv64-ssh-live-fresh-build-kdf-alpha-20260614T135535Z.log`
  failed after 46.20s, max RSS 169236 KB.
- Serial evidence showed Ed25519 alpha cleared, then KDF alpha failed closed:
  - pure `iv_s2c=f2f02928f41f49eafc384b54`
  - runtime `iv_s2c=f6600627b3c7c1778bab095d`
  - pure `key_s2c=895f72bc70c813f33b0a4d1619719908a0c719cee0bab5ecfb5594555bea5eac`
  - runtime `key_s2c=faf39f819bd8700041b674ebdced1c4b91bee08cdc99250d0150ff1b898f2623`
  - `kdf sha256 alpha mismatch: refusing session keys`

This explains why OpenSSH rejected the first encrypted packet even though the
server's AES-GCM output matched Python for the server's own logged key/IV:
OpenSSH was deriving the runtime/OpenSSH-compatible key stream, while the
server had been using pure SHA-256-derived keys.

`src/os/crypto/sha256.spl` was patched to use explicit modulo-2^32 additions in
the message schedule, compression rounds, and state feed-forward path, matching
the earlier SHA-512 overflow hardening pattern.

Focused evidence:

- `SIMPLE_LIB=src bin/simple test test/01_unit/os/crypto/sha256_pure_simple_spec.spl --mode=interpreter --no-cache`
  passes 3/3.
- `SIMPLE_LIB=src bin/simple check src/os/crypto/sha256.spl src/os/apps/sshd/ssh_kex_core.spl src/os/apps/sshd/ssh_session_kex.spl`
  passes 3/3.

The next fresh QEMU build
`build/qemu-memory-check/rv64-ssh-live-sha256-modadd-kdf-alpha-20260614T135749Z.log`
failed earlier on a new Ed25519 runtime/pure alpha mismatch for exchange hash
`1951131fc61680b042ce4fa29bf90e8a7036044611d3210a143713dc3163ed2e`, max RSS
168872 KB, so the SHA-256 KDF alpha fix still needs another QEMU pass after the
remaining Ed25519 RV64 compiled-pure divergence is closed.

## Update: 2026-06-14 14:13 UTC

After patching point encoding to avoid indexed byte reads in `ed_point_encode`
and `fe_is_negative`, the guarded QEMU memory run
`build/qemu-memory-check/rv64-ssh-live-fe-is-negative-u8at-20260614T141305Z.log`
failed after 50.16s with max RSS 170316 KB.

The run left no `qemu-system-*` process behind, but the Ed25519 alpha guard
correctly failed closed again:

- exchange hash `192b439d2ba96c82125a2ad5f4fa6f137365b014558bdf5ff0ddcf4406e25f0d`
- direct runtime signature `59bf55a7b9c321e171e2ba4d3bbf54ad7898cfd56bdb41288b31097da078ddf54aac1b415a9eda477253d819170351af0d6a9193730521b76fca465e32c74107`
- pure/component signature `59bf55a7b9c321e171e2ba4d3bbf54ad7898cfd56bdb41288b31097da078dd7dcba81b56efc239b34eae7d758c0f6b133144abfb42dc514009c58502fc38a50e`
- first 32-byte `R` half now matches; remaining divergence is in the `S` half.

Current blocker: RV64 compiled-pure Ed25519 scalar/signature finalization still
diverges from the runtime C oracle for at least this exchange hash. The alpha
guard must remain in place until pure Simple and runtime C agree.

## Update: 2026-06-14 15:42 UTC

The Ed25519 alpha mismatch was reduced to a native point-encoding bug:

- A focused single-vector regression now lives at
  `test/01_unit/os/crypto/ed25519_rv64_single_exchange_hash_spec.spl`.
- Native mode reproduced the same bad signature bytes as the RV64 live run.
- `ed_point_encode` used a typed `if` expression for the sign byte:
  `val sign_bit: u8 = if fe_is_negative(x): 0x80 else: 0`.
- Native codegen narrowed that conditional expression incorrectly in the encode
  path, producing `0x08`-style corruption in the last encoded point byte.
- The fix uses explicit `u8` assignment:
  initialize `sign_bit` to zero and assign `(128).to_u8()` only when the sign is
  negative.

Focused evidence:

- `SIMPLE_LIB=src bin/simple test test/01_unit/os/crypto/ed25519_rv64_single_exchange_hash_spec.spl --mode=interpreter --no-cache`
  passes 1/1.
- `SIMPLE_LIB=src bin/simple test test/01_unit/os/crypto/ed25519_rv64_single_exchange_hash_spec.spl --mode=native --no-cache --force-rebuild`
  passes 1/1.
- `SIMPLE_LIB=src bin/simple test test/01_unit/os/crypto/ed25519_scalar_muladd_spec.spl --mode=interpreter --no-cache`
  passes 5/5.

Fresh QEMU evidence:

- `build/qemu-memory-check/rv64-ssh-live-ed25519-signbit-fix-20260614T154241Z.log`
  failed after 47.22s with max RSS 163336 KB.
- Ed25519 alpha cleared; the live run progressed to KDF alpha.
- KDF still fails closed:
  - pure `iv_s2c=38393519b4d15ea9f2a3511f`
  - runtime `iv_s2c=d90c7b6b48fa8e9eda76aa9f`
  - pure `key_s2c=10b04a0c661b756ab344354392cb0434b935db5089bf869d758fe8b06740694a`
  - runtime `key_s2c=e303ddaad63ebcaaf200f91ce3e3fb921f619c3a59410f9937d1a9da3107a747`
  - `kdf sha256 alpha mismatch: refusing session keys`

Current blocker: RV64/native pure SHA-256 KDF derivation still diverges from the
runtime/OpenSSH-compatible SHA-256 path. The alpha guard remains fail-closed and
must stay in place until both paths agree.

## Update: 2026-06-14 18:28 UTC

The SHA-256/KDF alpha mismatch was localized to native message-schedule
extension:

- Empty-string SHA-256 native output was wrong even though padding, constants,
  rotations, `Ch`, `Maj`, and the first 16 compression rounds matched the
  reference path.
- Focused diagnostics showed native schedule extension produced `w[16] =
  0x10000000` for the empty block, where SHA-256 requires `0x80000000`.
- `src/os/crypto/sha256.spl` now keeps the compression schedule as a 16-word
  ring with explicit slot access, avoiding the RV64/native dynamic
  `w[t - n]` array-index corruption.

Focused evidence:

- `SIMPLE_LIB=src bin/simple check src/os/crypto/sha256.spl src/os/crypto/curve25519.spl src/os/crypto/ed25519_ops.spl src/os/crypto/ed25519.spl test/01_unit/os/crypto/sha256_pure_simple_spec.spl test/01_unit/os/crypto/ed25519_rv64_single_exchange_hash_spec.spl test/01_unit/os/crypto/ed25519_scalar_muladd_spec.spl`
  passes 7/7.
- `SIMPLE_LIB=src bin/simple test test/01_unit/os/crypto/sha256_pure_simple_spec.spl --mode=interpreter --no-cache`
  passes 3/3.
- `SIMPLE_LIB=src bin/simple test test/01_unit/os/crypto/sha256_pure_simple_spec.spl --mode=native --no-cache --force-rebuild`
  passes 3/3.
- `SIMPLE_LIB=src bin/simple test test/01_unit/os/crypto/ed25519_rv64_single_exchange_hash_spec.spl --mode=interpreter --no-cache`
  passes 1/1.
- `SIMPLE_LIB=src bin/simple test test/01_unit/os/crypto/ed25519_rv64_single_exchange_hash_spec.spl --mode=native --no-cache --force-rebuild`
  passes 1/1.
- `SIMPLE_LIB=src bin/simple test test/01_unit/os/crypto/ed25519_scalar_muladd_spec.spl --mode=interpreter --no-cache`
  passes 5/5.

Full QEMU evidence remains incomplete because the external session boundary
killed long-running foreground/detached QEMU wrappers before the test harness
could write final status. No stale `qemu-system-*` process was left behind.

The side logs from the latest partial live run are still useful:

- `build/os/rv64-ssh-live.serial.log`
- `build/os/rv64-ssh-live.openssh-good.txt`

They show KEX completed, Ed25519 alpha matched, KDF alpha matched, NEWKEYS was
sent/received, the first server-to-client encrypted EXT_INFO packet was accepted
by OpenSSH, and OpenSSH then sent encrypted packet type 5. The serial log stops
at `recv_packet_payload encrypted_io=true` before `recv encrypted head bytes`,
so the current blocker has moved past SHA/KDF into post-NEWKEYS
client-to-server encrypted receive/decrypt or the boot TCP raw receive shim.

## Update: 2026-06-14 18:46 UTC

Parallel read-only agents converged on the receive path rather than crypto:

- AES-GCM sequence, nonce, AAD framing, runtime status-prefix handling, and
  EXT_INFO ordering are compatible with OpenSSH for the captured transcript.
- The expected next decrypted client payload is SSH message type 5
  (`SSH_MSG_SERVICE_REQUEST`, service `ssh-userauth`).
- The serial log stops before `recv encrypted head bytes`, so the old live fd
  200 encrypted path was spinning in the generic `rt_net_recv_bytes` loop before
  it ever had a complete encrypted SSH frame to decrypt.
- The RV64 boot TCP shim also advertises a fixed 4096-byte receive window and
  silently truncates payload if the RX buffer is full; that remains a follow-up
  hardening risk.

Implementation progress:

- Added `rt_boot_tcp_read_ssh_encrypted_packet(fd)` in
  `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`. It mirrors the
  plaintext packet helper but reads one encrypted SSH frame:
  4 clear length bytes plus `packet_length` encrypted body bytes plus the
  16-byte GCM tag.
- Exported it through
  `src/os/kernel/net/rt_net_socket_facade.spl` as
  `rt_net_recv_ssh_encrypted_packet`.
- Updated the live fd 200 encrypted branch in
  `src/os/apps/sshd/ssh_session.spl` to call the framed helper before the
  generic receive-buffer loop.
- Added
  `test/01_unit/os/apps/sshd/ssh_cipher_live_aes256_gcm_spec.spl` to prove the
  first encrypted `SSH_MSG_SERVICE_REQUEST` round-trips at sequence 0 and fails
  closed at sequence 1.

Focused safe evidence:

- `SIMPLE_LIB=src bin/simple check src/os/kernel/net/rt_net_socket_facade.spl src/os/apps/sshd/ssh_session.spl src/os/apps/sshd/ssh_cipher_live.spl test/01_unit/os/apps/sshd/ssh_cipher_live_aes256_gcm_spec.spl`
  passes 4/4.
- `SIMPLE_LIB=src bin/simple test test/01_unit/os/apps/sshd/ssh_cipher_live_aes256_gcm_spec.spl --mode=interpreter --no-cache`
  passes 2/2.
- `bin/simple os build --scenario=rv64-ssh` passes without launching QEMU and
  builds `build/os/simpleos_riscv64_ssh_live.elf` through the Cranelift live
  wrapper path, confirming the new C helper links in the SSH live lane.

No fresh full QEMU run was attempted for this patch because the previous long
QEMU attempts were killed by the external session boundary. Before the next live
attempt, check for stale QEMU processes and remove
`build/os/simpleos_riscv64_ssh_live.elf`.

## Update: 2026-06-14 23:46 UTC

The RV64 boot TCP shim was hardened for the receive-window risk identified by a
parallel read-only agent:

- `rt_send_tcp_packet` no longer advertises a fixed 4096-byte receive window.
  It now compacts unread RX bytes and advertises the actual free capacity in
  `g_boot_tcp_rx_buf`.
- Incoming TCP payload is no longer silently truncated when the RX buffer is
  full. The shim logs `BTCP RX FULL`, ACKs the current receive point, and leaves
  `g_boot_tcp_recv_next` unchanged so the peer can retry instead of losing the
  tail of an encrypted SSH frame.

Focused safe evidence:

- `SIMPLE_LIB=src bin/simple check src/os/crypto/sha256.spl src/os/kernel/net/rt_net_socket_facade.spl src/os/apps/sshd/ssh_cipher_live.spl src/os/apps/sshd/ssh_session.spl test/01_unit/os/apps/sshd/ssh_cipher_live_aes256_gcm_spec.spl`
  passes 5/5.
- `SIMPLE_LIB=src bin/simple test test/01_unit/os/apps/sshd/ssh_cipher_live_aes256_gcm_spec.spl --mode=interpreter --no-cache`
  passes 2/2.
- `SIMPLE_LIB=src bin/simple test test/01_unit/os/crypto/sha256_pure_simple_spec.spl --mode=native --no-cache --force-rebuild`
  passes 3/3.
- `bin/simple os build --scenario=rv64-ssh`
  passes and rebuilds `build/os/simpleos_riscv64_ssh_live.elf` through the
  Cranelift live wrapper path.

No QEMU run was attempted in this step.

## Update: 2026-06-15 — Live QEMU rerun: GCM tag divergence cleared, blocker moved off crypto

Fresh full live run (this session):

```
SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed \
SIMPLE_TEST_TIMEOUT=900 SIMPLEOS_RV64_SSH_LIVE=1 SIMPLE_OS_BUILD_BACKEND=cranelift \
bin/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl \
  --mode=interpreter --clean --timeout 900 --sequential
```

Capture: `doc/06_spec/tui/03_system/os/rv64_ssh_live_login_in_qemu_live.txt`
(serial: `build/os/rv64-ssh-live.serial.log`).

Alpha pure-vs-C comparison (dual-backend `mode=alpha runtime-first`) — all GREEN
on RV64, no fail-closed:

- X25519 public: `runtime len=32` + `pure len=32`, no `alpha mismatch`.
- X25519 shared: no `alpha mismatch`.
- Ed25519 sign: `alpha runtime done len=64` + `alpha pure done len=64`, no mismatch.
- KEX completes through exchange-hash + KDF; `newkeys sent` / `client NEWKEYS`;
  `cipher activated c2s_seq=0 s2c_seq=1`.

AES-256-GCM (runtime-only, no alpha guard) now correct **both directions** on RV64
— the "MAC incorrect" rejection in the 12:16 UTC update is gone:

- Server→client encrypt produced `encrypted s2c packet seq=0 len=68`.
- OpenSSH client **accepted** it: `kex_ext_info_client_parse: server-sig-algs=<ssh-ed25519>`
  (no `message authentication code incorrect`).
- Client→server: server received `recv encrypted live packet len=68 seq=0` and
  `decrypt result=0105...ext-info-in-auth@openssh.com` (valid plaintext).

Remaining blocker is **no longer crypto / GCM tag**. The encrypted recv-loop does
not progress past the first client encrypted packet (EXT_INFO) to the subsequent
`SSH_MSG_SERVICE_REQUEST` / userauth, so `auth ok` / `exec command=true` never
appear and the good-password probe times out (`openssh-good-exit=124`,
`good_seen=0 bad_seen=0`, `TEST FAILED`). Next work is the post-EXT_INFO
encrypted session read-loop in `ssh_session*.spl`, not AES-GCM.

### Alpha compare robustness (3 fresh ephemeral runs)

Re-ran the live lane 3× (each a fresh KEX / fresh X25519 + exchange hash). All
three are identical and green for the dual-backend `mode=alpha runtime-first`
crypto: X25519 `runtime len=32`+`pure len=32` (no `alpha mismatch`), Ed25519
`alpha runtime done len=64`+`alpha pure done len=64`, `newkeys sent`,
`cipher activated`. Per-run serial logs:
`build/qemu-memory-check/alpha-multirun/serial-run{1,2,3}.log`. So the
pure-vs-C parity for the asymmetric/hash crypto is robust across ephemeral keys,
not a single-run artifact.

### Why AES-GCM cannot join the live RV64 alpha compare (linking blocker)

Attempted to add a log-only dual-backend diagnostic that recomputes the first
server→client packet through a pure-only `aes256_gcm_encrypt_pure_only`
(skipping the `rt_tls13_aes256_gcm_encrypt` fast-path) and logs pure-vs-C
equality, always returning the runtime output. It compiles for the host
(`bin/simple check` 3/3) but the **RV64 baremetal link fails**:

```
ld.lld: error: undefined symbol: rt_array_new_with_cap
  referenced by os__crypto__aes256_gcm__aes256_key_expansion (+19 more)
```

Pulling any pure `os.crypto.aes256_gcm` function into the live image drags the
full pure AES path (`aes256_key_expansion` / sbox / rcon tables) into the link,
and `ld.lld` reports exactly **one** undefined symbol: `rt_array_new_with_cap`
(the allocate-with-capacity array extern, used ~10× across `aes256_gcm.spl`).

Important: this is NOT a general "no heap on baremetal" wall. `ssh_cipher_live`
itself uses `var x: [u8] = []` + `.push()` throughout in the same image and
links fine — so basic array ops are present; only the *with-capacity* variant is
unresolved. The fix is therefore likely **small** and should be checked before
anyone commits to a large freestanding helper:

- Option A: register/provide `rt_array_new_with_cap` for the baremetal RV64
  target (it is already a declared extern at `aes256_gcm.spl:16`).
- Option B: rewrite the ~10 `rt_array_new_with_cap(n)` call sites to `[]` + push
  (the pure-only probe even did `rt_array_new_with_cap(16)` then immediately
  `.push()`, i.e. trivially `[]`).

Only if both are infeasible does the already-noted freestanding RV64 AES-GCM
helper become required. The diagnostic edit was reverted;
`bin/simple os build --scenario=rv64-ssh` is green again.

#### Follow-up (2026-06-15): layer 1 fixed, layer 2 (SIMD) is the real blocker

Layer 1 done: `rt_array_new_with_cap` in `src/os/crypto/aes256_gcm.spl` was
replaced with a pure-Simple `_new_u8` helper (`[]`-based; `cap` is a growth hint
and all sites push). Host `check` OK, NIST-vectors KAT 12/12 + `aes_gcm_rfc_vectors`
pass, no interpreter regression. This is kept (the module's "suitable for
baremetal" header is now true).

But re-adding the pure-only AES diagnostic then exposed **layer 2**:
`ld.lld: undefined symbol: rt_simd_shr_u64x4`. `aes256_encrypt_block` is
SIMD-based (`use std.simd_crypto.{simd_aes_round, ...}`), and `std.simd_crypto`
references ~18 interpreter-only `rt_simd_*` intrinsics (add/and/or/shl/shr/xor
u64x4, clmul, aes_round, shuffle, vec2u64/vec4u64) with no baremetal-linkable
runtime symbols. GHASH/GCTR are already scalar, so the SIMD reach is only the
AES block cipher.

So `rt_array_new_with_cap` was NOT the sole blocker. A live RV64 pure-vs-C
AES-GCM compare needs ONE of: (a) a **scalar AES-256 block** in a SIMD-free
module (pure Simple; reuse nvfs `aes128_gcm.spl` scalar `_sub_bytes`/`_shift_rows`/
`_mix_columns`/`_add_round_key` + the already-scalar `aes256_key_expansion`), or
(b) baremetal-linkable `rt_simd_*` (runtime work). Both are larger than the
named fix and were deferred. AES-GCM already works bidirectionally on RV64 (tags
correct both ends), so this alpha compare is log-only verification, not a
functional blocker. The pure-only entry + diagnostic were reverted; tree is
green.
