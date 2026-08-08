# ssh_native_client — pure-Simple SSH CLIENT reusing the sshd protocol core

Lane: SSHCLI. Date: 2026-07-27. Status: **slice shipped, spec-proven, not yet
wired to a socket.**

## Why this lane exists

The roadmap framing ("blocked, multi-week, OpenSSH port") was wrong. A
9,576-line pure-Simple SSH **server** already exists at `src/os/apps/sshd/`,
wired to real KAT-verified crypto (`src/lib/common/crypto/`, `src/os/crypto/`).
What was missing on the client side was not the protocol — it was
**direction-asymmetric message handling and, critically, host-key pinning.**

## What already existed (checked before writing anything)

| Tree | Verdict |
|---|---|
| `src/os/apps/sshd/**` (9,576 lines) | Real server. Transport, curve25519 KEX, ed25519/rsa/ecdsa host keys, AES-GCM, channels. Reused. |
| `src/lib/*/io/ssh_sffi.spl`, `ssh_ffi.spl` | SFFI facade over `rt_ssh_*`. Not usable in-guest. Untouched. |
| `src/os/tools/net/_SshTool` (1,035 lines) | **A pure-Simple client already exists.** It reuses the sshd core, but: (a) it is socket-coupled — `rt_io_tcp_*` externs sit directly in `run.spl`, so no protocol step is testable without a live server; (b) it verifies the host-key SIGNATURE through `std.io.signature_sffi.verify_host_key`, an **SFFI/C** call (`rt_ed25519_verify`), not pure Simple, so it cannot run in-guest; (c) it has **NO known_hosts pinning at all** (zero matches for `known_hosts` in the tree) — it only checks that the signature matches the key the server just handed it, which is worthless against a man in the middle; (d) password auth only, pty+shell only, no `exec`. |

So this lane is complementary, not duplicative — but it does mean there are now
two client trees, and that must be resolved (next increment #1).

## Reuse vs new — module table

**REUSED VERBATIM from `os.apps.sshd` (no second implementation written):**

| Module | What is reused | Why it is direction-agnostic |
|---|---|---|
| `ssh_packet` | `ssh_put_u32/string/text/bool/byte/mpint`, `ssh_get_u32/string/text`, `ssh_packet_build`, `ssh_packet_read`, ascii<->bytes | The binary packet protocol and SSH string codec are identical in both directions (RFC 4253 §6). |
| `ssh_transport` | `ssh_parse_version_string`, `ssh_parse_kexinit`, `ssh_negotiate_algorithms`, `ssh_kex_uses_strict_kex`, `SshKexInit`, `SshAlgorithms` | The `SSH-2.0-` prefix rule, KEXINIT decoding and the negotiation function already take (client, server) proposals as arguments — it was already written direction-neutral. |
| `ssh_kex_core` | `ssh_kex_public_from_private`, `ssh_kex_compute_shared`, `ssh_kex_compute_exchange_hash`, `ssh_derive_keys` | X25519, H, and the A..F key-derivation letters are defined identically for both peers. |
| `ssh_kex_primitives` | `SshSessionKeys`, `ssh_build_ed25519_host_key_blob` | Blob format is a wire format, not a role. |
| `os.crypto.ed25519` / `sha256` / `curve25519` | `ed25519_sign`, `ed25519_verify`, hashing | Pure Simple, KAT-verified. Replaces the SFFI `verify_host_key` used by `_SshTool`. |

**NEW — `src/os/apps/ssh_client/` (each has no server counterpart):**

| Module | Lines | Why a client-side variant is genuinely required |
|---|---|---|
| `ssh_client_version.spl` | 176 | The client sends its banner FIRST and must tolerate an arbitrary informational preamble from the server before the ID string (RFC 4253 §4.2) — a server never skips a preamble, so sshd has no such code. Also adds the client-side hardening sshd does not need: 255-byte cap, control-byte rejection, empty-softwareversion rejection. The prefix/CRLF check itself delegates to the reused `ssh_parse_version_string`. |
| `ssh_client_kexinit.spl` | 104 | `ssh_build_kexinit` in sshd hardcodes the SERVER spellings `ext-info-s` / `kex-strict-s-v00@openssh.com` and the server's preference order. The client must advertise `ext-info-c` / `kex-strict-c-v00@openssh.com` and supply its own cookie. Decoding and negotiation are the reused sshd functions. |
| `ssh_known_hosts.spl` | 203 | **Entirely absent server-side — a server never verifies a host key.** Store parse/render, strict base64 (bytes, not text), and fail-closed verification. |
| `ssh_client_kex.spl` | 217 | The client BUILDS `KEX_ECDH_INIT` and PARSES `KEX_ECDH_REPLY`; sshd does the exact mirror. The client is the only side that VERIFIES a host-key signature over H. |
| `ssh_client_auth.spl` | 232 | The client BUILDS `SERVICE_REQUEST`/`USERAUTH_REQUEST` and PARSES `SERVICE_ACCEPT`/`SUCCESS`/`FAILURE`/`BANNER`/`PK_OK`; `ssh_auth.spl` is the mirror. |
| `ssh_client_channel.spl` | 268 | The client OPENS the channel and SENDS `exec`; `ssh_channel.spl` receives them. |
| `ssh_client_session.spl` | 305 | Socket-free state machine `(state, inbound) -> (state, outbound)`. Has no analogue: `ssh_session.spl` is 78 KB of socket- and PTY-coupled server session code. |

`src/os/apps/sshd/**` was **NOT modified**. No refactor of the server was
needed — the pieces worth reusing were already direction-neutral.

## Slice shipped

Transport (version + KEXINIT + packet) -> host-key pinning -> curve25519 KEX
with signature verification -> key derivation -> one auth method wired into the
state machine (password; publickey/ed25519 request builder implemented and
spec'd but not yet the default path) -> session channel + `exec` + stdout/stderr
+ exit status.

**Not in this slice, deliberately:** the encrypted record layer is not wired
(`ssh_cipher` AES-GCM exists in sshd and would be attached around the payloads
this state machine emits), no rekey, no PTY, no port forwarding, no agent, no
sftp, no RSA/ECDSA host-key verification (ed25519 only).

## Host-key verification behaviour (the security core)

- The only non-error outcome of `ssh_known_hosts_verify` is `Ok(true)`, and it
  is reachable only when host, algorithm, AND the full key blob match a stored
  entry byte for byte. There is deliberately **no `Ok(false)`** for a caller to
  misread as non-fatal.
- Unknown host -> `Err("unknown host key ... refusing to connect")`.
- Same host+algorithm, different blob -> `Err("HOST KEY MISMATCH ... possible
  man-in-the-middle, refusing to connect")` — reported distinctly from unknown.
- A malformed known_hosts line is a hard parse error; a store that cannot be
  read never degrades into an empty (= trust-nothing-but-also-warn-nothing)
  store. Base64 is strict — an invalid character is an error, not a skip,
  because a silently skipped character decodes to a *different* key.
- **Ordering is load-bearing:** `ssh_client_complete_kex` pins the host key
  BEFORE verifying the signature and before deriving any keys. A MITM key is
  refused before its (perfectly valid) signature is ever considered, and no key
  material is produced on any failure path.
- The session-flow spec asserts the consequence: on a MITM key the state machine
  never advances past `await_kexreply`, so the password is never sent.

## Test matrix

| Spec | Blocks / examples | Default lane | `SIMPLE_EXECUTION_MODE=interpreter` |
|---|---|---|---|
| `ssh_client_protocol_spec.spl` | 8 + 5 + 2 + 6 + 4 = 25 | 0 failures | 0 failures |
| `ssh_client_host_key_spec.spl` | 4 + 5 = 9 | 0 failures | 0 failures |
| `ssh_client_kex_inprocess_spec.spl` | 4 + 4 = 8 | 0 failures | not run (see below) |
| `ssh_client_session_flow_spec.spl` | 3 | 0 failures | not run (see below) |

**A/B honesty — the A/B is currently a no-op for these specs.** Every one of
the four files transitively imports `os.crypto.ed25519`, and at HEAD that path
cannot be JIT-lowered:

    [INFO] JIT compilation failed, falling back to interpreter:
           HIR lowering error: Unknown type: u128

So the "default lane" run and the `SIMPLE_EXECUTION_MODE=interpreter` run
execute the SAME engine — the interpreter — for all four files (confirmed by
grepping the fallback line out of each run's log). A genuine JIT-vs-interpreter
A/B of the SSH client is **not possible at HEAD**; it needs the `u128` HIR
lowering gap in the crypto tree closed first. This also explains the runtime
cost (~2 s per X25519, ~3 s per ed25519 operation, minutes per crypto spec) and
is the reason the specs are split into a fast pair and a slow pair. Recorded
here rather than glossed, because "green on both engines" would be a false
claim for this tree today.

Required oracles, all present and green:
- malformed banner rejected (5 distinct malformations, each its own example);
- KEXINIT negotiation picks curve25519-sha256 / ssh-ed25519 / aes256-gcm against
  the REAL `ssh_build_kexinit`, and fails closed with no common algorithm;
- unknown host key REFUSED; changed host key REFUSED as a mismatch;
- signature over H verifies with the right key, FAILS with the wrong key, and
  FAILS over a different hash;
- packet encode/decode round-trip including padding (length % 8 == 0, padding
  >= 4), truncated packet fails closed.

## In-process client <-> server: YES, it worked

`ssh_client_kex_inprocess_spec.spl` and `ssh_client_session_flow_spec.spl` drive
the client against the real sshd code with no socket:

- client encodes `KEX_ECDH_INIT` -> the REAL `ssh_parse_kex_ecdh_init` decodes
  it and returns exactly the client's Q_C;
- the REAL `ssh_build_kexinit`, `ssh_build_kex_ecdh_reply`, `ssh_build_newkeys`,
  `ssh_build_service_accept`, `ssh_build_auth_success` produce the server side;
- the shared secret and H come from the REAL `ssh_kex_compute_shared` /
  `ssh_kex_compute_exchange_hash`; the host-key signature is a REAL ed25519
  signature; the client verifies it and derives 32-byte c2s/s2c keys and 12-byte
  IVs that differ per direction.

Only the connection-protocol records (CHANNEL_OPEN_CONFIRMATION, CHANNEL_DATA,
exit-status, CLOSE) are encoded in the spec rather than by an sshd builder,
because sshd's builders for those live inside socket-coupled session code.
Their encodings are independently asserted in the protocol spec.

Honest cost note: the pure-Simple curve25519/ed25519 primitives are slow under
the current toolchain (~2 s per X25519, ~3 s per ed25519 op), so the two
crypto-heavy specs take minutes. That is why they are split from the fast ones.

## Deliberate-red calibration

Two reds, each applied ALONE and then reverted with a green re-verify.

**RED-1 — trust-on-first-use instead of refusing an unknown host.**
`ssh_known_hosts.spl`: the final `Err("unknown host key ... refusing to
connect")` replaced by `Ok(true)`.
- `ssh_client_host_key_spec.spl` -> `4 examples, 0 failures` (store block,
  unaffected) and `5 examples, 2 failures`:
  `✗ REFUSES an unknown host key`, `✗ REFUSES a key pinned for a different host name`.
- Note the other three in that block stayed green, which is the correct
  blast radius: exact-match, changed-key and empty-blob do not route through
  the unknown branch.
- Reverted -> `4 examples, 0 failures` + `5 examples, 0 failures`.

**RED-2 — accept any host-key signature.**
`ssh_client_kex.spl`: `if not ed25519_verify(...)` replaced by `if false`.
- `ssh_client_kex_inprocess_spec.spl` signature block -> `4 examples, 2 failures`:
  `✗ REFUSES a signature made by a different host key`,
  `✗ REFUSES a signature over a different exchange hash`.
  The two positive cases stayed green, as expected.
- The in-process KEX block's MITM/unknown cases stay green under RED-2, and that
  is itself the layering evidence: those refusals come from known_hosts pinning,
  which runs BEFORE signature verification, so they do not depend on the
  signature check at all. The two defences are independent.
- Reverted -> both blocks `4 examples, 0 failures`.

## Lint

`bin/simple lint src/os/apps/ssh_client/*.spl` was run. It found **one real
defect**, which is fixed, and a pile of **false positives from a linter bug**,
which are not.

**Real defect (fixed):** `ssh_base64_encode_bytes` accumulated the encoded
output with `out = out + <char>` inside the encoding loop — genuine O(n^2) on a
`text` accumulator. Replaced with a `[text]` parts array joined once, plus a
`_sshcli_b64_char` helper. Re-verified green: `ssh_client_host_key_spec.spl`
(4 + 5 examples, 0 failures, including the base64 encode->decode->original
round-trip over a 51-byte host key blob) and `ssh_client_session_flow_spec.spl`
(3 examples, 0 failures — it calls `ssh_known_hosts_line`, so it exercises the
changed encoder).

**Linter bug — COLL006 fires on integer loop counters (Deny level).**
Reduced to a 7-line file containing no string at all:

    fn count_to_ten() -> u64:
        var total: u64 = 0
        var i: u64 = 0
        while i < 10:
            total = total + i
            i = i + 1
        total

    build/sshcli_probe/coll006_probe.spl:2:0: error[COLL006]: string concat in loop (O(n^2))
    build/sshcli_probe/coll006_probe.spl:2:0: error[COLL006]: string concat in loop (O(n^2))
    Found 2 error(s), 0 warning(s)
    Lint failed in 1 file(s)

Root cause: `is_string_concat_assign_expr` in
`src/compiler/35.semantics/lint/collection_patterns.spl:368` matches ANY
`x = x + <non-array-literal>` inside a loop body — target IDENT, RHS binary
`+`, RHS-left the same IDENT, RHS-right not an array literal. **There is no
type check on `x`**, so every `i = i + 1` loop counter and every integer
accumulator matches. `COLL006` is then escalated to `LintLevel.Deny` at
`src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:57`, so it FAILS the
lint gate.

Suggested fix (NOT applied — `src/compiler/**` is outside this lane's owned
paths): require the assignment target to be `text`-typed before emitting
COLL006, or at minimum exclude integer-typed targets. Until then the lint gate
is unpassable for essentially any counted `while` loop in the repo, which is
worth confirming against other trees before anyone treats a COLL006 count as a
quality signal.

**Final tally after the real fix — 13 COLL006 errors remain, all verified
false positives:**

| File | errors | warnings |
|---|---|---|
| `ssh_client_auth.spl` | 0 | 5 |
| `ssh_client_channel.spl` | 0 | 4 |
| `ssh_client_kex.spl` | 1 | 4 |
| `ssh_client_kexinit.spl` | 2 | 2 |
| `ssh_client_session.spl` | 2 | 3 |
| `ssh_client_version.spl` | 3 | 7 |
| `ssh_known_hosts.spl` | 5 | 13 |
| `mod.spl` | (import-only, no summary) | |

Verified rather than assumed. Every COLL006 location resolves to a function
whose only self-assignment is an integer:

    _b64_char_value, ssh_base64_encode_bytes, ssh_known_hosts_parse,
    _sshcli_blobs_equal, ssh_known_hosts_status, _sshcli_find_crlf,
    _sshcli_slice, _sshcli_has_control_bytes, _sshcli_copy (x2),
    _sshcli_append, ssh_client_build_kexinit, ssh_client_kexinit_proposal

and a grep for every `x = x + ...` assignment in the whole tree returns 16
hits, all integers (`i = i + 1`, `i = i + 3`, `bits = bits + 6`,
`lines = lines + 1`, `lineno = lineno + 1`, `offset = end + 2`) — **zero**
`text` self-concatenations. The single `var _: text` declaration in the tree
(`ssh_client_channel.spl:212`) is assigned, never concatenated. So the one
genuine O(n^2) is fixed and none remains.

These are deliberately NOT worked around — the alternative would be contorting
correct byte-copy loops to appease a broken check, which is exactly the silent
normalization the repo rules forbid.

**Warnings** (not gate-failing, left as-is with the sshd tree's precedent):
`RAW-RT-001` (this tree declares `extern fn rt_bytes_u8_at` directly, copied
from `ssh_packet.spl` for baremetal safety — worth a shared std wrapper
decision), `FSK003` (bare `.to_u8()`/`.to_i64()` under the freestanding alias
bridge), `unnamed_duplicate_typed_args`, and `W0404` on
`ssh_client_channel.spl` (31 exported symbols vs a threshold of 30 — most are
protocol constants; worth splitting the constants into their own module).

## What a LIVE end-to-end gate would require

1. **Attach the record layer.** The state machine emits/consumes PAYLOADS. A
   live run needs `ssh_packet_build_with_block_size` + `ssh_cipher` AES-GCM
   wrapped around them, with sequence numbers and the NEWKEYS switchover. Note
   the sshd LIVE path (`ssh_cipher_live.spl`) is C-accelerated; the client must
   use the pure-Simple `ssh_cipher.spl` to stay in-guest-capable.
2. **A socket.** On the host, the existing `rt_io_tcp_*` externs used by
   `_SshTool`. **In-guest this is a hard blocker:** `rt_io_tcp_connect` is a NOP
   in the guest runtime (already recorded in the `ssh:` ledger note), so an
   in-guest client cannot connect at all until that lands.
3. **A real peer + evidence.** Client -> the existing SimpleOS sshd in the x64
   QEMU real-firmware gate (OVMF pflash, no `-kernel`), and client -> stock
   OpenSSH sshd for interop. Evidence bar: a transcript showing banner exchange,
   the negotiated suite, `known_hosts` accept, `exec` output and exit status.
4. **A negative live gate.** Point the client at a server whose host key is NOT
   in known_hosts and show the connection REFUSED before userauth. Without this
   the pinning is only proven in-process.
5. **Board runnability.** Per `.claude/rules/board-runnable.md`, the same client
   binary must run on the dev board, not only QEMU. Currently blocked by (2).
6. **Randomness.** The cookie and the X25519 ephemeral scalar are caller-
   supplied by design (so specs are deterministic). A live client must feed them
   from a real CSPRNG — `ssh_kex_random.spl` exists but sshd's own comments note
   `random_bytes` may fault on baremetal. This must be resolved before any live
   use; a fixed ephemeral key would be catastrophic.

## Ordered next-increment plan

1. **Resolve the two-client-trees problem.** Refactor `src/os/tools/net/_SshTool`
   to keep its socket I/O and delegate all protocol logic to
   `os.apps.ssh_client`, and drop its SFFI `verify_host_key` in favour of the
   pure-Simple `ssh_client_verify_host_signature`. This also gives `_SshTool`
   known_hosts pinning, which it currently lacks entirely. One owner per concept.
2. **Wire the record layer** (packet framing + AES-GCM + sequence numbers +
   NEWKEYS switchover) behind a `SshClientTransport` that the state machine
   drives, still socket-free at the seam so specs keep working.
3. **Make publickey the default auth path**, with `PK_OK` probe-then-sign, and
   load the user key from disk (`host_key_loader` already parses OpenSSH lines).
4. **known_hosts file I/O** — read `~/.ssh/known_hosts`, and an explicit
   user-confirmed append path for first connections (never automatic).
5. **Live host gate** against the SimpleOS sshd in QEMU, then against OpenSSH.
6. **In-guest gate** once `rt_io_tcp_connect` is real; then board evidence.
7. RSA/ECDSA host-key verification, rekey, PTY/shell, subsystem/sftp.

## Files owned by this lane

- `src/os/apps/ssh_client/{mod,ssh_client_version,ssh_client_kexinit,ssh_known_hosts,ssh_client_kex,ssh_client_auth,ssh_client_channel,ssh_client_session}.spl`
- `test/01_unit/os/apps/ssh_client/{ssh_client_protocol,ssh_client_host_key,ssh_client_kex_inprocess,ssh_client_session_flow}_spec.spl`
- the `ssh:` note line in `doc/08_tracking/os/production_status.sdn`
- this file
