# SimpleOS server credential zeroization gap

## Status

Open, but NARROWED 2026-08-17: the `text`-copy half is closed in source; the
compiler-resistant-zeroization and no-credential-bytes-in-artifacts halves are
still open. Still release-blocking for production credential handling.

## Problem

The host disk builder wipes the transient buffer used to read the bounded
server credential after copying it into the ephemeral acceptance image. The
SimpleOS server then reads `/SYS/SRVDB.KEY` into immutable `[u8]` and `text`
values. The current target runtime exposes no proven secure-zero operation for
those copies after `CapabilityTable` registration.

## Required closure

Provide a target-owned secret buffer with bounded read, non-copying policy
registration or an owned move, and compiler-resistant zeroization at shutdown.
Verify that logs, receipts, crash output, and retained images contain no
credential bytes. Until then, use only ephemeral acceptance credentials,
restrict the generated image, and securely destroy it after the reboot probe.


## Triage 2026-08-17 — DEFERRED, blocker recorded

Reviewed in the lines 32-46 backlog sweep. Not actionable from this session: not a defect to re-verify but a MISSING RUNTIME PRIMITIVE: the record asks for
a target-owned secret buffer with bounded read, non-copying policy registration
or an owned move, and compiler-resistant zeroization at shutdown. That is a
runtime + language design change, not a bug fix, and its acceptance criterion
("logs, receipts, crash output, and retained images contain no credential
bytes") requires a SimpleOS boot with image inspection -- unavailable here. The
stated interim mitigation (ephemeral acceptance credentials only, restricted
image, destroyed after the reboot probe) remains the correct posture.

Status unchanged. Recorded so future sweeps skip this in O(1) instead of
re-deriving the same blocker.

## 2026-08-17 — the immutable-`text` copy is eliminated

**What was actually wrong.** `load_server_policy`
(`src/os/apps/servers_user/main.spl`) already wiped its mutable `[u8]` buffer on
every path — that part of this record was already satisfied. The live defect was
one line: `val credential = bytes_to_string(bytes).trim()`. That materialised the
secret as an immutable `text` (two of them — the untrimmed and the trimmed) purely
because `CapabilityTable.register_authenticated` took `text`. `text` has no
zeroization surface, so those copies survived every `wipe_credential_bytes` call
and lived for the process lifetime, reachable from a core dump or a retained
acceptance image. The wipe was real; it was wiping the wrong thing.

**Fix.**

- `src/lib/nogc_sync_mut/database/server/capability.spl` gains
  `register_authenticated_bytes(capability, credential: [u8])`, which hashes the
  caller's still-owned mutable bytes with `sha256_u8_hex` and retains only the
  digest. Same fail-closed empty-credential refusal as the text path.
- `src/os/apps/servers_user/main.spl` gains `trim_credential_bytes`, a
  byte-domain equivalent of `.trim()` returning a fresh MUTABLE buffer, and calls
  the new registration. The credential now exists only as `[u8]` from the file
  read through digest registration; both buffers are wiped on every path,
  rejection paths included.

**Why the two registration paths agree.** `sha256_text(s)` is literally
`sha256_u8_hex(rt_text_to_bytes(s))` (`src/lib/common/crypto/sha256.spl:209-220`,
including the JIT fallback branch), so the digest stored from bytes is
byte-for-byte the one `authenticate_principal` computes from the wire credential.
This is the load-bearing claim and it is what the spec pins — a byte path that
merely "returned without error" would have locked the operator out of their own
database while looking green.

**Evidence.** `test/01_unit/lib/database/server/credential_zeroization_spec.spl`
(mirrored to `test/unit/lib/database/server/credential_zeroization_spec.spl`):

```
4 examples, 0 failures
SPEC FILE VERDICT: .../credential_zeroization_spec.spl declared>=4 executed=4 passed=4 failed=0 dropped=0
Results: 4 total, 4 passed, 0 failed
```

Sabotage arm — replacing `sha256_u8_hex(credential)` with a constant digest:

```
4 examples, 2 failures
SPEC FILE VERDICT: ... declared>=4 executed=4 passed=2 failed=2 dropped=0
Results: 4 total, 2 passed, 2 failed        (exit 1)
```

Reverted to green afterwards. The two arms that bite are the interchangeability
scenario and the survives-the-wipe scenario; the deny scenarios correctly stay
green under sabotage, which is why they are not the oracle.

## What remains open

1. **Compiler-resistant zeroization.** `wipe_credential_bytes` is an ordinary
   store loop with no reader afterwards — a dead-store-eliminating optimizer may
   legally delete it. Closing this needs a target-owned secret buffer whose wipe
   the compiler cannot elide (an explicit barrier or a runtime-owned
   `rt_secure_zero`), not a `.spl` loop. There is no owned secure-zero primitive
   in the tree today: `git grep -l 'zeroiz\|secure_zero' src` returns only
   vendored crates plus `src/compiler_rust/{compiler,runtime}/src/.../random.rs`.
2. **Artifact scanning.** No gate yet proves logs, receipts, crash output, and
   retained images contain no credential bytes.

Until both land, keep the existing mitigation: ephemeral acceptance credentials
only, restricted generated image, securely destroyed after the reboot probe.
