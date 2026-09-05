# Quantum-Resistant Script Signing (`wots-merkle-sha256-w16-h8`)

Hash-based signatures for repo scripts: WOTS (Winternitz one-time signatures,
w=16) under a Merkle tree of height 8, built from **SHA-256 only**. Security
rests solely on SHA-256 preimage / second-preimage resistance — no RSA/ECC
number theory, so Shor's algorithm gains nothing. Grover's quadratic speedup
against a 256-bit hash leaves ~128-bit post-quantum strength, the same margin
SPHINCS+/XMSS target. This scheme is a deliberately small, auditable cousin of
XMSS: ~350 lines of POSIX shell plus a pure-Simple verifier.

## Components

| Piece | Path |
|---|---|
| Shared shell library (the byte-exact contract lives in its header) | `scripts/trust/pq-sign-lib.shs` |
| Keygen | `scripts/trust/keygen-pq.shs` |
| Signer | `scripts/trust/sign-script.shs` |
| Verifier (shell, house verdict convention, `--selftest`) | `scripts/trust/verify-script.shs` |
| Verifier (pure Simple) | `src/lib/nogc_sync_mut/trust/script_signature.spl` |
| Spec / probe | `test/01_unit/lib/trust/script_signature_spec.spl`, `probe_script_signature.spl` |
| Committed trust root | `config/trust/scv_migration_root.pub` |
| INSECURE test fixture key (seeds public by design) | `test/fixtures/trust/selftest_key/` |

## Algorithm (fixed contract)

H = SHA-256, n = 32 bytes. WOTS w=16: 64 message nibbles + 3 checksum nibbles
= 67 hash chains. All hashes are domain-separated with an ASCII prefix:

- chain key: `sk[i][j] = H("wots-sk" || sk_seed || i:u32be || j:u16be)`
- chain step: `F(x) = H("wots-f" || pub_seed || x)`; `F^k` = k applications
- leaf: `leaf[i] = H("wots-pk" || pk_0 || … || pk_66)`, `pk_j = F^15(sk[i][j])`
- tree node: `H("node" || left || right)`; height 8 ⇒ 256 leaves; root = public key
- message: `m = H("msg" || exact script bytes)`; digits `b_0..b_63` are the
  nibbles of m high-first; checksum `C = Σ(15−b_j)`; `b_64..b_66` = 12-bit
  big-endian C
- sign: `sig_j = F^{b_j}(sk[i][j])`; verify: `pk_j = F^{15−b_j}(sig_j)` → leaf
  → climb the auth path (bit k of leaf index 0 ⇒ node is the left child) →
  must equal the trusted root.

Signature file `<script>.sig` is plain `key=value` lines: `alg`, `key_id`,
`leaf` (decimal), `sig` (67×64 hex), `auth` (8×64 hex, leaf level first).

## Keygen

```sh
sh scripts/trust/keygen-pq.shs --name scv-migration-root \
   --out config/trust/scv_migration_root.pub          # ~9 min, 275k hashes
```

Private state lands in `~/.config/simple/keys/<name>/` (mode 0700): `sk_seed`,
`pub_seed`, `next_leaf`, `key_id`, `root`, and a cached `tree` of all 511
Merkle nodes so signing needs no recomputation. Keygen **refuses** to
overwrite an existing key dir or `.pub` file. Only the `.pub` (alg, key_id,
root, pub_seed, created_utc, revocation_epoch) is committed.

## Sign and verify

```sh
sh scripts/trust/sign-script.shs --name scv-migration-root scripts/foo.shs
sh scripts/trust/verify-script.shs --public config/trust/scv_migration_root.pub scripts/foo.shs
```

Verify follows the house verdict convention (last stdout line):
`PASS — <n> file(s) verified` exit 0 / `FAIL — <k> invalid: <names>` exit 1 /
`ERROR — nothing was checked` exit 2 (0 files is ERROR; a missing `.sig` is a
FAIL). `--selftest` runs first unless `--no-selftest` and is fatal: sign→PASS,
flipped byte→FAIL, tampered sig→FAIL, wrong root→FAIL, leaf monotonicity,
exhaustion refusal, no-seed-leak.

From Simple: `use std.nogc_sync_mut.trust.script_signature.{script_signature_verify_file}`
returns `{valid, reason, leaf, key_id}`.

## THE stateful-key hazard (read this twice)

WOTS is **one-time** per leaf. Signing the same leaf twice reveals enough
chain intermediates that an attacker can forge signatures for other messages —
statefulness is the price of hash-only security. Consequences:

- **Never copy or restore the key dir** (no backups that can be rolled back,
  no shared filesystems, no VM snapshots). A restored `next_leaf` = reuse.
- The signer bumps `next_leaf` atomically (tmp+mv) **before** deriving any
  signature byte, and re-reads it to confirm; a crash burns a leaf, never
  reuses one.
- 256 signatures per key, then it is **exhausted** and signing is refused.
  Rotate before that.

## Rotation and revocation

1. Keygen a new name (`--name scv-migration-root-2`) → new `.pub`.
2. Commit the new `.pub`; re-sign the covered scripts with the new key.
3. Retire the old root by bumping `revocation_epoch` in the OLD `.pub` (or
   deleting it); verifiers pin key_id, so old signatures stop validating once
   the root file is removed/rotated. Keep the old key dir until every consumer
   has moved, then shred it.

## Why hash-based, in one paragraph

Every classical signature scheme in the repo's threat model (ed25519, RSA)
falls to a cryptographically relevant quantum computer via Shor. Hash-based
signatures reduce to nothing but the hash function: forging requires either a
second preimage of a Merkle node/leaf or inverting a chain value, both
generic-hash problems where quantum attacks are limited to Grover. SHA-256 is
already the repo's audited primitive (`src/lib/common/crypto/sha256.spl`,
pinned to FIPS vectors), so no new cryptographic dependency is introduced.
