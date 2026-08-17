# SECURITY: PASETO v4 tampered token signature is accepted instead of rejected

- **Date:** 2026-07-20
- **Area:** PASETO v4 implementation exercised via
  `test/unit/lib/crypto/paseto_v4_kat_spec.spl`
- **Severity:** critical — this is an authentication-bypass-shaped defect
  (a tampered token is not being rejected). No exploitability/impact
  analysis was performed in this triage pass; that judgment is out of scope
  here and should not be assumed either way pending investigation.
- **Status:** OPEN.

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/paseto_v4_kat_spec.spl --no-session-daemon
```

```
✗ tampered token signature is rejected
    expected true to equal false
```

1 of 14 examples fails (13 pass, including other sign/verify round-trips in
the same file — this is not a total break of PASETO v4 signing).

## Root-cause hypothesis

The failing assertion's message ("expected true to equal false") indicates
the test computed `true` (tamper detected / signature invalid) where the
spec's own logic expects `false` for a *correctly functioning* rejection —
or equivalently, that the verify call returned "valid" for a token the test
had deliberately corrupted. Not further root-caused in this pass (would
require reading the exact `it` block body and the PASETO v4 sign/verify
implementation under `src/os/crypto/` or `src/lib/common/crypto/` to
determine whether the bug is in signature verification, in how the test
corrupts the token, or in how the boolean is interpreted) — flagging with
high severity given the security shape of the symptom rather than
delaying.

## What NOT to do

Do not weaken or invert this assertion to force green under any
circumstances — this is exactly the class of check the "never soften an
assertion" rule exists to protect.

## Affected specs

- `test/unit/lib/crypto/paseto_v4_kat_spec.spl` (1 of 14 examples)

## Re-triage 2026-08-17 (content-classified, m9a_tests lane)

**Verdict: ALREADY-FIXED CANDIDATE (high confidence). The doc was filed when
"the primary source module [was] unlocated"; it is located now, and both the
PASETO verify path and the Ed25519 primitive underneath it are real.**

### The module the doc could not find

`src/os/crypto/paseto.spl`. Its v4.public verify path does enforce the
signature — the check is present and its failure is fatal, not advisory:

```
683:    if not ed25519_verify(pk, m2, sig):
```

built on the PAE-encoded message the sign path produces (`603: val sig =
ed25519_sign(sk_seed, pk, m2)`), imported at line 27 from
`os.crypto.ed25519.{ed25519_sign, ed25519_keypair_from_seed, ed25519_verify}`.

### The primitive is a real RFC 8032 verifier, not a stub

`src/os/crypto/ed25519.spl:444` `fn ed25519_verify(public_key: [u8], message:
[u8], signature: [u8]) -> bool` implements the full §5.1.7 procedure, and every
step that can reject actually rejects:

- `455-458`: length gates — `signature.len() != 64` and `public_key.len() != 32` return false
- `472-473`: non-canonical S rejected (`_sc_is_geq_L(s_bytes)` -> false), backed by a real `_sc_sub_L` borrow check at `510-517`
- `480-493`: `k = SHA-512(R || A || M) mod L` over the actual message bytes
- `495-503`: the group equation `S*B == R + k*A`, compared in encoded form
- `519-528`: `_bytes_equal` is a constant-time OR-of-XOR compare, not `==` on a prefix

This is the opposite of the failure mode the session brief warns about (a JIT
fallback swallowing a completely missing P-256 implementation): there is
nothing here that returns `true` on a path that skipped verification. A
tampered token changes `m2`, which changes `k`, which breaks the group
equation.

### The specs assertions are correctly oriented

`test/unit/lib/crypto/paseto_v4_kat_spec.spl` asserts rejection, not
acceptance — `_tampered_local_ok()` (line 184) and `_tampered_public_ok()`
(line 219) each flip one byte of a good token
(`good.substring(0, 15) + "X" + good.substring(16, good.length())`) and the
examples at lines 281 and 333 `expect(...).to_equal(false)`.

### Residual risk found while reading (NOT the reported bug)

`ed25519_verify` calls `ed_point_decode(public_key)` and `ed_point_decode(r_bytes)`
at lines 476-477 and **does not check the result for a decode failure**, though
its own docstring at 450-451 says "reject if invalid". That is a robustness gap
on malformed-key input, not a signature-acceptance bug on a tampered token, and
`src/os/crypto/**` belongs to another lane this session — recorded here as a
DIAGNOSIS for that owner, not fixed.

### Not runtime-confirmed

`bin/simple test test/unit/lib/crypto/paseto_v4_kat_spec.spl --timeout 1200`
did not reach a `Results:` line before this batch closed (host load average
81-133; sibling runs in this batch were SIGTERMed at rc=143, which per the
session brief is UNVERIFIED rather than failed). **Do not close this P1 on the
content evidence alone** — re-run the KAT spec on a quiet host and quote the
`Results:` line first. Given the code above, the expected outcome is GREEN.

## CORRECTION 2026-08-17 — the section above is WRONG; RED reproduced

**Retracting the "ALREADY-FIXED CANDIDATE (high confidence) ... expected outcome
is GREEN" verdict written earlier in this file.** It was a content-only
prediction and the run falsified it. Reading a verify path and judging it
"correct-shaped" is not evidence; this is the mistake the session brief warns
about from the other direction.

```
Results: 14 total, 8 passed, 6 failed
FAIL test/unit/lib/crypto/paseto_v4_kat_spec.spl
```

### The failure pattern: every ENCRYPT/SIGN passes, every DECRYPT/VERIFY fails

```
✓ 4-E-1/4-E-2/4-E-3: encrypt → exact token      ✓ 4-S-1/4-S-2: sign → exact token
✓ wrong footer is rejected                       ✓ v3.local / v3.public rejected by v4
✗ 4-E-1 decrypts to original payload             ✗ 4-E-3 decrypts to original payload
✗ correct footer allows decryption               ✗ 4-S-1 verifies and payload matches
✗ tampered ciphertext is rejected by BLAKE2b MAC ✗ tampered token signature is rejected
```

Every construction KAT reproduces the RFC vector **byte-exactly**, so ChaCha20,
BLAKE2b and Ed25519 *signing* are correct. All six failures are on consumption
paths.

### Split the row: the two tamper failures have DIFFERENT causes

**v4.public — FALSE RED, defective test fixture (fixed here).** Both tamper
helpers built their "tampered" token as
`good.substring(0, 15) + "X" + good.substring(16, good.length())`. For the
v4.public vector, index 15 is the `X` of `eyJkYXRh...` — **the substitution
replaced "X" with "X"**. Verified mechanically:

```
v4.public: char_at_15=X -> replaced with X   tampered == original ? True   (len 188 -> 188)
v4.local : char_at_15=A -> replaced with X   tampered == original ? False  (len 187 -> 187)
```

So `_tampered_public_ok()` handed `paseto_v4_public_verify` an **untouched,
perfectly valid token** and the example demanded it be REJECTED. Ed25519
returning `Ok` there is correct behaviour. **There is no v4.public
signature-acceptance bug** — the titles "tampered token signature accepted" is,
for the public arm, an artefact of this fixture. This inverts the usual vacuity
mode: instead of a false green it manufactured a phantom P1 auth bypass.

**v4.local — GENUINE, still RED.** The local tamper is real (`A` -> `X`), and
`_local_ok(tampered)` returned **true**: a tampered v4.local token is accepted,
so the BLAKE2b MAC is not being enforced on decrypt. Compounding it, the
untampered `4-E-1`/`4-E-3` vectors do NOT decrypt back to their known plaintext
and `correct footer allows decryption` fails. Read together: v4.local decrypt
returns `Ok` regardless of authenticity **and** recovers the wrong plaintext.
That is a real authentication bypass and remains the live P1.

Root cause is in the v4.local decrypt path of `src/os/crypto/paseto.spl`
(pre-auth MAC comparison + key/nonce split), **not** in `ed25519.spl`.
`src/os/crypto/**` belongs to another lane — DIAGNOSIS ONLY, no source edit
made.

### Spec changes (test lane scope)

Per `.claude/rules/testing.md` a correct-but-failing spec must stay RED; the
edits below only repair a fixture that was not testing what it claimed, and
**strengthen** the suite. The genuine v4.local failures are left RED.

- added `_flip_char_at(value, index)`, which substitutes a character guaranteed
  to differ (`"X"`, or `"Y"` when the original is already `"X"`), and routed
  both tamper helpers through it;
- added two guard examples — *"the tampered local/public token actually differs
  from the original"* — so a tamper fixture that silently degrades to a no-op
  fails loudly at the fixture instead of being reported as an auth bypass.

File: `test/unit/lib/crypto/paseto_v4_kat_spec.spl`. Post-fix `Results:` line
pending re-run; the v4.public rejection example is expected to go GREEN and the
v4.local ones to stay RED.

### Class sweep and fix-verification status (2026-08-17)

Swept `test/**` for the same fixed-character tamper idiom
(`substring(0, N) + "<char>" + ... substring(...)`). After the fix, the only
remaining matches in the tree are the explanatory comments in the two repaired
specs and the two class-detection specs. **No other negative-test fixture in
`test/` uses this idiom**, so the class is currently contained to the PASETO
KAT specs.

`_flip_char_at`s contract was verified against an independent implementation
of the same string semantics (`substring(start, end_exclusive)`), which
reproduced the defect and confirmed every assertion in the class spec:

```
index15 = X
naive_flip_15 == original ? True      <- the no-op that caused the phantom P1
naive_flip_14 == original ? False
flip15 != original ? True   flip14 != original ? True
flip("abXde", 2) = abYde    flip("abcde", 2) = abXde
length preserved: True
```

**Fix NOT yet confirmed by a spec run.** Two post-fix attempts on
`paseto_v4_kat_spec.spl` were SIGTERMed at rc=143 during session setup, before
reaching the spec, under a host load average of 81-133 — UNVERIFIED per the
session brief, not passing and not failing. The post-fix `Results:` line is
still outstanding; re-run on a quiet host. Expected: the two
`... actually differs from the original` guards GREEN, the v4.public rejection
example GREEN, and the four v4.local examples still RED (the genuine bug).

### Class-detection spec VERIFIED GREEN 2026-08-17

`test/unit/lib/crypto/tamper_fixture_actually_tampers_class_spec.spl`, run via
`sh scripts/resource/test-slot.shs bin/simple test <spec> --no-session-daemon --timeout 2400`:

```
rc=0
  ✓ silently degrades to a no-op when the target is already the replacement
  ✓ does mutate when the target differs from the replacement
  ✓ changes a character that is not already the replacement
  ✓ changes a character that IS already the replacement
  ✓ substitutes Y when the original is X
  ✓ substitutes X otherwise
  ✓ preserves length and every other position
Results: 7 total, 7 passed, 0 failed
```

This settles three things that were previously only argued from content:

1. The repaired spec syntax **parses and executes** — 7 examples ran, so the
   edit did not degrade the file to the `zero-examples` vacuity this batch hunts.
2. `_flip_char_at` behaves as specified, including the case that matters
   (`changes a character that IS already the replacement`).
3. The original defect is now pinned by an **executable** example rather than a
   comment: *"silently degrades to a no-op when the target is already the
   replacement"* passes, i.e. the old idiom demonstrably produced an identical
   token. The phantom v4.public "auth bypass" cannot silently return.

The same `_flip_char_at` source now used by `paseto_v4_kat_spec.spl` is
byte-identical to the verified copy, so the helper is proven; what remains
unverified for the KAT spec is only its own post-fix `Results:` line.

### Why the earlier runs died — earlyoom, not the repo monitor

Six consecutive spec runs returned rc=143 with no `Results:` line. Cause
identified:

```
/usr/bin/earlyoom -r 3600 --prefer ^(simple|rustc|cc1|cc1plus|lto1|collect2|qemu-system|ld) \
                          --avoid ^(claude|codex|gemini|node|sshd|dockerd|containerd|systemd|jj|git|bash)$
earlyoom[1479]: low memory! at or below SIGTERM limits: mem 10.00%, swap 10.00%
earlyoom[1479]: sending SIGTERM to process 211447 uid 1000 "simple": badness 999, VmRSS 6318 MiB
```

Host at 108/125 GB used, ~2 GB free, **zero swap**. `earlyoom` is configured to
`--prefer` killing `simple` and to `--avoid` the agent processes, so a spec run
is the designated victim while the agent driving it survives — which is why this
presents as an inexplicable compiler-shaped failure rather than an infra event.

**This is NOT the `kill_simple_monitor.shs` hazard from the session brief.**
That script is exonerated here: no kills logged since 06:30, `MIN_AGE_SECS` now
900 (the harmful 60 is gone), and its RSS cap is 24 GB — far above these
processes. The briefs 06:35 fix is holding; this is a second, independent
SIGTERM source with the identical rc=143/no-`Results:` signature.

**Workaround that worked:** `sh scripts/resource/test-slot.shs <cmd>
--no-session-daemon` completed where six direct invocations were killed.

## CORRECTION #2, 2026-08-17 — NO AUTHENTICATION BYPASS EXISTS. Spec is 16/16 GREEN.

**Retracting the "v4.local — GENUINE, still RED ... real authentication bypass"
finding written earlier in this file.** It was wrong. Running the same spec on
the same tree with `--no-session-daemon`:

```
sh scripts/resource/test-slot.shs bin/simple test \
   test/unit/lib/crypto/paseto_v4_kat_spec.spl --no-session-daemon --timeout 2400
rc=0
  ✓ 4-E-1/4-E-2/4-E-3: encrypt → exact token   ✓ 4-S-1/4-S-2: sign → exact token
  ✓ 4-E-1 decrypts to original payload         ✓ 4-E-3 decrypts to original payload
  ✓ the tampered local token actually differs from the original
  ✓ tampered ciphertext is rejected by BLAKE2b MAC
  ✓ wrong footer is rejected                   ✓ correct footer allows decryption
  ✓ 4-S-1 verifies and payload matches
  ✓ the tampered public token actually differs from the original
  ✓ tampered token signature is rejected
  ✓ v3.local rejected by v4.local decrypt      ✓ v3.public rejected by v4.public verify
Results: 16 total, 16 passed, 0 failed
```

**A tampered v4.local token IS rejected and a tampered v4.public token IS
rejected.** The P1 as filed does not reproduce on current source.

### Why the earlier `14 total, 8 passed, 6 failed` was not evidence of a bypass

My spec edit changed only the two tamper helpers (the no-op fix plus two guard
examples). It did **not** touch `_decrypt_4e1`, `_decrypt_4e3`,
`_footer_correct_ok` or `_verify_4s1_payload` — yet all four flipped from ✗ to
✓. An unmodified helper cannot be fixed by an unrelated edit, so the earlier
failures were **environmental, not cryptographic**. The remaining difference
between the two runs is the **session daemon** (the RED run used it; the GREEN
run passed `--no-session-daemon`).

That matches a hazard already documented in this repo, in the header of
`test/01_unit/lib/mem_infra/guard_backend_parity_spec.spl` (lines 101-108): a
`bin/simple test` served by an already-running daemon "ran under a stale
environment — and so did any shell it forked, since the shell inherits the
daemons environment too." A stale daemon serving stale module state explains
the exact observed signature: pure *construction* paths (encrypt/sign, which
only hash and encode) reproduced their RFC vectors byte-exactly, while every
*consumption* path (decrypt/verify, which resolves more of the library surface)
failed.

An isolation run — same fixed spec, daemon ENABLED — is in flight to confirm the
daemon specifically; see the parent report. Regardless of that outcome, the
GREEN run above is sufficient to state that **no bypass is reproducible today.**

### What remains true from the earlier analysis

Only the fixture defect, which is real and is fixed: the v4.public "tamper" was
a byte-for-byte no-op (`char_at_15` was already `"X"`), so that example demanded
rejection of a VALID token and could never have passed. Its repair is verified
by the two new `... actually differs from the original` guard examples (both ✓
above) and by the 7/7 GREEN class-detection spec.

### Status recommendation

**CLOSE as NOT-REPRODUCIBLE**, with the caveat that the original 2026-07-20
report may itself have been a stale-daemon false RED of the same kind — which
would make this doc a sibling of
`shellout_specs_target_refusing_production_wrapper_2026-08-17.md`: a
plausible-looking, security-shaped false RED produced by test infrastructure
rather than by the code under test.
