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

## CORRECTION #3, 2026-08-17 — the session-daemon attribution is WRONG too

**Retracting the "the remaining difference between the two runs is the session
daemon" explanation in CORRECTION #2.** The isolation run was performed: the
same fixed spec, same slot helper, daemon **ENABLED** (no `--no-session-daemon`):

```
sh scripts/resource/test-slot.shs bin/simple test \
   test/unit/lib/crypto/paseto_v4_kat_spec.spl --timeout 2400
rc=0
Results: 16 total, 16 passed, 0 failed
```

Identical to the daemon-disabled run. **The session daemon is exonerated** — it
does not cause the failures, and the `guard_backend_parity_spec.spl:101-108`
stale-environment hazard, while real in general, is not the mechanism here.

### What is established, and what is not

Established (three independent runs):
- The current spec is **16/16 GREEN with the daemon on AND off**. No PASETO
  authentication bypass is reproducible on current source. CORRECTION #2s
  headline verdict stands; only its causal explanation was wrong.
- The v4.public fixture defect was real and is fixed (7/7 class spec GREEN).

**NOT established: why the first run reported `14 total, 8 passed, 6 failed`.**
Two candidate explanations remain, and I could not separate them before this
batch closed:

1. **Host corruption of the run itself.** That run executed at peak degradation
   — ~94 concurrent `simple` processes, 108/125 GB used, ~2 GB free, zero swap,
   and `earlyoom` actively SIGTERMing neighbouring `simple` processes
   (`--prefer ^(simple|...)`). If a run under those conditions can report
   *wrong example outcomes* rather than merely dying, that is a serious finding
   in its own right and would mean **any RED collected during todays load peak
   is untrustworthy, not just the absent-`Results:` ones.**
2. **Something in the edit.** Considered and judged unlikely but not excluded:
   the four flipped examples (`4-E-1`/`4-E-3` decrypt, `correct footer allows
   decryption`, `4-S-1 verifies`) call helpers the edit never touched, so no
   direct mechanism is visible. An indirect one (example count/order changing
   from 14 to 16) is speculative.

A discriminating probe — the exact pre-edit blob (`79ad784175ab~1`) re-run on
todays quieter host — was launched; see the parent report for its outcome. If
that probe is GREEN, explanation (1) holds and the original RED was never real.

**Do not cite CORRECTION #2s daemon explanation.** It is superseded by this
section. The verdict (NOT-REPRODUCIBLE, close) is unchanged.

## CORRECTION #4, 2026-08-17 — DO NOT CLOSE. A real silent-wrong-result defect is here, and my spec edit MASKED it.

**Retracting CORRECTION #2s "CLOSE as NOT-REPRODUCIBLE".** That verdict rested
on the fixed spec being GREEN. The pre-edit spec was then re-run on a quiet host
via the same slot helper, and it reproduces **deterministically**:

```
git show 79ad784175ab~1:test/unit/lib/crypto/paseto_v4_kat_spec.spl   (pre-edit blob)
sh scripts/resource/test-slot.shs bin/simple test <that blob> --no-session-daemon --timeout 2400
rc=1
  ✓ 4-E-1 / 4-E-2 / 4-E-3 encrypt → exact token      ✓ 4-S-1 / 4-S-2 sign → exact token
  ✗ 4-E-1 decrypts to original payload               ✗ 4-E-3 decrypts to original payload
  ✗ tampered ciphertext is rejected by BLAKE2b MAC   ✗ correct footer allows decryption
  ✗ 4-S-1 verifies and payload matches               ✗ tampered token signature is rejected
  ✓ wrong footer is rejected                         ✓ v3.local / v3.public rejected
Results: 14 total, 8 passed, 6 failed
```

So **host degradation is excluded** (CORRECTION #3s explanation (1) is dead
too): the RED is deterministic on a quiet host, in both daemon modes.

### The actual defect is in the interpreter, not in PASETO

`diff` between the pre-edit and post-edit specs touches **only the two tamper
helpers**. But four of the six failing examples — `4-E-1 decrypts to original
payload`, `4-E-3 decrypts to original payload`, `correct footer allows
decryption`, `4-S-1 verifies and payload matches` — call `_decrypt_4e1`,
`_decrypt_4e3`, `_footer_correct_ok` and `_verify_4s1_payload`, which are
**byte-identical in both files and were never edited**.

**Editing one function changed the observable behaviour of other, untouched
functions in the same module.** That is a silent wrong result — precisely the
class this batch exists to find — and it is a compiler/interpreter defect, not a
cryptographic one.

The structural difference the edit removed:

```
OLD:  fn _tampered_local_ok() -> bool:
          val good = "<187-char literal>"          # long literal bound to a LOCAL VAL
          val tampered = good.substring(0, 15) + "X" + good.substring(16, good.length())

NEW:  fn _local_token_4e1() -> text:
          "<same 187-char literal>"                # returned directly, no local binding
```

i.e. a long string literal bound to a local `val` and duplicated across two
functions of one module, versus the same literal returned directly.

### My edit is a MASK, not a fix — treat it as such

The repair to the v4.public tamper fixture is independently correct and stays
(that no-op was real: `char_at_15` was already `"X"`). **But it also removed the
trigger for the interpreter defect, turning a true RED into a green.** That is
the worst possible outcome of a test-lane edit and is recorded here rather than
left to be discovered. Anyone reading `16/16 GREEN` on the current spec must not
infer that the underlying defect is gone.

### Consequences

- **The crypto verdict is INDETERMINATE, not clean.** With module behaviour
  corrupted, the ✗ on `tampered ciphertext is rejected by BLAKE2b MAC` cannot be
  read as an authentication bypass *or* as sound rejection. PASETO can only be
  judged once the interpreter defect is fixed.
- **This bug doc should be SPLIT**: a compiler/interpreter row (the real,
  reproducible defect) and a PASETO row (blocked on it).
- **Other specs may be silently affected.** Any spec with a long string literal
  bound to a local `val` and duplicated in the same module is a candidate, and
  the corruption is invisible — the examples simply return wrong answers.

### Isolation probe filed

`test/01_unit/compiler/interpreter/long_literal_local_val_aliasing_probe_spec.spl`
reduces the shape to pure text identities with no crypto. Result pending; if it
passes, the trigger is narrower than "duplicate long literal via local val" and
the paseto blob remains the only known witness — which must be stated, not
smoothed over.

Root cause is in the interpreter (`src/compiler_rust/**` / interpreter string
handling), outside the test lanes file scope: **DIAGNOSIS ONLY.**

### Isolation probe result — hypothesis FALSIFIED, trigger is narrower

`test/01_unit/compiler/interpreter/long_literal_local_val_aliasing_probe_spec.spl`:

```
rc=0
  ✓ the directly-returned literal has the expected length
  ✓ the local-val-bound literal has the expected length
  ✓ both binding styles yield the same text
  ✓ a split-and-rejoin of the local-val copy reconstructs the original
  ✓ keeps its header
  ✓ agrees with the direct copy at the index the old fixture mutated
  ✓ agrees with the direct copy on its final characters
Results: 7 total, 7 passed, 0 failed
```

**"Long string literal bound to a local `val` and duplicated in one module" is
NOT the trigger.** That shape is handled correctly in isolation, so the
mechanism proposed in CORRECTION #4 is wrong even though its *observation*
stands: editing one function still demonstrably changes the behaviour of
untouched functions in the paseto spec.

The probe spec is kept rather than deleted — it pins correct behaviour for a
shape that had to be ruled out, and a future regression in it would be
meaningful.

### A sharper reading of the failure set

Grouping the pre-edit failures by the helper they route through is more
informative than grouping by name:

| example | helper | verdict |
|---|---|---|
| 4-E-1 / 4-E-3 decrypt to original payload | `_local_payload` | ✗ |
| tampered ciphertext rejected | `_local_ok` | ✗ |
| correct footer allows decryption | `_local_ok_with_footer` | ✗ |
| **wrong footer is rejected** | **`_local_ok_with_footer`** | **✓** |
| 4-S-1 verifies and payload matches | `_public_payload` | ✗ |
| tampered token signature rejected | `_public_ok` | ✗ |
| v3.local / v3.public rejected | *inline `match`, no helper* | ✓ |
| all encrypt / sign KATs | *no decrypt/verify at all* | ✓ |

Two facts constrain any explanation: the **same** helper
(`_local_ok_with_footer`) both passes and fails depending on the example, and
the two consumption examples that bypass the `_*_ok` wrappers with an inline
`match` both pass. So the corruption is not a blanket "decrypt always fails" —
it is selective, and it involves the wrapper-helper call path.

A declaration-count bisect (pre-edit blob plus a single trivial unused function,
nothing else changed) is running to test whether the defect is sensitive to
module layout rather than to any specific edit content. Result pending.

## CORRECTION #5, 2026-08-17 — FINAL. Cause found; this row is BLOCKED, not closeable.

The declaration-layout bisect resolved it. Pre-edit blob **plus one trivial,
unused function** (`fn _zz_probe_unused() -> i64: 1`), nothing else changed:

```
(A) baseline            Results: 14 total,  8 passed, 6 failed
(B) baseline + 1 fn     Results: 14 total, 13 passed, 1 failed
```

**Five examples flipped ✗→✓ because an unused function was added.** They do not
call it, reference it, or share state with it. Example count is identical (14).
This is an interpreter defect, now filed separately as
`doc/08_tracking/bug/interpreter_declaration_layout_changes_unrelated_example_results_2026-08-17.md`.

### The complete, coherent picture

Three distinct things were tangled together in this row:

1. **Interpreter layout defect (REAL, P1, newly filed).** Module layout changes
   the results of unrelated examples. This produced five of the six original
   failures and is the reason this docs P1 looked like a crypto bug.
2. **The v4.public tamper fixture (REAL, fixed, verified).** `char_at_15` was
   already `"X"`, so the "tamper" was a byte-for-byte no-op and the example
   demanded that a VALID token be rejected. It is the **single remaining failure
   in variant (B)** — an excellent control, since it proves (B) is not
   "everything passes now" and that this defect is genuinely independent of the
   layout bug. Fixed via `_flip_char_at` plus two guard examples; verified by the
   7/7 GREEN class-detection spec.
3. **PASETO cryptography (NO DEFECT FOUND).** Every encrypt/sign KAT reproduces
   its RFC vector byte-exactly in every variant. Once the layout defect is
   dodged, `tampered ciphertext is rejected by BLAKE2b MAC` **passes** — the MAC
   is enforced. There is no evidence of an authentication bypass.

### Corrections to my own earlier sections in this file

- CORRECTION #2s "close as NOT-REPRODUCIBLE" — wrong; the RED was real and
  deterministic.
- CORRECTION #2/#3s session-daemon explanation — wrong; daemon exonerated.
- CORRECTION #3s host-corruption explanation — wrong; reproduces on a quiet host.
- CORRECTION #4s "long literal via local val" mechanism — wrong; probed 7/7 GREEN.
- CORRECTION #4s core *observation* — **correct** and now explained: editing one
  function did change untouched functions behaviour, because module layout is
  the trigger.

### Status

**BLOCKED on the interpreter defect. Do not close, and do not re-verify by
re-running this spec** — a green result in this file is not trustworthy while
layout perturbation can flip five examples. Re-assess PASETO only after
`interpreter_declaration_layout_changes_unrelated_example_results_2026-08-17.md`
is fixed. Severity of THIS row should drop from P1 (authentication bypass) to a
tracking row, since no bypass has been demonstrated.
