# Post-quantum sig/KEM `list` retype batch — documented, not landed (2026-07-30)

Assignment (part 2): next crypto retype batch per the pass-9 fix order —
post-quantum sig/KEM files (`ml_dsa*`, `ml_kem*`, `slh_dsa_wots.spl`), same
rigor as the kafka fix (both-engine A/B, NIST KAT references where present
in-repo, per-file PROVED/INFERRED), watching the `src/os/crypto` W1006
landmine.

## Files in scope (from the pass-9 census, all under `src/os/crypto`)

```
39  ml_dsa.spl           (NIST FIPS 204 — ML-DSA signatures)
39  ml_dsa_sample.spl
36  ml_kem_kpke.spl       (NIST FIPS 203 — ML-KEM key encapsulation)
18  ml_dsa_ntt.spl
17  ml_kem.spl
9   ml_kem_ntt.spl
2   slh_dsa_wots.spl      (NIST FIPS 205 — SLH-DSA, WOTS+ leaf primitive)
```
160 `: list` sites total.

## Blocked: cannot produce a both-engine A/B proof for `src/os/crypto` with available tooling

Attempted the smallest file first (`slh_dsa_wots.spl`, 2 sites:
`base_2b`/`wots_checksum_digits_p`/`wots_msg_to_digits_p`/128s wrappers,
all holding base-16 WOTS+ digit values — homogeneous `i64`, mechanically
retyped exactly like the kafka fix). The retype itself compiled and ran
correctly, **but every standalone probe against an `os.crypto.*` function
hits the identical symptom already flagged for `hotp.spl` in the pass-9
census**:

```
[jit-fallback] unresolved external symbol 'base_2b': whole module dropped
to the interpreter (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1
to turn this into a hard error.
```

This is not file-specific — it reproduced identically for `base_2b`
(this pass) and `hotp_sha1_bytes` (pass 9), both under `os.crypto.*`. The
whole module silently drops to the interpreter for *any* top-level
standalone-script call into `os.crypto`, meaning **both my "default
engine" and "interpret" runs actually execute the interpreter** — there
is currently no way, with the probe methodology used throughout this
campaign (a standalone `.spl` script invoking `bin/simple`), to exercise
the true default/JIT engine against `os.crypto` code and therefore no way
to produce the both-engine A/B proof this batch requires. Landing a retype
here without that proof would mean shipping unverified changes into
post-quantum signature/KEM primitives on the strength of "the same
mechanical pattern worked elsewhere" alone — exactly the kind of
plausible-but-unverified change this campaign has repeatedly found to be
insufficient (e.g. pass 8's second, independently-discovered
`_b58_list_all_zero` bug that a first-pass "it compiles, ship it" fix
would have missed).

**Reverted the `slh_dsa_wots.spl` edit** rather than land it half-verified
(confirmed via `diff` against `git show HEAD:...` that the file is back
to its pre-edit state). No `src/os/crypto` file was changed this pass.

## W1006 landmine assessment (for whoever picks this batch up)

Checked whether these files already use `mut` (the standing rule is
"never add `mut` in src/os/crypto — W1006 demotion landmine"):
`slh_dsa_wots.spl` has zero existing `mut` usage, and the retype pattern
established across base58/sha256/kafka is a pure type-annotation change
(`: list` → `: [i64]`) that does not itself require adding `mut` anywhere
— the mutation shape of the existing code (`var out = []` /
`.push()`/`.append()`/`.get()`) is unchanged by retyping, only the
declared element type is. **The W1006 landmine is therefore likely not
triggered by this specific class of change**, but this was not confirmed
end-to-end for the larger files (`ml_dsa*`/`ml_kem*`) given the
verification blocker above took priority, and the HIR memory-safety
checker's exact capability rules for `[i64]` vs `list` receivers were not
audited. Flag, don't assume, for whoever does this batch.

## NIST KAT infrastructure already in the repo (confirmed present, for the eventual fix)

```
test/01_unit/lib/crypto/ml_dsa_44_kat_spec.spl
test/01_unit/lib/crypto/ml_dsa_65_spec.spl
test/01_unit/lib/crypto/ml_dsa_87_kat_spec.spl
test/01_unit/lib/crypto/ml_kem_512_kat_spec.spl
test/01_unit/lib/crypto/ml_kem_768_kat_spec.spl
test/01_unit/lib/crypto/ml_kem_1024_kat_spec.spl
test/01_unit/lib/crypto/slh_dsa_128s_spec.spl
test/01_unit/lib/crypto/slh_dsa_192s_256s_spec.spl
```
(each duplicated under `test/unit/lib/crypto/` — a second test-path root
seen elsewhere in this repo). These give real, in-repo KAT references for
whoever does the retype+verify pass once the `os.crypto` JIT-linking
question is resolved — per the campaign's standing discipline, they
should still be spot-checked against an independently-derived source
(e.g. the official NIST ACVP/KAT files) before being trusted as-is,
matching the fabricated-BIP39-vector lesson.

## Recommended path for a future pass

1. Root-cause the `os.crypto` "unresolved external symbol" JIT-fallback
   itself first — it blocks not just this retype batch but *any*
   both-engine verification of `os.crypto` code, which is a bigger
   problem than the `list` typing question (an entire module tier is
   currently unverifiable against the default engine via the standard
   probe methodology). This is plausibly a build/link-unit boundary
   issue (`os.crypto` may be built as its own object/archive not linked
   into ad hoc single-file script compiles) rather than a codegen bug —
   worth checking whether existing `os.crypto` specs (run via `bin/simple
   test` or a driver that links the full module set) get real JIT
   coverage even when a bare `bin/simple probe.spl` does not.
2. Once unblocked, retype in the same size order as tier 1 generally:
   `slh_dsa_wots.spl` (2, smallest, already drafted above — re-derive
   the edit, it was reverted) → `ml_kem_ntt.spl` (9) → `ml_kem.spl` (17)
   → `ml_dsa_ntt.spl` (18) → `ml_kem_kpke.spl` (36) →
   `ml_dsa.spl`/`ml_dsa_sample.spl` (39 each).
3. Use the in-repo KAT spec files above as the primary oracle, but
   independently spot-check at least one vector per file against an
   external, non-memory source before trusting it.

## Campaign status

Part 1 (crc32_table) landed this pass:
`doc/08_tracking/bug/kafka_crc32_table_64_of_256_fix_2026-07-30.md`,
commit `8d2161ec2de1eccbf41def0c0013a62077b76096`. Part 2
(post-quantum retype) is deliberately **not** landed — documented per the
assignment's own "document the needed change instead of editing if the
landmine applies" clause, generalized to the verification blocker found
here. The site-fix order from pass 9 is otherwise unchanged; this doc
narrows it with the specific `os.crypto` blocker any future pass needs to
clear first.
