# SQLCipher4 boundary coverage gap plan — 2026-11-03

Base inspected: `d6c83048995e577ca6b2feb48dccc40b4eaa5a96` from origin/release/1.0.0.
Scope: test-only additions for the DevHub Messenger SQLCipher4 production codec.
No production crypto change. No release-readiness or 99% claim.

| Requirement | New scenario | Production owner / decision |
|---|---|---|
| REQ-CIPHER-BOUNDARY-001 | Binary secret yields two fixed key hex values | sqlcipher4_keys: both PBKDF2 stages and byte preservation |
| REQ-CIPHER-BOUNDARY-002 | 255, 256, 65536, 2^31, 2^32-1 HMAC values | sqlcipher4_page: all LE32 shifts and binary input ordering |
| REQ-CIPHER-BOUNDARY-003 | material sizes 0/79/81, closed/80, open/80 | _session_keys: closed gate, width gate, success continuation |
| REQ-CIPHER-BOUNDARY-004 | RNG returns 0/15/17 bytes | record encode: IV-length failure gate |

Existing discriminators are retained: unit keys spec has ASCII golden, empty
secret, salt widths, raw key and profile errors; unit page spec has wrong AES
and HMAC keys, plaintext-header rejection, page geometry, constant-time compare
functional outcomes and NIST CBC vector. Dense integration spec exercises
ciphertext/IV/tag mutations on pages 1/5/9, swap, cross-database and truncation.
Dense system specs exercise actual Messenger rooms/members/history/fetch,
including Unicode and overflow. No duplicate tamper or end-to-end cases added.

## Evidence and remaining work

- Python 3.13.15 / OpenSSL 3.0.21 independently computed fixed PBKDF2 and HMAC
  vectors. Inputs, output bytes, generator and provider are committed.
- 6 unit scenarios and 4 record-integration scenarios are authored, unrun.
- Typed key oracle asserts compare_evidence status; HMAC assertions compare
  all 64 output bytes. No self-derived Simple expected value or capture-only pass.
- Unit/record assertions require their exact typed error code; unexpected Ok
  yields an explicit `unexpected-success` string that cannot equal any oracle.
- No admitted runtime: native execution, docgen, zero-stub admission and
  sabotage runs are UNRUN. Branch hits and complete denominator UNMEASURED.
- Do not aggregate cases into a coverage percent. Primitive HMAC framing cases
  primarily discriminate arithmetic/serialization errors, not new branch hits.
- Outstanding instrumentation must include key helper native owner separately;
  sqlcipher4_keys currently calls rt_pbkdf2_hmac_sha512. Simple wrapper coverage
  alone cannot establish coverage of that native implementation.
- Unreachable CBC failure arms and zeroization failure arms need evidence and
  explicit accounting, never silent denominator exclusion.
- New binary KDF case: mutate either fixed key byte and require fail, restore
  and require pass. High-page-number cases: truncate LE32 to a byte and require
  fail. These sabotage checks remain planned, not executed.

Merge owner: root campaign coordinator. Final reviewer: Astra exact-commit
review. No new sidecar agents or builds are launched by this lane.
