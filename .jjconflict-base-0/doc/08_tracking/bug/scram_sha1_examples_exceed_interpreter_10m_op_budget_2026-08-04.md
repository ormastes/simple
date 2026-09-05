# SCRAM-SHA-1 RFC 5802 examples blow the interpreter's 10 M-operation budget once PBKDF2 actually runs

**Status:** OPEN
**Found:** 2026-08-04

## Symptom

Supplying the previously-missing `pbkdf2_sha1_bytes` (see below) makes this
spec's **reported** number worse, not better:

```
# BEFORE — pbkdf2_sha1_bytes did not exist
bin/simple test --no-cache test/01_unit/os/crypto/scram_sha1_rfc5802_spec.spl
# Results: 15 total, 7 passed, 8 failed
#   Error: semantic: function `pbkdf2_sha1_bytes` not found  (x3)

# AFTER — the function exists, so the examples now do real KDF work
bin/simple test --no-cache --timeout 800 test/01_unit/os/crypto/scram_sha1_rfc5802_spec.spl
# Results: 15 total, 3 passed, 12 failed
#   ✗ client-final text matches expected message with SHA-1 proof
#     execution limit exceeded: Execution limit of 10000000 operations exceeded
#   … 12 of these
```

Do **not** "fix" this by reverting `pbkdf2_sha1_bytes`. The 8 original failures
were `function not found`; the 12 new ones are the examples finally executing.

## Root cause (proven)

RFC 5802 §5 fixes the SCRAM-SHA-1 test vector at **i=4096**, so each example
runs 4096 HMAC-SHA-1 rounds. The tree-walk interpreter caps a run at 10 000 000
operations — `EXECUTION_LIMIT`, default 10 M, message emitted at
`src/compiler_rust/compiler/src/interpreter_state.rs:463`, settable via
`SIMPLE_EXECUTION_LIMIT` (`src/compiler_rust/driver/src/cli/init.rs:163`). One
PBKDF2-SHA-1 block at c=4096 exceeds that budget on its own.

`src/lib/common/crypto/pbkdf2.spl:19-25` already documents the sibling case for
SHA-256 ("~9.5 ms per HMAC call in interpreter mode … a single 32-byte block at
c=4096 exceeds the 60 s test-runner watchdog", filed as
`pbkdf2_interpreter_slow_c4096_2026-06-15.md`). This is the same wall reached
through the operation counter rather than the clock.

## The implementation itself is correct

Two independent oracles, both on `SIMPLE_EXECUTION_MODE=interpret` (never the
JIT — see `jit_corrupts_i64_array_returned_from_sha1_bytes_2026-08-04.md`):

1. **RFC 6070 vectors** (P="password", S="salt"), exact match:
   * c=1, dkLen=20 → `0c60c80f961f0e71f3a9b524af6012062fe037a6`
   * c=2, dkLen=20 → `ea6c014dc72d6f8ccd1ed92ace1d41f0d8de8957`
2. **The spec's own RFC 5802 reference values**, with the budget lifted:

   ```
   SIMPLE_EXECUTION_LIMIT=0 bin/simple test --no-cache --timeout 1800 \
       test/01_unit/os/crypto/scram_sha1_rfc5802_spec.spl
   ✓ client-first format is n,,n=user,r=<nonce>
   ✓ client-first length is 38 bytes
   ✓ client-final is byte-exact with computed ClientProof
   ✓ client-final text matches expected message with SHA-1 proof
   ✓ ServerSignature hex matches RFC 5802 reference
   ✓ ServerSignature is 20 bytes
   # 2 examples, 0 failures / 4 examples, 0 failures — 6 ran, 6 passed, 0 failed
   ```

   The three that previously died on the op limit are exactly the three that
   assert the RFC 5802 reference ClientProof and ServerSignature. They pass.

## Still unmeasured

That `SIMPLE_EXECUTION_LIMIT=0` run **did not complete**: output stops after the
6th example with no summary line and the runner reports
`Results: 1 total, 0 passed, 1 failed` / `FAIL` because it cannot parse a
summary from a truncated stream. The remaining 9 examples (server-side verify,
`ct_eq`, server-final decode) never emitted a verdict — they are **unmeasured,
not failing**. Treating that `FAIL` as 9 real failures would be a false red.

## Why not fixed now

Three candidate fixes, none safe to pick from a measurement lane:

* Raise or disable `EXECUTION_LIMIT` for crypto specs — needs a policy decision
  about which specs get the exemption, or the counter stops catching real
  infinite loops.
* Make the interpreter's HMAC-SHA-1 inner loop cheap enough to fit the budget —
  a real perf lane on `src/lib/common/crypto/{sha1,hmac}.spl`.
* Run these specs natively rather than interpreted — blocked by
  `jit_corrupts_i64_array_returned_from_sha1_bytes_2026-08-04.md`, which makes
  the JIT produce wrong digests, so the fast engine is currently unusable for
  exactly this code.

The third is the one that matters: until the JIT list-return corruption is
fixed, deliberately-expensive KDFs can only be exercised on the slow engine,
where they do not fit the budget.
