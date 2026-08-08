# A fabricated BLAKE2s KAT would have condemned a correct implementation

**Status:** FIXED (vector corrected in both spec copies; filed for the pattern)
**Found:** 2026-08-04
**Severity:** high — the wrong value was attributed to a named reference tool
(`hashlib.blake2s`), so the natural response to the red test is to "fix" the
hash implementation until it reproduces a digest no BLAKE2s ever produces

## Symptom

`test/01_unit/lib/crypto/blake2s_spec.spl` (and its legacy duplicate
`test/unit/lib/crypto/blake2s_spec.spl`) asserted:

```
it "65-byte input (one full block + 1 residual byte) 32-byte digest":
    # Python: hashlib.blake2s(b'a'*65).hexdigest()
    #   b4ee6ca1ad2ff2a4a8b45b51e01a7a3e5a77a55aae54e9fd0baad0f20c6bb2db
```

Against a fresh RFC 7693 implementation the run reported:

```
Results: 9 total, 8 passed, 1 failed
expected 045f8ae18932119bd051ac7ba5c73db59892055fad5c32f82d79a6543d92a497
      to equal b4ee6ca1ad2ff2a4a8b45b51e01a7a3e5a77a55aae54e9fd0baad0f20c6bb2db
```

Expected (per the comment): `b4ee6ca1…`. Actual: `045f8ae1…`.

## Root cause

The recorded vector is not the BLAKE2s-256 digest of 65 `a` bytes. Independent
confirmation from OpenSSL, which shares no code with this tree:

```sh
$ printf 'a%.0s' $(seq 1 64) > /tmp/a64.bin
$ printf 'a%.0s' $(seq 1 65) > /tmp/a65.bin
$ openssl dgst -blake2s256 /tmp/a64.bin /tmp/a65.bin
BLAKE2S-256(/tmp/a64.bin)= 651d2f5f20952eacaea2fba2f2af2bcd633e511ea2d2e4c9ae2ac0d9ffb7b252
BLAKE2S-256(/tmp/a65.bin)= 045f8ae18932119bd051ac7ba5c73db59892055fad5c32f82d79a6543d92a497
```

OpenSSL agrees with this tree's implementation on BOTH inputs, including the
64-byte one the same spec file already asserted and passed. Three further
authoritative vectors in the same file also pass unmodified: the RFC 7693 empty
digest (`69217a30…`), the RFC 7693 Appendix B `abc` digest (`508c5e8c…`), and
two keyed vectors from `blake2-kat.json`. The 65-byte entry is the only one in
the file that no reference implementation reproduces.

The 65-byte case is the file's only *multi-block unkeyed* vector, so it is
precisely the vector that pins the update-boundary compression. A wrong oracle
there is maximally expensive: it points the reader at the one code path the
other vectors do not cover.

`src/lib/common/crypto/blake2s.spl:150` (`blake2s_update`) is correct as
written — a full buffer is compressed only when the *next* byte arrives, never
on the 64-byte boundary itself, so the RFC's final-block flag lands on the last
block.

## Fix applied

Both spec copies now assert `045f8ae1…`, and the comment cites the reproducible
`openssl dgst -blake2s256` command instead of an unverifiable claim about what
some Python session printed.

## Why this is filed rather than closed silently

This is the fourth fabricated crypto test vector found in this tree (see
`fabricated_crypto_test_vector_in_bip39_kat`, the ed25519 KAT note, and the
ZUC-128 keystream entry). The shared shape: a hand-written digest attributed to
a named tool in a comment, with no command recorded that anyone could re-run.
A KAT whose provenance cannot be re-executed is not a known-answer test.
Vectors should either come from the standard's own appendix or carry the exact
command that regenerates them.
