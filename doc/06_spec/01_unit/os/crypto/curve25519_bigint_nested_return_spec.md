# Curve25519 bigint nested return regression

Status: UNRUN. This is an authored manual, not generated execution evidence.

Requirement REQ-CRYPTO-NESTED-RETURN-001: producers of bigint collections
must preserve the inner list type so callers can index limbs and query length.

Source: `test/01_unit/os/crypto/curve25519_bigint_nested_return_spec.spl`.
Implementation: `src/os/crypto/curve25519_bigint.spl`.

The four cases assert quotient/remainder values including divisor-zero/one
branches, both field and coordinate swap branches, independently calculated
Montgomery ladder coordinates `(1, 0, 324, 36)`, and a 32-byte multi-limb
roundtrip. The existing bigint print probe only checks literal string lengths;
the RFC7748 suite has a real bigint base-point vector and remains unchanged.

Diagnosis: campaign1 row 9 reports unresolved `len`/`get` after reading an
element of a plain `list` returned by `_bi_divmod_i64`, `_bigint_cswap_pair`,
and `_bigint_ladder_step`. Their values are nested lists. `bigint_fe_cswap`
has the same incorrect outer-only declaration. Correcting their return types
to `[list]` retains the inner list shape, as already used in curve448. No
algorithm, cast, caller annotation, or compiler fallback is introduced.
This is a source annotation correction; compiler inference failure has not
been established. Existing scalar limb erasure is outside this narrow change.

Pending validation, coordinated by the parent: execute this spec with the
admitted self-hosted runtime and retry only failed campaign row 9 and its
affected closure. Existing green objects must be preserved. No full rebuild
or Rust seed fallback is authorized. Native success is not claimed here.
