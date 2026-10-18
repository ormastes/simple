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

## Retry3 correction

The annotation-only patch failed actual native retry3 with the same len/get
diagnostics. Native get constructs Optional<T>; crypto used it as T. The
subsequent compatibility repair uses fixed-position indexing and keeps the
nested declarations. See
`doc/08_tracking/bug/array_get_contract_drift_crypto_2026-10-18.md` for the
conflicting API contracts, exact trace, and workaround retirement gate.
Updated tests remain UNRUN. Earlier diagnosis above is historical and is
insufficient to explain or resolve the native failure by itself.

The scalar access follow-up also covers bit indices 0/1/29/30/60, empty input,
shift carries, and modulo integration. Existing get_bit callers prove n >= 0;
negative-n behavior remains unspecified. These additional cases are UNRUN.

## Native evidence boundary (2026-10-18)

The corrected source now has a real AArch64 relocatable-object PASS and a linked
Ed25519 example PASS against an independent five-line affine oracle. These do
not mark this SSpec file executed: its division, bit, carry and ladder scenarios
remain UNRUN because a qualified SSpec runner is unavailable. The preserved
get-contract probes also remain unresolved. Exact source/object/binary hashes
and local evidence locations are recorded in
`doc/08_tracking/bug/array_get_contract_drift_crypto_2026-10-18.md`.
