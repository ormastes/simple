# Frozen-array in-place mutation silently no-ops under the seed interpreter (2026-10-23)

Status: OPEN — seed-runtime defect; no fix landed. Worked around in
`test/01_unit/lib/database/codec/sqlcipher4_page_spec.spl` (copy-based
`_flip` helper, PR #4190) — revert that helper to the in-place form as the
fix's verification.

## Observed failure

The cipher-c page-codec spec's tamper helper originally mutated a fixture
byte array in place:

```
fn _flip(data: [u8], i: i64) -> [u8]:
    data[i] = data[i] ^ 0xff
    data
```

Under the Rust seed interpreter (x86_64-pc-windows-msvc, bootstrap
profile, 2026-10-23 build), the indexed store `data[i] = ...` on this
array SILENTLY DID NOTHING: the function returned the array with the
original byte intact, the 4 tamper vectors + 1 no-reveal test passed
against the UN-tampered ciphertext, and the scenario reported PASS — a
vacuous test. No diagnostic, no freeze error, no copy-on-write marker;
just a lost store.

Converting the helper to build a copy (`var out = data; out[i] = ...` also
lost the store; a push-built fresh array worked) made the tamper vectors
genuinely exercise the codec, and one of them then caught a REAL cipher-c
bug (wrong-AES-key guard accepted a tampered page) before #4190 merged.

## Why this is dangerous

Silent store loss turns red tests green. Any spec whose mutation step is
load-bearing but whose assertions are loose enough (or, worse, asserted on
a different object) will pass vacuously. The defect class is the same
family as the documented array-mutation projections issues
(`array_mutation_projected_receiver_types_2026-10-05.md`,
`aliased_array_mut_param_mutation_lost_interpreter_2026-08-06.md`) — but
those fail LOUD (build/type errors); this instance fails SILENT at
runtime.

## Repro

1. `<seed> test` a minimal spec: `var a: [u8] = [1,2,3]; a[1] = 99;
   expect(a[1]).to_equal(99)` where `a` originates from a frozen source
   (e.g. a function parameter re-bound locally, or an array returned from
   an extern/codec boundary). Parameter-direct and fresh-literal forms may
   behave differently — the cipher-c case was a spec-file-level helper
   parameter.
2. Under the 2026-10-23 seed the store is lost; under the pure-Simple
   runner (once self-hosted binaries catch up) verify the semantics the
   language actually specifies for frozen-source stores — erroring is
   acceptable; silently dropping the store is not.

## Next steps

1. Seed interpreter: locate the indexed-store path for `[u8]` with a
   frozen/immutable backing (Value::ByteArray shared backing) — the store
   likely writes to a copy or is dropped when the backing is shared, with
   no mutability check firing.
2. Decide specified semantics (error vs copy-on-write) and make the seed
   match, with a diagnostic if it errors.
3. Verification: revert `sqlcipher4_page_spec.spl` `_flip` to the
   in-place form; the 25/25 suite must stay green AND the tamper vectors
   must remain non-vacuous (assert the flipped byte read-back inside the
   helper itself so vacuity is caught by construction).
