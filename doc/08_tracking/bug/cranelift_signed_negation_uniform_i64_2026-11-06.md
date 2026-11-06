# Cranelift narrow signed negation mixes narrow zero with I64 storage

Status: focused repair verified; full compiler rebuild and admission pending.
Base: release/1.0.0, d456ae0d2302db554ecb011a001c8e4e2c1627aa.

## Requirement and cause

REQ-CRANELIFT-SIGNED-NEGATION: the self-hosted Cranelift backend must compile
negation of i8/i16/i32 values and preserve two's-complement signed width.
Ordinary negatives, zero and i64 operations must remain correct.

The adapter stores integer SSA values uniformly as I64, but unary negation
created its zero using the declared MIR type. An immutable Stage2 producer
rejected the real source fixture with five verifier errors, including:

    isub.i8: arg 1 has type i64, expected i8
    isub.i16: arg 1 has type i64, expected i16
    isub.i32: arg 1 has type i64, expected i32

The small `cranelift_integer_negation` owner now emits subtraction at storage
width and restores signed I8/I16/I32 through reduction and sign extension.
The adapter selects the signed narrow type and delegates to this owner.
Unsigned result normalization remains in its existing adapter owner; floating
negation remains on its existing IEEE sign-bit path.

## Real before/after evidence

Producer: immutable self-hosted Stage2 `compiler.snapshot`, SHA256
`43f9a6fc68ac232fcb3d28b0a28ada8fba5b04f5e16326e8f122d09208671c5f`.
Runtime: matching `bootstrap-opus-10/phase2-runtime-capsules/43f9a6fc...`,
`host-gpu` bundle, native aarch64 Cranelift backend.

Before: `source_repro.spl` (five assertions) failed native compilation, exit 1,
with the verifier errors above. Log: `/tmp/seed-next-audit-signed-unary-build.log`.

After: the immutable Stage2 compiled the corrected helper and a minimal
producer as three modules. This new native producer executed successfully,
used the exact helper to generate an AOT object, and reported 14 generated
comparisons. Clang linked that object; its native executable returned zero
failed comparisons. The cases cover each narrow minimum, +7, -7 and zero,
plus i64 widening and i64 minimum. This is execution evidence, not a source
substring assertion. See the companion native-evidence manual for commands.

Artifact SHA256 values:

- Producer: `2bf6d072d1b8303b9edde31eb8eb616b819579bf233c705302c38381671187a0`
- Object: `91637e6719fce7436c12074c843f53ac2fedd2df4cb483478eb7b94eff8c01ff`
- Native checker: `14b1d76862523f160e0fe5615d50ceacb7923ca4060a6ffbae08a64055afe924`

All after-proof frontend, HIR and native caches were explicitly private under
`/tmp/cranelift-negation-20261106/`. The original diagnostic supplied a private
native cache but used the candidate's default HIR cache; no frozen producer,
runtime capsule or live campaign was modified.

## Qualification limits

Focused native emission: PASS. Whole compiler verification: NOT QUALIFIED.
The full adapter/CLI has not been rebuilt, so the original source fixture must
be recompiled through the next compiler generation before closing admission.

There is no deployed/admitted full self-hosted CLI in this environment. The
available bootstrap compiler supports `compile` and `native-build`, not normal
`check`/`test`. Therefore compiler/lib/MCP/LSP checks, interpreter MCP stdio
integration, core runtime smoke and MCP native smoke remain unavailable.
The native helper producer does not satisfy those gates or constitute a
seed-to-Phase-3 qualification. Direct-env working/staged guards and executable
spec layout check are recorded separately and do not replace runtime gates.
