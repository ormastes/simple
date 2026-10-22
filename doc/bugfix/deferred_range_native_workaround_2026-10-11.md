# Deferred deserialization native range workaround

Issue: https://github.com/ormastes/simple/issues/3014

The C36 producer 5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235
compiled all seven HIR modules of deferred_deserialize.spl from source aeb2517fac0
but stopped in MIR on unsupported range indexing. Its diagnostic has no source
location; the first thrown site is therefore not established. Retained HIR names
the closure and authored source. The closure contains five range-index sites:
deferred_deserialize.spl:47 (byte array) and deferred_subst.spl:140,145,152,160
(text). No other range-index expressions were found in these seven modules.

The byte-array workaround copies the same half-open interval into a typed byte
array. Negative bounds count from the end, lower bounds clamp at zero, the end
clamps to length, and reversed/out-of-range intervals remain empty. This follows
the existing range interpretation in compiler_rust/compiler/src/interpreter/expr/
collections.rs:17 and :424. The Rust code was inspected only as semantic reference;
no Rust seed was used to execute or qualify the change. Existing field-length
validation, UTF-8 validation, returned offset, and error messages are unchanged.

The four text expressions use native-supported colon slices with the same
nonnegative half-open bounds. Both forms are byte-indexed, so multibyte surrounding
text and whole-identifier boundary checks remain intact. This does not implement
native range-index lowering. The issue remains open.

The standalone native fixture covers nonzero offsets, empty text, multibyte text,
invalid/truncated UTF-8, truncated declared fields, trailing bytes outside the
field, negative/clamped/reversed byte intervals, and identifier substitution.
It returns distinct nonzero exit codes on failures and prints a PASS line only
after the checks. No native result is claimed yet. Manual HIR/MIR/real-object
qualification and fixture execution are required before the full build.

The temporary copy remains linear in field length and allocates one destination
array as the original slice did. Push growth may change allocation constants;
this patch makes no measured performance claim.
