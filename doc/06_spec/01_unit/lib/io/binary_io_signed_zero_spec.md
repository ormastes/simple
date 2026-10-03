# IEEE signed-zero reconstruction

Authored acceptance manual for
`test/01_unit/lib/io/binary_io_signed_zero_spec.spl`. Tests are unexecuted;
this is not generated runtime evidence.

Four scenarios exercise the production bit decoders and inspect independently
specified IEEE bit patterns through the existing encoding boundary:

- Positive and negative f64 zeros retain their distinct sign bits.
- Positive and negative f32 zeros retain their distinct sign bits.
- Negative 1.5, minimum subnormal and infinity roundtrip in both widths.
- Negative NaN patterns remain NaN; payload preservation is not claimed.

This supports REQ-001 input fidelity. Join-key normalization may intentionally
equate signed zeros, while decoding must preserve the input value's sign.
All requested engines and runtime binding checks remain required.
