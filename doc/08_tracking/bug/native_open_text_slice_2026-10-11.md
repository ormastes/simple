# Native open-ended text slice loses its omitted endpoint

The source-extracted RC1 receipt parser compiled successfully with pure-Simple
producer `55544a213fafb05c82bd191a2878042865f33277efa7081bf1c107b8771c7bd2`,
but its valid document-summary assertions failed. A separate native primitive
probe compiled and ran with exit zero: `line[prefix.len():]` returned empty,
while direct splitting of the expected suffix returned all three correct parts.
The receipt grammar itself was not changed.

Evidence: `C:/dev/simple-rc1-native-parser-evidence/primitive-sdk23/result.json`
and its source, compile and run logs. This is diagnostic evidence, not admission.
The original expected-output list mistakenly expected prefix length 12; the
correct length of `SPL Doctest: ` is **13**, matching actual output. That historical
receipt is preserved unchanged. The empty suffix is a separate real failure.

The flat parser represents an omitted endpoint as a synthetic `IntLit(-1)`.
The flat-to-typed AST bridge passed it as an ordinary second `slice` argument,
losing the omitted-end meaning. MIR already handles the one-argument form by
computing the receiver length. The bridge now preserves that form. Both postfix
parser paths also accept `[:]`, using the same established omitted-end marker.
Explicit negative expressions retain their existing two-bound lowering.

The native fixture covers dynamic/literal start, closed range, omitted start,
omitted end, both omitted, empty tails, chained receivers and UTF-8 byte-offset
boundaries. The cycle3 diagnostic compiler passed the first fifteen numbered
text cases and a separate array-tail/full-copy collector. The original fixture
then failed because it assumed negative endpoints were relative to length.

Fresh old/new SDK probes both returned empty for literal, dynamic and
parenthesized explicit `-1` endpoints. This agrees with the legacy SDK slice
provider's clamping behavior; another runtime provider uses relative endpoints.
The portable regression now compares those bracket forms with the unchanged
explicit method `word.slice(1, -1)`, preserving provider behavior without defining
a new negative-index language policy. Historical failed receipts remain intact.

Evidence under `C:/dev/simple-rc1-native-parser-evidence`: `baseline-old` and
`baseline-new` establish the old/new comparison; `cycle3-trace` retains the
numbered text results. The remaining receipt parser failure is independently
localized to numeric count validation after successful slicing/tokenization.
The final portable fixture passed all 25 assertions with compile and run exits
zero: `cycle3-portable-fixture/native-open-slice/result.json`. Its source SHA256
is `c936a27f150b6ad110f13bc22edfa6d1f73481c5d652088eba76ceb86ece24a3`;
the exact produced executable SHA256 is
`0cd3fd56ef08863bb1baac49ec4d8f6767ad3e7239df9418d2308e7279a23db6`.
This focused regression passes; full compiler/release qualification remains
pending and the separate integer-conversion receipt blocker is still open.
