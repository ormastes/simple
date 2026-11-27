# Runtime implementation source ratchet

`scripts/check/check-rt-dual-implementation-ratchet.shs` compares owned C and
Rust `rt_*` definitions. It is a lexical source census, not proof that a symbol
is linked or available on a particular target. Conditional implementation
bodies are counted without evaluating the preprocessor.

The C lane includes definitions in owned `src/runtime/**/*.c` and `**/*.h`.
Headers that contain implementation bodies are not merely API declarations:
an existing Linux header definition followed by a new non-Linux `.c` fallback
is the same primitive at both ends of a push. Header prototypes, calls,
comments and string literals do not establish an implementation. Runtime
`vendor/**`, `miniaudio.h`, `stb_image.h` and `stb_truetype.h` remain excluded.

The independent Rust census keeps its runtime and native provider roots;
neither Simple declarations nor a union of C and Rust names supplies a missing
implementation. No new symbol allowlist or frozen-baseline update is implied
by recognition of an owned header body.

Push admission uses `--rev TIP --baseline-rev BASE` and extracts both committed
trees with the same rules. New unpaired definitions remain fatal, including a
new `.c` implementation whose base contains only a header prototype. Frozen
baseline drift remains visible and retains its existing standalone policy.

Run `sh scripts/check/check-rt-dual-implementation-ratchet.shs --selftest` for
the extractor and committed-tree regression suite. It covers inherited header
implementations, prototype-only negatives, truly new unpaired C definitions,
third-party exclusions and the existing independent Rust cases. It does not
claim execution or cross-platform parity of any runtime primitive.
