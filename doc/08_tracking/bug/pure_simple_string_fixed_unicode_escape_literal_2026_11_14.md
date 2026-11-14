# Fixed-width Unicode string escapes survive as literal text

Status: observed on pinned producer; current-source repair authored, independent
review and execution pending. No current-compiler execution or fix PASS claimed.

The facts-key probe compiled by producer SHA256
`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`
emits the six literal ASCII bytes spelling `\u0000` where the source author
intended a NUL separator. The producer is:

`/home/yoon/dev/simple-jit-free-s1-20261114/build/bootstrap/pinned-src/pinned-33bc5c6d1d80/build/bootstrap-jitfree-s1/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`

Retained evidence is `/tmp/aop-facts-framing-probe-20261114`, diagnostic fixture
commit `d0c520c4e1c4e8ccfa359779cf19a28d958a68b9`. Its
`attempt3-execution.sdn` and `run-attempt3.log` bind the producer, source and
binary. The printed frame is 367 bytes, with 14 literal escape spellings and
zero NUL bytes. Native SHA256 matches independent hashing of those printed
bytes (`0f5dd699e79ba1ff15bdcb3cbbb923bd57878d071cfce64145d478fda16771ed`).
The intended UTF-8/NUL golden remains
`d606ea14d13b8949daccd477e2caa960a2d09879144afe9b586c37dfb6a8eb9e`.
Earlier probe checks 1–13 passed, including the old matcher collision and its
framed-key repair; the golden failed with exit 14. No oracle is changed to match
the accidental encoding, and no additional probe has been run for this issue.

## Current-source boundary

Audited release revision: `7e769434990916a8d2143169b29f2807f3e6a41b`.
`src/compiler/10.frontend/core/lexer_struct.spl`, `CoreLexer.scan_string`,
branches on `esc == "u"`. Only the braced form is decoded. Otherwise it pushes
the backslash and `u` as separate literal fragments; the following digits are
then ordinary string content. Thus the currently inspected source still
contains the exact silent-preservation behavior. This is source evidence,
not proof that a newly built compiler reproduces the old producer result.

The Rust parser owner `src/compiler_rust/parser/src/lexer/escapes.rs` documents
and implements fixed-width and braced Unicode strings. However the staged
ADR-005 char-literal issue explicitly plans to narrow character escapes to the
shared braced form. Character policy must not be expanded incidentally by a
string repair. Historical reports also describe fixed-width forms as unsupported.
The parent authorized fixed-width support specifically for double-quoted
strings as seed/internal-producer compatibility, without widening character
syntax. Raw strings and doubled-backslash literals retain their meaning.

## Scoped repair

The double-quoted scanner now decodes exactly four hexadecimal digits after
an unbraced `u`, or one through six hexadecimal digits inside braces. It
rejects missing digits, missing closing braces, surrogates and values above
U+10FFFF. It does not combine surrogate pairs. A fifth digit after a fixed-width
escape is ordinary following text. Errors point to the original backslash,
including codepoint offsets and line/column after a non-ASCII source prefix.

Only the double-quoted branch calls the bounded decoder. The staged char
scanner and legacy single-quoted-string branch are unchanged. Decoded NUL
uses the existing `has_nul` path, so source token contents retain NUL without
publishing it through environment mirrors.

Seven authored scenarios in
`test/01_unit/compiler/frontend/lexer_double_quoted_unicode_escape_spec.spl`
call the actual CoreLexer owner and assert numeric UTF-8 bytes, literal
preservation, interpolation spelling, malformed rejection, coordinates and
the unchanged char gate. The native fixture
`test/fixtures/compiler/double_quoted_unicode_escape_native_probe.spl`
checks final compiled bytes and interpolation. Both remain **UNRUN**.

The required first execution is an exact current-lexer function projection,
under explicit bounded resource admission. That qualifies the exercised source
functions only. An updated compiler and the unchanged facts-key golden must
still execute before claiming repaired-producer behavior. No build is started
without the parent's concrete source/probe review.

## Required qualification

Use the actual lexer/parser owner and native compiled output, preserving the
independent golden. Cover embedded NUL and non-ASCII scalars, interpolation,
raw text and escaped-backslash preservation, and malformed/truncated/surrogate
escapes. Keep diagnostics separate from decoding acceptance and preserve the
staged character-literal contract. No syntax substitution in the facts-key
owner is a repair of this compiler boundary.
