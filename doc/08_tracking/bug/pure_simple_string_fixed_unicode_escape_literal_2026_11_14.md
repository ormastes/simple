# Fixed-width Unicode string escapes survive as literal text

Status: source repair independently reviewed; actual lexer projection passed
nine groups and failed one inherited provider group. Full execution remains
nonpassing. No repaired-compiler or full fix PASS claimed.

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

## One authorized actual-function execution

Source repair commit: `c1a5b77c74d`. The independently reviewed projection is
`/tmp/simple-unicode-escape-lexer-probe-20261115`, fixture
`4d5dff0561ab4640a7e508b7ea88ae28c76be432`. It retains exact production scanner,
helper, character and raw-string methods and actual character/environment
providers. It omits unrelated token dispatch and does not replace decoding.
The source SHA256 is
`658ef92b0294d45280c93c56e732f67ebf9d92b104a9f3f05a1e4174e4b32e65`;
the resulting executable SHA256 is
`1f521a93ef0284cdcdfc885b2b16e48857bf2c6c052fb71a71d4c4ddd67cf649`.

Compile exit was 0; execution exit was **1**. Nine groups passed: NUL bytes,
ASCII/multibyte bytes, exact fixed width, braced scalars, raw/doubled backslash,
interpolation token spelling, malformed rejection, source coordinates, and
unchanged char grammar. The sole failing group preserved the independent
numeric oracle for provider control characters 11 and 12.

The actual `char_from_code_inline` provider special-cases those values with
fixed-width Unicode string constants. When compiled by defective producer
855f48d3, these constants retain the same literal-escape defect. This is an
additional bootstrap dependency, not permission to weaken that oracle. The
parent assigned a separate production-provider repair through its existing
byte-based scalar conversion owner.

`execution.sdn`, `scope.sdn`, `watchdog.sdn`, `command.sdn`, `compile.log` and
`run.log` retain the single attempt. Cgroup memory was 2 GiB, swap 0; available
memory at launch was 64,266,686,464 bytes, peak scope memory 751,144,960 bytes,
elapsed watchdog time 9.218 seconds, under a 90-second deadline. No failed or
green criterion was rerun. SSpec and the committed full native fixture remain
UNRUN; direct scanner evidence is not a full compiler test. An updated compiler
and unchanged facts-key golden must execute before producer qualification.

## Required qualification

Use the actual lexer/parser owner and native compiled output, preserving the
independent golden. Cover embedded NUL and non-ASCII scalars, interpolation,
raw text and escaped-backslash preservation, and malformed/truncated/surrogate
escapes. Keep diagnostics separate from decoding acceptance and preserve the
staged character-literal contract. No syntax substitution in the facts-key
owner is a repair of this compiler boundary.
