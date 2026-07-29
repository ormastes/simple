# std.common.json tokenizer rejects raw non-ASCII string content

**Status:** open — found while fixing \uXXXX decoding (same commit adds that fix).
**Severity:** any JSON document whose string content contains raw (unescaped)
non-ASCII UTF-8 fails to parse: `json_parse("\"café\"")` returns nil, while
`json_parse("\"cafe\"")` parses fine (verified empirically, spec-lane
interpreter, 2026-07-29).

## Mechanism

`json_tokenize` in `src/lib/common/json/parser.spl` walks the input with a
single `pos` used both as a `char_at(pos)` character index and compared
against `text.len()`, which is BYTE length. Any multi-byte character makes
char count < byte count, so after the closing quote the main loop keeps
iterating over a phantom tail (`char_at` past the last character), producing
an INVALID/trailing token and a nil parse.

This is the byte-vs-character index bug family
(`doc/08_tracking/bug/bracket_slice_byte_index_survey_2026-07-29.md`); note
the survey's "genuinely byte-safe" finding was about the JS-engine copy
(`src/lib/common/js/builtins/json.spl`, byte-slice based), not this file.

## Consequences

- `parse -> serialize -> parse` does not round-trip for non-ASCII: the
  serializer (correctly, RFC 8259 allows it) emits decoded UTF-8 raw, and
  the tokenizer then rejects its own serializer's output.
- Interoperability: JSON from tools that do not \u-escape non-ASCII (the
  common default) is unreadable.

## Suggested fix

Make `json_tokenize` byte-consistent like the JS-engine copy (byte slices
throughout), or track a character count for loop bounds. Keyword slicing
(`text.slice(pos, pos + 4)`) must use the same index space as `pos`.

## Test hook

`test/01_unit/lib/common/json/json_unicode_escape_spec.spl` has the
serialize-direction assertion and a comment pointing here; when this bug is
fixed, extend that spec with the full round-trip.
