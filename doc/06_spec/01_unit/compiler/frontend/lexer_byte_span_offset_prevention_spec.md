# Lexer UTF-8 byte spans across text length semantics

**Status: AUTHORED / NOT_RUN.** Five scenarios mirror `test/01_unit/compiler/frontend/lexer_byte_span_offset_prevention_spec.spl`. This complete lexer slice is extracted from PR7500 head95156319e2a onto release b37cca889050. It includes the cache and all state/reset wiring; the remaining original PR and its Rust/profile changes are not qualified or superseded by this manual.

The lexer accepts character positions but publishes UTF-8 byte spans. Its ASCII shortcut must compare byte length with character count, and its multibyte cursor must add byte widths. Both use the existing canonical `str_len` byte owner, so changing text `.len()` to code-point count does not silently change span units. Array `.len()` remains element count.

## Reconstruct tokens from real source

1. Lex the ASCII source and reconstruct every nonempty plain token (or quoted string token) from its span; require at least 18 checked tokens.
2. Repeat with multibyte literal and comment text; require at least 12 checked tokens.
3. Alternate ASCII, multibyte, ASCII and multibyte sources to detect a cached ASCII decision leaking across initialization.

The helper checks span ordering and actual reconstructed text. The prefix oracle independently walks source characters and counts their bytes; EOF bounds also use bytes.

## Anchor the oracle to known bytes

1. Prepare `aé中😀`, ASCII `abcd`, and empty text.
2. Require literal prefix arrays `[0, 1, 3, 6, 10]`, `[0, 1, 2, 3, 4]`, and `[0]` respectively.
3. Require the mixed fixture byte length to be 10.

These numeric expectations do not come from the production cursor or a second invocation of the same helper. They prevent the oracle and implementation from silently agreeing on character counts.

## Exercise the production cursor directly

1. Initialize the actual lexer with `aé中😀` and call its exported byte-offset owner for positions 0 through 4; require 0, 1, 3, 6, 10.
2. Move backwards to position 2 and require 3; request 99 and require the end clamp 10.
3. Reinitialize with ASCII and require offsets 4 and 1; then reinitialize with mixed text and require 10 again.

4. Save the mixed lexer state, initialize and save an ASCII lexer, then restore each state and require its own byte offsets.

This covers state take/install ownership, cached ASCII admission, the multibyte cursor, backward reset, upper clamping and source replacement. It does not claim all lexer error paths or performance budgets.

## Execution admission

No compiler, runtime or docgen execution was performed. After manager/owner coordination and an admitted immutable full runtime, run this exact five-case spec once under the campaign canonical process-tree watchdog with a 120-second outer cap and one native slot. Retain actual nonzero discovery, assertion outcomes, runtime/source/provider identity and lifecycle receipt; timeouts or zero discovery fail. Native replay and the complete PR's independent memory/performance obligations remain open.

Run admitted `spipe-docgen` for this exact spec with `--output doc/06_spec --no-index`; require complete documentation and 0 stubs. Authored manual presence is not generated-document or runtime PASS.
