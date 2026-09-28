# SDN candidate structured issue mapping

Status: IMPLEMENTED, RUNTIME BLOCKED; NOT ADMITTED.

## Scope and dependency

Extends draft #1986 at `10462ad26b13559bc3def16961e166e5b1a574e3`.
The draft's prerequisite #1960 remains required. The accepted subset, shared
ParseProgramV2 grammar/action ownership, and legacy default route are unchanged.
The governing [Stage 4 plan](../03_plan/compiler/environment_optimized_dynamic_libraries.md)
requires valid, malformed, incremental, recovery, Unicode, indentation,
string/interpolation/custom-block, and facade acceptance matrices. This is
only the unsupported-input issue-mapping slice; full dialect parity and issue
parity with legacy `parse_with_issues` remain open.

## Design

`std.sdn.inline_candidate.sdn_inline_parse_checked_v2(source, limits)` returns
`Result<SdnInlineCandidateV2, SdnInlineIssueV2>`. Issues contain `phase`, `code`,
`start`, and `count`. Positions are zero-based UTF-8 byte offsets. `start = -1`
with `count = 0` explicitly means unavailable; an empty span at a nonnegative
position remains distinguishable. No line/column or semantic path is invented.

The tokenizer retains its current source-order preflight. It rejects the first
non-ASCII scalar with its complete UTF-8 byte extent (2, 3, or 4 bytes for valid
text), or a multiline separator (CRLF spans both bytes). This is an unsupported
Unicode diagnostic, not UTF-8 decoding/validation or Unicode grammar support.
A later unsupported character may still be reported before an earlier syntax
error because preflight precedes grammar. Unterminated quote spans run from the
opening quote through EOF. Unsupported tokens identify their full verified
source spelling. Token-capacity issues identify the next token. Source capacity
and invalid configuration have no location. Internal lexer source mismatches
have no trusted span.

The new typed lexer path feeds the same real tokenizer and shared VM exactly
once. The existing public parse and lexer APIs map typed errors back to their
original code strings. Integer-array callers therefore keep their API and
acceptance behavior. Program validation, VM, and semantic projection errors
retain their original codes and report unknown positions: the VM currently
exposes no failed token position, and projection currently returns text errors.
No second scan attempts to guess these positions.

## Focused verification

Four added public-API scenarios cover 2/3/4-byte Unicode after an ASCII prefix,
CRLF, unclosed quotes, unknown grammar/projection/configuration positions,
existing error-code compatibility, and successful committed output against
both the prior facade and independent legacy values. The original candidate
suite remains in place. These are executable specs, not runtime PASS evidence.

Attempted once from the isolated worktree:

`SIMPLE_LIB=src /Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple test test/01_unit/lib/structural/parse/sdn_inline_candidate_v2_spec.spl --mode=interpreter`

The self-hosted release runtime SHA-256 is
`2a59a9cbc17e7e078b2b4dbb44bad7f865a0aa201cbd21405059b412c6c033ba`.
It exited 139 immediately after discovery and cover-check, before assertions,
matching the baseline failure recorded by #1986. Log:
`/private/tmp/sdn-candidate-issue-spans-test.log`.
No seed fallback, commit, push, source-matched runtime pass, core/MCP pass,
performance result, or Stage 4 admission is claimed. Parent review and a
working source-matched runtime are required before acceptance.
