# Owner-scoped original lexer receipt

REQ-MC-008/B5 C2. Authored manual; runtime and generated SPipe evidence UNRUN.

Executable: `test/01_unit/compiler/frontend/lexer_reference_tokens_v1_spec.spl`.

1. Compare the new owner-scoped token receipt against the actual existing
   value/writeback lexer facade for primitive functions, selective aliases,
   both list delimiters, branches, strings and Unicode comments. Require
   equal token kind, original character/UTF-8 ranges, line/column and exact
   original spelling. The production path does not use that old per-token
   facade; it remains unchanged for existing callers.
2. Retain a receipt across a different scan and a repeated original scan.
   Require unchanged copied scalar coordinates/spellings. Empty source and
   comments-only source are valid empty token inventories.
3. Refuse exhausted/invalid capacity and invalid lexical source without
   returning a partial success. A subsequent valid scan must recover.

No mock lexer or claimed runtime/performance PASS is used. The new entrypoint
owns its local lexer and calls mutable methods in the declaration module,
preserving the existing imported-method ownership workaround.
