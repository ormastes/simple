# SSpec call and trailing-block nodes lose source spans

Status: open; source repair and native regression verification pending.
Requirements: REQ-TRC-002, REQ-TRC-007, REQ-TRC-012.

The production parser exists in the tracked compiler frontend. Source review
found that `try_parse_bare_ident_string_call` creates identifier/call nodes
with span zero, and `parse_trailing_colon_block_arg` creates lambda/block nodes
with span zero. These forms are needed for ordinary literal SSpec declarations.

An AST-based trace extractor cannot report an exact declaration location by
trusting these missing spans. Executing candidate registration callbacks or
guessing locations from line-prefix matches does not repair the AST contract.

Propagate the actual consumed token/block spans through these parser paths.
Verify nested literal SSpec declarations, escaped and Unicode text, comments,
and malformed/dynamic declarations using the production parser. Check that
source offsets identify the corresponding immutable input bytes. Keep the
issue open until native fixtures pass on the admitted Phase 3 compiler.
