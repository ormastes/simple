# Lexer re-reads the path for an empty source, bypassing @when/@cfg preprocessing

Status: open

`lex_init_with_path(source, path)` (`src/compiler/10.frontend/core/lexer.spl`) replaces
an empty `source` with `file_read(path)`, and `current_core_source_get()` falls back to
`SIMPLE_BOOTSTRAP_LEX_PATH` when the inline slot is empty. Both run AFTER
`parser_init_with_path` preprocessed the caller's text, so any caller that hands `""` with
a real path parses the raw, unpreprocessed file. This caused
`native_worker_when_unstripped_2026-11-17.md` (worker placeholder surfaces).

The re-read exists as a defense against the old native "reads every source as empty"
failure, so it was not removed in that fix. Wanted: make the empty-source case fail
closed (diagnostic) or route the re-read through `_pp_preprocess_conditionals`, then drop
the disk fallback. Repro: parse `""` with a path whose file has a top-level
`@when(os="windows"):` -> `2:20: unexpected token in expression: ':'`.
