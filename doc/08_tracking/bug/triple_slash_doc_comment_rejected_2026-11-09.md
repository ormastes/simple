# triple_slash_doc_comment_rejected_2026-11-09 (P2, bootstrap)

Self-hosted stage2 (`stage2_new4.exe`) rejects
`src/lib/nogc_sync_mut/test_runner/sdoctest/discovery.spl:51` with
`unexpected token in expression: use # for comments`.

Root cause: the pure-Simple lexer (`src/compiler/10.frontend/core/lexer_struct.spl`)
deliberately turns `//` into an error token (kind 191) — Simple comments are `#`
only and `///` is not a doc-comment form (the syntax quick reference documents
none). Two stdlib files (`sdoctest/discovery.spl`, `ndarray/rt_alloc.spl`) used
`///`, which only the Rust seed tolerated.

Fix: convert those files to `#`; clarify the lexer diagnostic to name `//`/`///`
explicitly. Spec: `test/01_unit/compiler/lexer/lexer_slash_comment_spec.spl`
(red 1/3 -> green 3/3). Phase-4 WA-triple-slash can be dropped after landing.
