# Seed native-build rejects core_codegen.spl after #6481 (suspected quote in comment)

- id: seed_lexer_quote_in_comment_core_codegen_2026-11-04
- status: fix-implemented-verification-pending
- priority: P1

Reported by slice D: the Rust seed native-build on release/1.0.0 failed with an
f-string parse error in `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`
after #6481. The only new text #6481 added there is a `# @workaround` comment
(line 176) containing unbalanced single quotes (`Const's ... ('total enum ...')`);
the code lines (`_sffi_tuple_get_req`, `.unwrap()`) use forms already present
elsewhere. Suspected gap: the seed lexer tracks quotes inside `#` comments.
Fix: comment rewritten without quotes. Verify: seed native-build of core_codegen.spl.
