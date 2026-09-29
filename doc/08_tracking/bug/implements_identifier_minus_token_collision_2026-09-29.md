# Contextual implements identifier collides with unary minus

## Actual failure and cause

The frozen 668 Linux full-CLI/configc diagnostics reject member/index/argument references to the existing composition locals named `implements`. Sites include `src/lib/nogc_sync_mut/composition/source.spl:280/288` and `codec.spl:336/340`. Evidence grouping is retained at `D:/dev/simple-wsl-recovery-20260928/linux-phase2-parser-errors-20260929.json`; no failed batch was retried by this lane.

The pure core `tokens.spl` defined both `TOK_KW_IMPLEMENTS` and `TOK_MINUS` as 61. `keyword_lookup("implements")` emitted 61. `parser_expr.spl` consumes kind 61 in unary/additive grammar, so `implements.len()` becomes a minus followed by an unexpected dot; call arguments similarly fail at a comma. Token-name lookup also mislabeled minus as implements, and the operator's requires-RHS classification incorrectly continued lines ending in this identifier.

## Language contract and narrow correction

The existing Rust lexer regression `lexer_tests_features.rs::test_mock_declaration` explicitly expects Identifier text `implements`. Its mock parser in `stmt_parsing/aop.rs` consumes that Identifier by text, making this a contextual word, not a globally reserved keyword. Existing library locals use that same identifier contract.

The fix is isolated in `D:/dev/simple-parser-implements-identifier-20260929`, branch `work/parser-implements-identifier-20260929`, base verified main `ba4dd5edd521f2b40584625da5671fd2faeae36d` (fetch shared by the case-arrow owner).

`keyword_lookup` now leaves implements as ordinary Ident=6. The legacy exported `TOK_KW_IMPLEMENTS` name is retained as an explicit alias of TOK_IDENT. Its misleading kind-name branch is removed; kind 6 remains human-named Ident. The core enum compatibility comment is updated. No expression grammar, library local, or case-arrow source is edited.

An owned-code search over src/test excluding vendor/target found no dedicated grammar consumer of TOK_KW_IMPLEMENTS: only the old keyword/name table, exports, and compatibility comment. Classification remains identifier classification, not keyword/operator classification. New consumers requiring contextual implements must inspect Ident text in the owning grammar, like the existing Rust mock parser.

## Compatibility and verification plan

MINUS=61 and every other operator/layout/literal wire code remain unchanged. Only the erroneous implements emission changes from 61 to existing Ident=6. Token field/tag/layout, AST layout and runtime ABI remain unchanged; no new enum variant is introduced. Retain the exported constant name, but its formerly incorrect numeric value is intentionally corrected. Producer/source-bound token/parser caches must regenerate rather than mixing old 61-coded identifier data with the corrected producer. Old frozen candidates and caches remain untouched.

Twelve authored unit cases cover lexical references, contextual mock word versus real minus, hard keywords, token/name/classification roundtrip, parameter/local/member/index/call/argument AST identities, unary minus, subtraction, newline behavior and malformed-input rejection. Mock declaration support in the pure frontend is not added or claimed by this lexical contract regression. A native fixture preserves the exact library identifier spelling and checks parameter/local/member/index/named-call/minus semantics.

High review precedes tests. A private one-thread bootstrap-only component can exercise these actual pure functions with the already reviewed b2d Rust seed. Preserve all assertions, suppress intentional negative diagnostics through parse_module_silent_checked, demand exact case/PASS markers, use no RSS cap and bounded time/disk/owned cleanup. A refreshed pure producer must later execute the native fixture; Rust-native execution alone is downstream evidence.

No tests/builds ran in this new lane. Its feature cycle budget is zero of three. Old unsigned semantic greens and exhausted memory feature cycles will not be rerun.

## Focused component finding: symbolic const initializer

Cycle 1 failed at link before assertions because the authored spec used the nonexistent inverse API token_kind_to_code. The corrected existing API is token_kind_code; production code was unchanged by that test repair.

Cycle 2 built with 2 modules compiled and 117 reused. Its actual run exited 1 at the first alias-equality check. Read-only ELF inspection proves TOK_IDENT at 0x495590 contains 6, while TOK_KW_IMPLEMENTS at 0x4956c0 contains 0 for the valid source initializer `const TOK_KW_IMPLEMENTS: i64 = TOK_IDENT`. The preceding MINUS=61 assertion passed. Producer was the reviewed bootstrap-only b2d seed SHA82ee7562b287b0fbe22256847a8916de7a88bc6f1a43a28275c12afedab167e1; source and input pins matched and no native baseline ran.

This is a concrete separate bootstrap-component symbolic-const initializer defect. Broader constant-alias behavior, other producers, and its internal compiler cause remain unverified; this token correction does not fix or claim to fix that general defect. Retained receipts are in D:/dev/simple-wsl-recovery-20260928/implements-focused-558976-20260929 and the actual artifact is /mnt/simple-bootstrap-6b2/implements-focused-8329-cycle2-20260929/parser-probe.

The compatibility name now uses explicit wire literal 6, matching the token table's existing numeric alias convention. Its intended value, identifier category and public name are unchanged from the reviewed design. Root approved this one-line correction using the actual ELF evidence. The final component cycle must skip the already-passed first MINUS=61 assertion and execute only the failed alias check onward plus unrun cases. All remaining assertions stay intact. Native fixture remains pending a corrected pure producer. The feature has used two of three cycles; no final execution PASS is asserted here.
