# Checker token-text interner survives file-scope teardown

ID: check_token_text_interner_survives_file_scope_teardown_2026-11-07
Status: fix-implemented-verification-pending. Runtime qualification UNRUN.

Source review found an independent lifetime obligation: checker file teardown could reclaim scope-owned token text while the process-global interner retained references used by a later lexer. Reset the canonical token-text interner after successful scope end and lexer-root replacement, before any subsequent token lookup. This is a source-contract finding; it is not proven to cause the observed For heap crash, which remains OPEN.

The repair landed in [PR7725](https://github.com/ormastes/simple/pull/7725), merge `673c5b65ce155c2f7be2d01e1091513801982333`, exact reviewed head `b7761e974ee5115b9e3017508bcadc92c598a0d8`. Astra independently reviewed the current-release reconciliation. `src/app/check/main.spl` changed only by the existing `core_token_text_intern_reset` import and reset/comment after successful end; current paused/retained failure logic was preserved. The older attempt-12 checker, its `reason_owned` condition, and the separate pending defer repair716 were not transplanted.

Authored production-facing regressions are `test/native_check_token_interner_teardown/main.spl` and its pinned `fixture.spl`. The probe explicitly pauses and promotes only its retained caller `[text]` graph, interns a second unretained spelling, ends the scope, churns allocations, rereads both spellings and invokes the real CLI. A future admitted runner must require exact CLI success JSON (`checked=1, files=1, errors=0, files_with_errors=0, coverage=semantic, semantic_complete=true`), final marker, native exit0 and entirely clean stderr; a local marker alone is insufficient.

Evidence scope:

- Source-only approval of v2 patch `555463d7` and exact PR head; canonical review packet `build/review/native-check-token-interner-teardown-candidate/v2/`. Exact-head review SHA256 `d4c063f70b6ded5df348bcbc11ef4529e670d918f27035d4ee43d2b71e01c39d` (`ASTRA-PR7725-REVIEW.md`).
- Current production Git blob `49673ac2a67d3b9828de89a8840d98dfa745f3cd`; fixture `bb3cd00837aa316a892d3ab717aeded538512720`; probe `cdfa9d8bc5248761eb96bbafee1132fef3c94711`.
- Source tests/native probe are UNRUN and runtime execution is NOT_ADMITTED. No native/compiler/performance pass is claimed. At source landing the returned CI workflows were in progress; source review is not runtime evidence.

WAIT_VERIFY: qualify this independent reset obligation only after explicit runtime/resource admission. Preserve the prior failed receipts and exhausted continuous iteration history; no automatic next build/run, prior-green replay, For-cause assertion or closure follows from registration.
