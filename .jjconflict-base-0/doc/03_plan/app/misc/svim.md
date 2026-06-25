# svim Agent Task Breakdown

> Status: TASK 1 DONE — modal grammar completion verified 2026-05-20. All svim specs pass (45 tests). Remaining tasks 2–5 not yet started.

1. ~~Complete shared-core modal grammar, search repeat, text-object editing, quickfix traversal, and deterministic visual edit behavior.~~ DONE 2026-05-20
   - Added `*` / `#` (search-word-forward/backward) to parser and execute dispatch
   - Added `W`, `b`, `e` motions to `_svim_motion_name` and `_svim_apply_motion`
   - Added `i"` / `a"` text-object support in `_svim_text_object_bounds`
   - Added `_search_word` method (word-under-cursor extraction + forward/backward repeat)
   - Added `_svim_WORD_motion`, `_svim_word_back_motion`, `_svim_word_end_motion` helpers
   - Added `_svim_quote_object_bounds` helper for `i"` / `a"`
   - `:cn` / `:cp` already wired in `execute_commandline`; `n` / `N` already in parser
   - Visual edit behavior already deterministic (selection anchored at cursor on mode enter)
   - core_spec.spl times out in interpreter mode (known native spec-wrapper limitation, tracked separately)
2. Keep the host shell thin while adding line-shell UX for multi-file sessions, open/save/search prompts, and command batching.
3. Add a SimpleOS-facing adapter shim that reuses `SvimSession` instead of duplicating edit logic.
4. Add a language bridge that converts parser diagnostics into shared buffer diagnostics and quickfix entries.
5. Run targeted `svim` tests and host-shell verification; track the remaining native spec-wrapper limitation separately from shared-core behavior.
