# svim Agent Task Breakdown

> Status: Tasks 1-4 have implementation evidence, but closure is blocked by
> focused `svim` core/log-mode failures found in the 2026-06-18 cleanup refresh.

## Cleanup Refresh (2026-06-18)

The earlier status text was stale: Tasks 2-4 now have implementation surfaces in
`src/app/svim/tui_shell.spl`, `src/app/svim/main.spl`,
`src/app/svim/simpleos_adapter.spl`, `src/app/svim/language_bridge_ext.spl`,
and `src/app/svim/language_port.spl`. Passing focused evidence exists for:

- `SIMPLE_LIB=src bin/simple test test/01_unit/app/svim/tui_shell_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/01_unit/app/svim/simpleos_adapter_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/01_unit/app/svim/svim_ext_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/01_unit/app/svim/language_port_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/01_unit/app/svim/multi_buffer_split_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/03_system/app/native_build/feature/svim_spec.spl`

The row is not done because two focused gates still fail:

- `SIMPLE_LIB=src bin/simple test test/01_unit/app/svim/core_spec.spl`
  reports `Passed: 21, Failed: 4`.
- `SIMPLE_LIB=src bin/simple test test/02_integration/app/svim_log_modes_spec.spl`
  reports `Passed: 3, Failed: 2`.

Next closure action: fix those core/log-mode failures and then rerun all focused
`svim` specs listed above before marking this plan done.

1. ~~Complete shared-core modal grammar, search repeat, text-object editing, quickfix traversal, and deterministic visual edit behavior.~~ DONE 2026-05-20
   - Added `*` / `#` (search-word-forward/backward) to parser and execute dispatch
   - Added `W`, `b`, `e` motions to `_svim_motion_name` and `_svim_apply_motion`
   - Added `i"` / `a"` text-object support in `_svim_text_object_bounds`
   - Added `_search_word` method (word-under-cursor extraction + forward/backward repeat)
   - Added `_svim_WORD_motion`, `_svim_word_back_motion`, `_svim_word_end_motion` helpers
   - Added `_svim_quote_object_bounds` helper for `i"` / `a"`
   - `:cn` / `:cp` already wired in `execute_commandline`; `n` / `N` already in parser
   - Visual edit behavior already deterministic (selection anchored at cursor on mode enter)
   - Current cleanup evidence shows `core_spec.spl` runs but fails
     (`21 passed, 4 failed`); fix those failures before closing the plan.
2. Keep the host shell thin while adding line-shell UX for multi-file sessions, open/save/search prompts, and command batching.
3. Add a SimpleOS-facing adapter shim that reuses `SvimSession` instead of duplicating edit logic.
4. Add a language bridge that converts parser diagnostics into shared buffer diagnostics and quickfix entries.
5. Run targeted `svim` tests and host-shell verification; track the remaining native spec-wrapper limitation separately from shared-core behavior.
