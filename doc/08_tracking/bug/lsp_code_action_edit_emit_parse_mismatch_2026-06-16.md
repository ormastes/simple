# Bug: LSP code-action edits never apply — emitter/parser mismatch (+ interp substring snag)

- **ID:** lsp_code_action_edit_emit_parse_mismatch_2026-06-16
- **Severity:** P2 (LSP quickfix/refactor actions surface but apply no edit)
- **Area:** lsp / app
- **Status:** open — root-caused, fix attempted and reverted (see Notes)
- **Found during:** reliable-mode plan P1 / R3 (doc/03_plan/compiler/reliable_mode/reliable_mode_plan.md)

## Summary
`textDocument/codeAction` returns actions whose **workspace edit is empty**, so accepting
a quickfix changes nothing. Two independent defects in the code-action chain, plus an
interpreter string-op snag that blocked the in-place fix.

## Defect 1 — parser reads flat keys nothing emits (CONFIRMED)
`src/lib/nogc_sync_mut/lsp/lsp_handlers.spl` `_parse_code_action` reconstructs the edit
only from flat keys `newText` / `editLine` / `editCol` / `editEndLine` / `editEndCol`
(the `if new_text != "" and edit_line != "":` branch). Grep confirms **nothing emits
`editLine`/`editCol`** — they appear only in that function. So the branch never runs and
the action returns `{title, kind}` with no `edit`.

Meanwhile `src/app/cli/query_navigation.spl` `query_code_actions` emits the **standard
nested** shape: `"edit":{"changes":{<path>:[{"range":{"start":{..},"end":{..}},"newText":..}]}}`.
The parser and emitter were never aligned.

## Defect 2 — emitter brace imbalance (ANALYSIS-derived; needs empirical confirm)
In `query_navigation.spl` the per-edit element is built from these pushes:
```
ep.push("{\"range\":{")
ep.push("\"start\":{\"line\":{rep.line},\"character\":{rep.column}},")
ep.push("\"end\":{\"line\":{rep.line},\"character\":{rep.column + (rep.end - rep.start)}}")
ep.push("},\"newText\":{emitter.encode_string(rep.new_text)}}")
```
Treating `{..}` interpolations as their values, push3 emits `"end":{..}}` (end-close **plus
an extra** `}`) and push4 starts with `}`, yielding `...}}},"newText":..}` — one closing
brace too many, so the element object closes before `,"newText"` (dangling key) with a
trailing unbalanced `}`. Expected element: `{"range":{"start":{..},"end":{..}},"newText":".."}`.
**Fix:** push3 should end with a single `}` (close `end` only); push4's leading `}` closes
`range`. Confirm by capturing raw `code-actions` output before changing (the empirical
capture attempt in the originating session returned no rows — invocation/trigger needs
re-checking: `bin/simple run src/app/cli/query.spl code-actions <file> <line>`).

## Defect 3 — interpreter substring/loop off-by-one blocked the fix (NEEDS ISOLATION)
The attempted fix added `_extract_emitted_range` to forward the emitted Range (rebuilt
with the request URI). Two extraction strategies both mis-extracted by exactly one `}` on
input verified by hand to be well-formed:
- a brace-depth counter over-ran (returned the Range **plus** the sibling `newText`);
- a between-markers scan (`substring` from after `"range":` to the next `,"newText":`)
  under-ran by one `}` (dropped the Range's closing brace).
Both point at a `text.substring`/while-loop-index subtlety in the interpreter, not a logic
error. Reproduce in isolation with a minimal `substring`-scan over a fixed string and
compare interpreter vs native. The fix was **reverted** rather than ship a malformed
`range`.

## Proposed fix (next session)
1. Fix Defect 2 (one brace in `query_navigation.spl` push3) and empirically confirm valid JSON.
2. Rewrite `_parse_code_action` to consume the nested `edit.changes` (extract `range` +
   `newText`, rebuild `documentChanges` with the request URI) — avoid the quirky
   `substring` scan; prefer a single shared serializer used by both CLI and LSP.
3. Add an LSP-level regression: a known fixable lint → `textDocument/codeAction` → assert a
   non-empty workspace edit with the correct range + newText.
4. Isolate Defect 3 and file separately if it reproduces outside this context.

## Repro
1. Open a `.spl` file with a fixable construct (e.g. `Foo.new()`).
2. Request a code action on that line; accept the offered quickfix.
3. Observed: no text change. Expected: the constructor rewrite applies.
