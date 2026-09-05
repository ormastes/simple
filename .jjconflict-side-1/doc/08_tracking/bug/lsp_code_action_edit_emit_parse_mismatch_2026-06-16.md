# Bug: LSP code-action edits never apply — emitter/parser mismatch (+ interp substring snag)

- **ID:** lsp_code_action_edit_emit_parse_mismatch_2026-06-16
- **Severity:** P2 (LSP quickfix/refactor actions surface but apply no edit)
- **Area:** lsp / app
- **Status:** RESOLVED 2026-09-02 (Defect 1 fixed in source; Defect 2 refuted by measurement; Defect 3 stays open under its own id -- see the RESOLVED section at the bottom). Was: open — root-caused, fix attempted and reverted (see Notes)
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

## Defect 3 — ROOT CAUSE (corrected): `}}` collapses in string literals
The attempted parser fix `_extract_emitted_range` appeared to mis-extract by one `}`. That
was a **red herring**: the bug is **`string_literal_double_brace_collapse_2026-06-16`** —
`{{`/`}}` inside ANY string literal collapse to a single brace. The probe inputs (built with
`}}` literals) were silently corrupted, so substring/loops operated on mangled data.
`text.substring` is NOT buggy. Crucially, the EMITTER has the same disease: `query_navigation`
builds the edit JSON with `}}` string literals, so Defect 2's "brace imbalance" is really this
collapse — the emitted JSON is genuinely missing closing braces and is malformed on the wire.

See [[string_literal_double_brace_collapse_2026-06-16]] for the minimal repro and the
build-via-concatenation workaround.

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

---

## RESOLVED 2026-09-02 — Defect 1 fixed in source; Defect 2 measured and refuted

Host aarch64-apple-darwin. Binary: `src/compiler_rust/target/release/simple` (Rust seed, 37,291,896 B, 2026-09-01 09:24). `bin/simple` on this host is the BOOTSTRAP cli (`simple-bootstrap 1.0.0-beta`, `compile`/`native-build` only) and answers `unknown command 'run'`, so it is NOT the lane used below.

**Defect 1 (parser reads flat keys nothing emits) -- FIXED.**
`_parse_code_action` (`src/lib/nogc_sync_mut/lsp/lsp_handlers.spl:728-747`)
now consumes the NESTED shape first: it extracts `newText` and the `range`
object via `_extract_emitted_range` (:700-726, documented against the
`edit.changes` shape `query_navigation.spl` actually emits) and rebuilds the
edit with `jo2(jp("range", range_obj), jp("newText", js(new_text)))`. The flat
`editLine`/`editCol` branch survives only as an explicitly-labelled
"Fallback: legacy flat-key emitters" at :748. Emitter and parser are aligned.

**Defect 2 (emitter brace imbalance) -- REFUTED by measurement, not by reading.**
The four `ep.push` lines at `query_navigation.spl:145-148` are unchanged, so
the static analysis in this doc still applies to the source text. Executing that
exact sequence prints:

```
{"range":{"start":{"line":3,"character":7},"end":{"line":3,"character":9}},"newText":"NT"}
```

which is balanced and well-formed. The reason is Defect 3: `}}` really does
collapse to a single `}` in a string literal on this tree (control measured in
the same program: `"x}}y"` -> `x}y` len 3, `"x{{y"` -> `x{y` len 3). Push 3's
trailing `}}` collapses to the single `}` that closes `end`, and push 4's
leading `}` closes `range`. The emitter was written against that behaviour, so
the "one closing brace too many" reading counts source characters the lexer
never emits. There is no imbalance on the wire.

Marking this record RESOLVED. **Defect 3 is a real, separate, still-open
language bug and is NOT closed here** -- it remains tracked as
`string_literal_double_brace_collapse_2026-06-16.md` (verified still open and
still reproducing, above). Note the coupling that record already names: fixing
the collapse WILL break this emitter, so `query_navigation.spl:147` must be
converted to a single `}` in the same change.
