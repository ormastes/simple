# Bug: `{{` / `}}` collapse to a single brace in ALL string literals (not just interpolated)

- **ID:** string_literal_double_brace_collapse_2026-06-16
- **Severity:** P2 (silently corrupts any literal building JSON/braces; root cause of broken LSP code-action edits)
- **Area:** language / interpreter (string-literal lexing)
- **Status:** open — minimal repro confirmed
- **Found while:** isolating the "substring off-by-one" suspected during reliable-mode P1/R3 (turns out NOT substring — see below)

## Summary
A doubled brace `{{` or `}}` inside a string literal is collapsed to a single brace,
**even when the literal contains no `{expr}` interpolation at all**. This silently drops
a brace from any string that legitimately needs a literal `}}` / `{{` (JSON objects, nested
maps, format templates), producing malformed output.

## Minimal repro (confirmed)
```simple
val a = "x}}y"
print a.len()        # => 3   (expected 4; the }} became } )
val b = "p{{q"
print b.len()        # => 3   (expected 4; the {{ became { )
val c = "end}}"
print c              # => "end}"   (one brace, not two)

# Control — concatenation preserves both braces:
val d = "end" + "}" + "}"
print d.len()        # => 5   (correct: "end}}")
```

## Impact / why it matters
- **LSP code-action edits never apply** (`lsp_code_action_edit_emit_parse_mismatch_2026-06-16`):
  `src/app/cli/query_navigation.spl` builds the edit JSON with string literals ending in
  `}}` (e.g. `"\"end\":{...}}"` then `"},\"newText\":..}"`). Those `}}` collapse, so the
  emitted JSON is missing closing braces → malformed → the client applies nothing. This,
  not the flat-key parser alone, is the deeper defect; the substring-based fix attempt
  was misled by probe inputs that ALSO used `}}` literals and were corrupted identically.
- Any JSON/template-building code using `}}`/`{{` literals is silently wrong.

## Expected behavior
Two reasonable options (decide by language design intent):
1. Only treat `{{`/`}}` as escapes **inside interpolated string literals** (Python f-string
   semantics); plain string literals keep `{{`/`}}` verbatim. OR
2. Keep global `{{`/`}}` escaping but **document it loudly** and provide/verify the escape
   round-trips (so JSON builders know to emit `}}}}` for a literal `}}`, or to concatenate).

## Workaround (today)
Build literal double-braces by concatenation: `"...}" + "}"` instead of `"...}}"`.
This is how the R3 emitter/parser fix should construct JSON until this is resolved.

## Related
- [[lsp_code_action_edit_emit_parse_mismatch_2026-06-16]] — the R3 blocker this root-causes;
  its "interpreter substring off-by-one" note is superseded by THIS finding.
- Prior art: brace handling in literals is a known sharp edge (LaTeX/JSON spec samples fail
  with "variable not found" when `{ident}` is read as interpolation).
