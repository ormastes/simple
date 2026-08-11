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

## Re-verification / triage (2026-08-09)

Re-ran the exact minimal repro against current `bin/simple`
(`bin/release/x86_64-unknown-linux-gnu/simple`, seed):

```
val a = "x}}y"; print a.len()   -> 3   (still collapsed, expected 4)
val b = "p{{q"; print b.len()   -> 3   (still collapsed, expected 4)
val c = "end}}"; print c        -> "end}" (still collapsed, expected "end}}")
```

Still reproduces exactly as originally reported. Not a stale defect.

Root cause is in the Rust seed's string-literal lexer/interpolation scanner
(`src/compiler_rust/parser/src/lexer/strings.rs`), not in the pure-Simple
self-hosted lexer. Read the self-hosted brace-interpolation scanner at
`src/compiler/10.frontend/core/lexer_struct.spl` (`fn scan_string`, `{`
handling around line 884 and `fs_nested_string_may_open` at line 984): its
lookahead logic pushes each un-matched `{` (or `}`) as a single literal
character independently and does not perform an unconditional `{{`→`{` /
`}}`→`}` collapse — so this specific defect does not appear to reproduce in
the self-hosted lexer by code inspection (not independently confirmed by
execution — `bootstrap/stage3/simple` in this tree has no `run`/file-exec
subcommand available to test against, per this repo's current bootstrap
build).

Per this sweep's scope rules (no edits under `src/compiler_rust/**`), this
defect is left **OPEN / out of scope for this sweep** — the fix, if the
seed's behavior is confirmed as the sole reproduction site, belongs in
`src/compiler_rust/parser/src/lexer/strings.rs`. No source changes made.
