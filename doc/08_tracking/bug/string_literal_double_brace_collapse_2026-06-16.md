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

## Reclassification (2026-08-25): works as documented — NOT a lexer defect

**Grammar reading.** The documented contract is that `{{` and `}}` are the
escapes for literal braces in EVERY double-quoted text literal, interpolated
or not (Python f-string semantics). Sources, quoted:

- `doc/02_requirements/compiler/parsing/syntax/parser_literals.md` (generated
  from `test/03_system/feature/usage/parser_literals_spec.spl` "escapes braces"):
  > **Example:** escapes braces
  > Given val s = "literal {{braces}}"
  > Then  expect s == r"literal {braces}"
- `src/compiler_rust/parser/src/lexer/strings.rs` (contract comment at
  `current_literal_raw`): "The documented language contract ... is that
  `{{`/`}}` collapse to a single literal brace in EVERY double-quoted text
  literal, interpolated or not — a briefly-landed 'keep raw when no
  interpolation' variant broke `.contains()` against single-brace text and
  was reverted here."
- `doc/08_tracking/bug/runtime_surface_spec_brace_escape_contains_red_2026-08-17.md`:
  option 1 of this record WAS landed (`d7213eb61742`), broke every
  `{{...}}` `.contains()` needle in the tree, and was reverted on 2026-08-18;
  that record closes with "`string_literal_double_brace_collapse_2026-06-16`
  remains decided the other way".
- `doc/07_guide/quick_reference/syntax_quick_reference.md` § "String
  Interpolation (Default)" shows `{expr}` interpolation only and is SILENT on
  brace escapes — it does not contradict the above; it just omits it.

Consequently the "minimal repro" above is the grammar working: `"x}}y"` IS
`x}y` (len 3), `"end}}"` IS `end}`, and `"{\"a\":{\"b\":1}}"` IS
`{"a":{"b":1}` — the first `}` closes nothing and is literal, the trailing
`}}` is one escaped brace. A nested-JSON tail needing two real braces must be
written `}}}}` (or built by concatenation / a raw `'...'` string). This is
option 2 of "Expected behavior"; option 1 was tried and rejected.

**Stale note corrected.** The 2026-08-09 triage above says the self-hosted
lexer "does not perform an unconditional `{{`→`{` / `}}`→`}` collapse". That
is true of `lexer_struct.spl::scan_string` in isolation but wrong for the
pipeline: the pure-Simple lexer keeps the token RAW by design, and the collapse
happens downstream in
`src/compiler/10.frontend/core/string_interpolation_expand.spl` —
`parse_string_interpolation_parts` skips depth-0 `{{`/`}}` as non-regions and
`decode_interpolation_brace_escapes` rewrites them (called from
`expand_string_interpolations`). Both compilers therefore agree.

**Evidence (2026-08-25, no source change under `src/`):**

- Seed probe (`bin/release/x86_64-unknown-linux-gnu/simple`, seed):
  `print("{\"a\":{\"b\":1}}}}")` -> `{"a":{"b":1}}`;
  `print("{\"a\":{\"b\":1}}")` -> `{"a":{"b":1}`;
  `val x = 1; print("v={x}}")` -> `v=1}`; `print("v={x}}}")` -> `v=1}`;
  `print("{{literal}}")` -> `{literal}`; `print("end}}")` -> `end}`;
  `print("x}}}y")` -> `x}}y`.
- Seed pinned test: `cargo test -p simple-parser double_braces_collapse_to_one_literal_brace`
  -> `test lexer::tests::fstring_brace_escape_tests::double_braces_collapse_to_one_literal_brace ... ok`.
- `test/01_unit/compiler/lexer_brace_escape_spec.spl` (+3 examples: `}}}}`
  nested-JSON tail, `}}}` triple, lone `}` after an interpolation):
  `Results: 11 total, 11 passed, 0 failed`.
- Self-hosted frontend, executed (not inspection):
  `test/01_unit/compiler/interpreter/pure_simple_frontend_interpolation_promotion_spec.spl`
  (+1 example driving `core_frontend_parse_reset` -> `expand_string_interpolations`
  on the nested-JSON literal and asserting the decoded `EXPR_STRING_LIT` value is
  `{"a":{"b":1}}`): `Results: 5 total, 5 passed, 0 failed`.

**Downstream.** `test/01_unit/lib/common/parsers_json_core_spec.spl` and
`test/01_unit/app/llm_caret/claude_cli_spec.spl` build their fixtures by
concatenation; that is a valid spelling under this grammar and needs no
rewrite (they may equally use `}}}}`). The LSP code-action emitter cited under
"Impact" must emit `}}}}` or concatenate — its bug record, not the lexer, owns
that fix.
