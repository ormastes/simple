# `}}` in a string literal silently drops a closing brace for nested JSON (W-STR-BRACE-001 footgun) (2026-11-12)

- **Status:** OPEN — related: `string_interp_malformed_brace_warning_to_error_2026-11-09`,
  `interp_brace_literal_collides_with_string_interpolation_2026-07-03`
- **Severity:** P2 (silent data corruption of test fixtures / wire text; no error surfaced)
- **Area:** string literal lexing, `src/compiler/10.frontend/core/string_interpolation_expand.spl`
  (W-STR-BRACE-001), seed `parser/src/lexer/strings.rs`

## Symptom

`}}` is the escape for a literal `}` in double-quoted text, so a JSON object
nested one level deep and written as a plain literal loses its outer closer:

```
val b = "{\"p\":{\"x\":1}} tail"   # -> {"p":{"x":1} tail   (17 chars, invalid JSON)
val a = "{\"p\":{}}"               # -> {"p":{}}            (8 chars, kept whole)
```

Two inconsistencies make this a footgun rather than a documented rule:

1. The W-STR-BRACE-001 "not a valid interpolation, kept as literal text"
   region rule preserves `{}}` whole (case `a`) but the non-empty nested object
   (case `b`) still collapses `}}`, so authors who check one case and
   extrapolate get truncated text in the other.
2. The only signal is a WARNING. Under `bin/simple test` it is not surfaced as
   a failure, so a spec builds an unparsable JSON-RPC line and the failure
   shows up far away (`"error: status=..."` from the MCP stdio handshake, or
   `variable \`path\` not found` when the literal is passed to `step(...)`).

Found while writing `source_open_intent_view_spec.spl`: the stdio request line
`{"params":{"arguments":{...}}}` lost two braces; the fix there appends a
`CLOSE = "}"` constant per level.

## Repro

`test/01_unit/compiler/lexer_brace_nested_json_literal_spec.spl`
(`@tag:in-development`; seed-run 2026-11-12: executed=1 passed=0 failed=1 —
`a` parses strictly, `b` does not).

## Prevention (passing, seed-run 2/2)

`test/01_unit/compiler/lexer_brace_json_concat_prevention_spec.spl` pins the
closer-concatenation pattern (one `}` appended per nesting level) producing
strictly parsable JSON with the exact byte length.

## Fix direction

Owner decision needed between: (a) ratchet W-STR-BRACE-001 to an ERROR in the
seed and the pure-Simple lexer (tracked by
`string_interp_malformed_brace_warning_to_error_2026-11-09`) so the author is
told at compile time; (b) apply the region rule consistently so `{...}}`
keeps both closers whenever the `{...}` is not a valid interpolation. Either
way, `}}`-in-literal must never be silent.
