# `extract_json_string` drops the escaped-quote tail only when called cross-module — 2026-08-25

Status: OPEN (P2) — seed defect; `src/app/llm_caret/json_helpers.spl:131-155`
is correct and unchanged. Spec stays RED.

## Symptom

`test/01_unit/app/llm_caret/json_helpers_spec.spl` —
`Results: 41 total, 40 passed, 1 failed` (fresh seed from origin/main `684fadabcae`):

```
✗ extracts a string value containing an escaped quote
    expected say \ to equal say \"hi\"
```

i.e. the backslash at index 4 of `say \"hi\"` did not set `escaped`, and the
loop returned at the very next `"`.

## Discriminating probe

The function body of `extract_json_string` copied VERBATIM into the spec file
as a private helper passes the identical input; the imported function fails:

```
✓ inline extract        (verbatim copy inside the spec)
✗ module extract        expected say \ to equal say \"hi\"
✓ module extract plain  (no escapes — the imported function works otherwise)
```

Standalone `"a\\b"[1] == "\\"` is `true`, and an isolated `if/elif/elif`
chain over `rest[end]` behaves. So the `ch == "\\"` comparison only fails when
the literal `"\\"` lives in `json_helpers.spl` and the call crosses the module
boundary — consistent with the co-compile warning printed on every run
(`public function make_error_response has 2 co-compiled definitions with 2
differing signatures ((String,Int,String)->String vs (text,i64,text)->text)`),
i.e. a String-vs-text representation mismatch for escaped literals across
modules.

## Unblock condition

Seed: a `"\\"` literal compared against `text[i]` must be identical whether the
comparison is compiled in the importing module or the imported one. Re-verify
with `bin/simple test test/01_unit/app/llm_caret/json_helpers_spec.spl` — the
one example above is the reproduce; "module extract plain" is the similar-case
control that must stay green.
