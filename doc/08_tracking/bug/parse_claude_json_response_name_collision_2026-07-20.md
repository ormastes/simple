# `parse_claude_json_response` likely global-registry name collision (2 modules, same name)

**Date:** 2026-07-20
**Severity:** medium
**Status:** open — hypothesis, not confirmed by isolated repro
**Found by:** whole-suite `test/unit/` triage campaign, `app/llm_caret`
cluster

## Symptom

`test/unit/app/llm_caret/claude_cli_spec.spl` fails 8 of ~39 examples on the
deployed binary (`bin/release/x86_64-unknown-linux-gnu/simple`, `bin/simple
test test/unit/app/llm_caret/claude_cli_spec.spl --no-session-daemon`), all
in the `parse_claude_json_response`/`parse_claude_stream_line` sections, with
fields coming back empty/zeroed instead of the parsed values:

```
✗ parses successful response
  expected  to equal sess-abc
✗ parses token counts
  expected 0 to equal 42
✗ parses error response
  expected end_turn to equal error
✗ handles missing model field
  expected : to equal
✗ handles multiline result content
  expected  to contain Line 1
✗ parses content_block_delta
  expected  to equal Hello
✗ parses message_stop
  expected  to equal end_turn
✗ parses message_start with model
  expected  to equal claude-sonnet-4-20250514
```

## Root-cause hypothesis

There are TWO functions named `parse_claude_json_response`, in two different
modules, with subtly different (incompatible) implementations:

```simple
# src/app/llm_caret/claude_cli.spl:174 (pub fn)
pub fn parse_claude_json_response(raw: text) -> CliResponse:
    ...
    val result_text = _extract_json_string(raw, "result")   # private helper (underscore)
    val model_text = _extract_json_string(raw, "model")
    ...

# src/lib/nogc_async_mut/llm/claude_cli.spl:103 (non-pub fn)
fn parse_claude_json_response(raw: text) -> CliResponse:
    ...
    val result_text = extract_json_string(raw, "result")    # different helper name (no underscore)
    val model_text = extract_json_string(raw, "model")
    ...
```

The spec (`test/unit/app/llm_caret/claude_cli_spec.spl`) has no visible
top-level `use` import for `parse_claude_json_response` — it appears to rely
on same-directory/sibling-module auto-resolution against
`src/app/llm_caret/claude_cli.spl`. If the interpreter's global symbol
registry resolves `parse_claude_json_response` to the WRONG module's
definition (e.g. the `lib/nogc_async_mut` one, whose `extract_json_string`
helper may not exist/behave the same as `_extract_json_string`), fields would
come back empty exactly as observed. This matches the known landmine class
"Function name collision (not just structs)" (see
`.claude/memory/reference_interpreter_dict_and_value_quirks.md` and
[[feedback-interp-struct-name-collision-global-registry]]): identically-named
functions across modules are not properly namespace-isolated under the
interpreter.

Not confirmed via isolated repro (would require tracing which module's
symbol actually wins, e.g. via a probe `print` in both function bodies and a
rebuild+run) — flagging as a hypothesis for whoever owns this module, since
confirming requires either an interpreter-internals trace or a source rename
experiment, both out of scope for this triage pass.

## Affected

- `test/unit/app/llm_caret/claude_cli_spec.spl` — 8 examples across
  `parse_claude_json_response - success/error/edge cases` and
  `parse_claude_stream_line` describe blocks (see symptom list above).

## Not the same root

`test/unit/app/llm_caret/server_spec.spl`'s 1 failure
(`"returns 501 for valid chat request"`, expects `501` but gets a `400
"messages required"` response) is unrelated — the request body sent by the
test (`{"content": "Hello"}`) never included a `messages` field, so a
strict-validation `400` may be the CORRECT current behavior for that
literal input, not a bug. Deciding whether this test's premise (endpoint is
still an unimplemented `501` stub) is stale requires knowing the current
`/v1/chat/completions` handler contract — left unclassified, not attempted as
a mechanical fix.
