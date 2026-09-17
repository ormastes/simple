# Seed string-literal length is one short when the value ends in `"}}`

Date: 2026-09-18
Host: Windows 11, Git Bash, seed built from merged main (post #1042/#1044)

## Symptom

A Simple string literal whose VALUE ends with the three characters `"}}`
(quote, brace, brace) reports `text.len()` one less than the true length, and
the final character is effectively truncated:

```
expect("\"x\"}}".len()).to_equal(5)              # seed says 4
expect("{\"a\":\"x\"}}".len()).to_equal(10)      # seed says 9
expect("{\"a\":{\"b\":\"x\"}}".len()).to_equal(15) # seed says 14
expect("{\"a\":{\"b\":\"x\"} }".len()).to_equal(16) # PASS -- space before } fixes it
```

Any literal NOT ending in that exact shape measures correctly, including
`"x"`, `{"a":"x"}`, `abc"x"def`, `{"a":{}}`, `{"a":{"b":1}}`, and
`{"a":{"b":1},"c":2}`.

## Downstream impact

`json_tokenize` walks `while pos < text.len()`; the short length drops the
final `}`, so a JSON document whose LAST nested value is a string (i.e. the
document text ends in `"}}`) loses its closing token and `json_parse` fails
with "Expected comma in object" / nil. Documents ending in a number, an
array (`]}`), or anything after the inner object parse fine. This is what
made two image_to_markdown contracts examples fail only for their exact
byte content: the PR code and messages were correct all along.

## Workaround in tree

test/01_unit/app/image_to_markdown/contracts_spec.spl now loads the two
affected extraction-JSON payloads from
test/fixture/image_to_markdown/{audited_document.v2.json,
chart_missing_x_value.v2.json} via file_read; runtime-read strings measure
correctly. Inline the literals again once the lexer is fixed.

## Resolution of the "runtime" manifestation (2026-09-18, later same day)

The runtime text layer is INNOCENT: `"}" + "}"` measures 2 and carries
`}}` correctly, and json_parse handles runtime/file-read strings containing
`}}` fine (the contracts fixtures prove it). The round-trip failure traced
to the CONVERTERS' OWN SOURCE: server.spl's JSON-assembly literals ended in
`\"}}`, which the collapse contract folded to `\"}`, so
openai_messages_to_anthropic_v1 / anthropic_messages_to_openai_v1 emitted
JSON missing the image part's closing brace. Fixed in the PR by splitting
those literals (`\"}" + "}"`); multimodal_proxy_spec is 11/11.

The collapse contract itself remains a sharp edge for ANY source that
builds JSON (or C, or anything with adjacent braces) in double-quoted
literals: the lexer silently folds `}}` to `}` and the malformed output
surfaces far away as a parse error. Consider: emitting a lint when a
literal contains `}}`/`{{` in a context that is not an f-string, or
recommending triple-quoted/raw strings for embedded JSON. Raw strings
(r"...") and file-read text are the safe carriers today.

## Follow-up audit (2026-09-18) — VERDICTS

`git grep -c '\\"}}' -- src/` finds 71 literals containing the sequence.
Per-site classification:

INTENDED (correct `{{` ... `{expr}` ... `}}` f-string wrapping, emits one
literal brace each side):
- src/app/devhub/cmd_minio.spl:230,345, src/app/devhub/cmd_storage.spl:196,913
- src/app/itf/cmd_minio.spl:220, src/app/semihost/reader.spl:395

FALSE POSITIVE (Rust format! escaping inside a .txt codegen template, never
lexed as a Simple literal):
- src/app/sffi_gen.templates/bootstrap_sffi.txt (all 10)

BUG PATTERN (single `{` open, bare `\"}}` close building JSON/DAP/SARIF --
the close collapses to one brace and the emitted document is malformed;
same defect as the llm_caret converters fixed in this PR):
- src/app/llm_caret/messaging/adapter/agent/hook_response.spl:17
  (additionalContext JSON)
- src/app/llm_caret/messaging/adapter/chat/kakao.spl:57
  (Kakao link JSON)
- src/app/llm_caret/messaging/adapter/chat/teams.spl:55
  (Teams channelData JSON)
- src/app/editor/debug_process_launch_smoke.spl:23,24
  (DAP initialize/launch payloads)
- src/app/editor/debug_process_smoke.spl:16
  (DAP frame; ALSO hardcodes Content-Length: 84, so the collapse desyncs
  the frame length from the payload -- double corruption)
- src/app/editor/editor_ctrl_debug.spl:87
  (DAP initialize payload)
- src/app/sspec_maintain/main.spl:61
  (SARIF runs[0].invocations[0].toolExecutionNotifications JSON)

Fix per site: split the literal at the sequence (`\"}" + "}"`), as in
server.spl. Left for a follow-up lane: these are pre-existing main defects
outside the image-memory PR's scope; folding them in would mix concerns.
The remaining ~50 occurrences are f-string closures in llm_caret/messaging
and plugins (pattern `...{x}}` ending an interpolation) and are intended.
