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

## Runtime manifestation (2026-09-18, same day): concatenation-built strings

The defect is not lexer-only. A string BUILT at runtime by concatenation
miscounts the same way when the result contains the sequence: the forward
OpenAI->Anthropic converter's output

```
[{"role":"user","content":[{"type":"image","source":{"type":"base64",
  "media_type":"image/png","data":"AA=="}}]}]
```

reports text.len() 111 where the true length is 112, and json_parse of it
fails with "Expected comma in object" -- the '}}' in the payload collides
with whatever the seed's text layer uses there. File-read strings carrying
the same bytes parse fine, so the corruption is specific to the
concat/join-built path. This blocks the openai->anthropic->openai round
-trip example in test/01_unit/app/llm_caret/multimodal_proxy_spec.spl
(10/11; the other ten were fixed by splitting literals at the sequence and
by replacing a corrupt inline PNG payload).

The common thread -- literals, concatenation results, but not file-read
strings -- points at the seed's text construction/flattening layer rather
than storage. Any fix should start there (text rope / escape handling for
adjacent closing braces).
