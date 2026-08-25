# smtp/send.spl bodyless "forward declarations" shadow the real mime helpers

**Date:** 2026-08-25 · **Severity:** HIGH (every caller of `message_build_simple`/`message_build_html` in all three tiers) · **Status:** OPEN

## Symptom
`semantic: missing return in non-unit function 'mime_type_text_plain'` when
LLM Caret's `mail_send` built a message against a real SMTP server
(greenmail, via `scripts/check/check-llm-caret-infra-live.shs`).

## Cause
`src/lib/nogc_sync_mut/smtp/send.spl:424` (and the identical blocks in
`nogc_async_mut/smtp/send.spl:367`, `gc_async_mut/smtp/send.spl:367`) carry
bodyless declarations such as `fn mime_type_text_plain() -> text` with no body.
Under the flat function namespace a module that imports anything from
`send.spl` resolves `smtp.mime.mime_type_text_plain()` to the bodyless
declaration instead of the real one in `smtp/mime.spl`. Isolated with a
two-spec fixture: importing only `header_from` from send.spl breaks the
mime call; a mime-only import passes.

## Workaround in place
`src/app/llm_caret/infra_mail.spl` builds its own RFC-822 text with
`mail_build_message()` (pinned by `infra_tools_spec`) and imports only what
it needs from `smtp.*`.

## Fix direction
Delete the bodyless declarations in all three `send.spl` files (they are not
forward declarations in Simple — they are definitions with a missing body)
and import the helpers from `smtp.mime` instead. Ship a reproducing spec
that imports `header_from` and calls `mime_type_text_plain()`.

## Unblock condition
The three `send.spl` files carry no bodyless `fn ... -> text` declarations
and `message_build_simple` round-trips through
`check-llm-caret-infra-live.shs` without the local builder.
