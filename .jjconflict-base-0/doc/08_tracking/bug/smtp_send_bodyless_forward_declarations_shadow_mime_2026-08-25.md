# smtp/send.spl bodyless "forward declarations" shadow the real mime helpers

**Date:** 2026-08-25 · **Severity:** HIGH (every caller of `message_build_simple`/`message_build_html` in all three tiers) · **Status:** FIXED (2026-08-25)

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

(2026-08-25: first half met — no bodyless declarations remain and the live check
passes. Retiring `infra_mail.spl`'s local builder is deferred to a follow-up change
because `infra_tools_spec` pins it; see Residue below.)

## Fix (2026-08-25)
Removed every bodyless declaration and imported the real helpers instead:

- `src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/smtp/send.spl` — deleted the
  9-line `# Forward declarations for MIME functions` block; added
  `use std.<tier>.smtp.mime.{mime_type_text_plain, mime_type_text_html,
  mime_type_multipart_alternative, mime_type_multipart_mixed,
  mime_type_application_octet_stream, mime_generate_boundary,
  mime_boundary_start, mime_boundary_end}` and
  `use std.<tier>.smtp.utilities.{base64_encode_with_line_breaks}`.
  `base64_encode_with_line_breaks` is imported from `utilities`, not `mime`:
  `mime.spl:127` was itself bodyless — the only body is `utilities.spl:67`.
- `src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/smtp/mime.spl` — the
  mirror-image `# Forward declarations` block (`header_content_type`,
  `header_content_transfer_encoding`, `header_content_disposition`,
  `base64_encode_bytes`, `base64_encode_with_line_breaks`, `qp_needs_encoding`)
  had to go too: after send.spl imported mime.spl, it shadowed the real
  `header_content_type` in send.spl (`missing return in non-unit function
  'header_content_type'`, 4/5 passed). Replaced with
  `use std.<tier>.smtp.send.{header_content_type, header_content_transfer_encoding, header_content_disposition}`
  and `use std.<tier>.smtp.utilities.{base64_encode_bytes, base64_encode_with_line_breaks, qp_needs_encoding}`.
  The resulting send<->mime `use` cycle loads cleanly.
- `gc_sync_mut/smtp/{send,mime}.spl` are `export use` passthroughs of
  `gc_async_mut` and needed no change.

Every name that was bodyless has a real definition in the same tier; none
existed only as a declaration.

## Evidence
Reproducing spec: `test/01_unit/lib/nogc_sync_mut/smtp/send_mime_shadow_spec.spl`
(imports `header_from` from send.spl and calls `mime_type_text_plain()`;
generalization cases: `message_build_simple` -> `smtp_dot_stuff` yields exactly
one `<CRLF>.<CRLF>` terminator, `message_build_html` sets the html content
type, `header_from`/`header_content_type` formatting).

- Before fix (`/mnt/data/tmp/claude-1000/smtp_0_before.log`):
  `semantic: missing return in non-unit function 'mime_type_text_plain'`,
  `Results: 5 total, 0 passed, 5 failed`.
- After fix: `Results: 5 total, 5 passed, 0 failed`.
- `test/01_unit/lib/smtp/response_code_numeric_guard_spec.spl`: `Results: 1 total, 1 passed, 0 failed`
- `test/01_unit/lib/nogc_sync_mut/smtp/send_email_validate_multibyte_spec.spl`: `Results: 7 total, 7 passed, 0 failed`
- `test/01_unit/lib/nogc_sync_mut/smtp/smtp_spec.spl`: `Results: 62 total, 62 passed, 0 failed`
- `test/01_unit/lib/gc_async_mut/smtp/types_spec.spl`: `Results: 5 total, 5 passed, 0 failed`
- `test/01_unit/app/llm_caret/infra_tools_spec.spl`: `Results: 17 total, 17 passed, 0 failed`
- `sh scripts/check/check-llm-caret-infra-live.shs`:
  `PASS — 2 live row(s) executed, 0 skipped, 0 failed (mail + storage live; ...)`

## Residue (same defect class, out of scope, not changed)
- `src/lib/{nogc_async_mut,gc_async_mut}/smtp/auth.spl:15` — bodyless
  `fn base64_encode_bytes(data: text) -> text` (real body: `utilities.spl:23`).
  `nogc_sync_mut/smtp/auth.spl` already imports it from `utilities` instead.
- `src/app/llm_caret/infra_mail.spl` still carries the `mail_build_message()`
  workaround (pinned by `infra_tools_spec`); it can be retired in a separate
  change now that `message_build_simple` resolves correctly.
- Lint: all three `mime.spl` files `Lint passed`; all three `send.spl` files
  report exactly one PRE-EXISTING `error[STUB001]` on the untouched
  `date_rfc5322_format` stub (reproduced on the HEAD copy of the file,
  line 420 there / 427 now). No new lint findings from this change.
