# UI test API typing loop mixes byte length with character indexing

Date: 2026-10-11.
Status: fixed in the handler and verified by both unchanged Phase1 seed
dispatcher scenarios. Native acceptance and docgen validation remain unverified.

## Source evidence

Owner: `src/app/ui.test_api/handler.spl`, function `_handle_type`, lines
187–193 at the reviewed revision. After injecting focus, it loops from zero to
`typed_text.len()`, reads `typed_text[idx]`, and emits one KeyPress per index.

The length boundary counts UTF-8 bytes while indexed character access is
character-oriented on the admitted Phase1 producer. For text such as
`한😀A`, byte length exceeds the three characters. Source analysis predicts
extra invalid/empty character accesses or events after the intended characters.
The subsequent baseline confirmed out-of-bounds access: both the raw and escaped
payload scenarios failed at character index 3 for length 3.

This loop predates the JSON field repair. That repair now decodes JSON Unicode
escapes correctly, making multibyte values reachable from escaped payloads too.
It must not be addressed by preserving escape text or discarding Unicode.

## Existing evidence boundary

`test/01_unit/app/ui/test_api_raw_unicode_spec.spl` passed four of four
Phase1 seed diagnostic cases. Log:
`build/phase-one-ui-diagnostic/test_api_raw_unicode_spec/cycle-one.log`.
Those cases verify JSON extraction with raw Korean and emoji; they do not call
the typing handler and are not evidence that character event dispatch succeeds.

The established text-iteration contract is described by
`test/01_unit/bugs/for_in_text_char_iteration_spec.spl`: text iteration yields
one text element per Unicode scalar and the self-hosted compiler lowers it
through the canonical string-character owner. That spec was inspected, not
rerun here.

## Minimal fix and acceptance

The handler now replaces the byte-length/index loop with the normal pure-Simple
character loop: `for ch in typed_text`, injecting `UIEvent.KeyPress(key: ch)`.
This removes the byte/character mismatch and redundant interpolation. The
post-fix Phase1 seed diagnostic passed both unchanged scenarios.

Add focused real-handler regressions for both raw `한😀A` and equivalent
JSON escapes `\uD55C\uD83D\uDE00A`. Each must observe the focus event followed
by exactly three key events containing `한`, `😀`, and `A`, in that order,
with no empty or duplicate events. Guard event-array accesses after asserting
the count. Preserve existing ASCII behavior.

The two focused real-dispatcher regressions now exist at
`test/03_system/gui/ui/web_test_api_unicode_typing_spec.spl`, with their manual
at `doc/06_spec/03_system/gui/ui/web_test_api_unicode_typing_spec.md`.
The pre-fix coordinator run executed both: zero passed, two failed, exit 1,
884 ms. Both failures reported character index 3 out of bounds for length 3.
Evidence: `build/phase-one-ui-diagnostic/web_test_api_unicode_typing_spec/cycle-one.log`;
input manifest: `build/phase-one-ui-diagnostic/unicode-typing-baseline-inputs.json`.

The post-fix diagnostic executed the unchanged scenarios: two passed, zero
failed, exit 0 in 1214 ms. Evidence:
`build/phase-one-ui-diagnostic/web_test_api_unicode_typing_spec/cycle-two.log`
with its `.rss.env`, `.command.json`, and `.exit` receipts. The source inputs
are bound by `build/phase-one-ui-diagnostic/unicode-typing-repair-inputs.json`;
the change is retained in `build/phase-one-ui-diagnostic/unicode-typing-repair.patch`.

The passing callback evidence is in-process and does not claim live HTTP,
browser delivery, or application consumption of the keys. Native acceptance
and docgen validation remain unverified. Keep this follow-up separate from
the already-qualified JSON extraction diagnostic and platform-spec test batch.
