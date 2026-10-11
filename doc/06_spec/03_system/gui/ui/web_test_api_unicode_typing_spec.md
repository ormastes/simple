# Web UI test API Unicode typing

Source: `test/03_system/gui/ui/web_test_api_unicode_typing_spec.spl`.
Production owner: `src/app/ui.test_api/handler.spl`, reached through
`dispatch_test_api` and a real `UISession`.
Requirement: REQ-SSPEC-SYSTEM.

Status: **Pre-fix Phase1 seed diagnostic: zero passed, two failed**. Both
scenarios failed with index 3 out of bounds for a three-character string.
The baseline exited 1 in 884 ms; evidence is retained at
`build/phase-one-ui-diagnostic/web_test_api_unicode_typing_spec/cycle-one.log`
and `build/phase-one-ui-diagnostic/unicode-typing-baseline-inputs.json`.
**Post-fix Phase1 seed diagnostic PASS: two passed, zero failed**, exit 0 in
1214 ms, using the unchanged scenarios and corrected character iteration.
Evidence: `build/phase-one-ui-diagnostic/web_test_api_unicode_typing_spec/cycle-two.log`
with its `.rss.env`, `.command.json`, and `.exit` receipts. Inputs and patch:
`build/phase-one-ui-diagnostic/unicode-typing-repair-inputs.json` and
`build/phase-one-ui-diagnostic/unicode-typing-repair.patch`.
Native acceptance and SPipe docgen validation remain pending. The 80% annotation
is a target, not measured coverage.

## Manual scenarios

1. **Raw Unicode typing.** Create a real input widget and reset the event
   recorder. POST `{"id":"unicode_typing_input","text":"한😀A"}` through the
   production dispatcher. Require HTTP status 200, JSON content type,
   `ok:true`, then exactly four callbacks: focus the input, key `한`, key
   `😀`, and key `A`, in that order.
2. **Escaped Unicode typing.** Create a fresh fixture and send equivalent JSON
   Unicode escapes: `\uD55C\uD83D\uDE00A`. Require the same response and exact
   four-event sequence. The emoji must arrive as one complete character after
   its UTF-16 surrogate-pair escape is decoded.

The recorder inspects actual production callback events and fails on unexpected
event kinds. An asserted count precedes a real length guard around every indexed
payload check. Extra, empty, reordered or split key events cannot satisfy the
expected sequence.

## Evidence boundary

This is in-process server-handler and callback evidence. It does not start an
HTTP listener or browser and does not claim that application event consumers
updated input state or rendered a surface. Existing ASCII tests are unchanged
and are not rerun by this focused regression lane.

Tracked source assessment:
`doc/08_tracking/bug/ui_test_api_unicode_typing_byte_character_mismatch_2026-10-11.md`.
The retained baseline predates the handler correction. The coordinator's second
run passed the same scenarios against the corrected character loop.

<details>
<summary>Executable SSpec, including real fixture and guarded event checker</summary>

```simple
# Unicode typing through the production UI test API dispatcher.
# codex-system-test
# @req REQ-SSPEC-SYSTEM
# @tag:system
# @cover src/app/ui.test_api/handler.spl 80%
# Coverage percentage is an admission target, not measured coverage.
# bug: doc/08_tracking/bug/ui_test_api_unicode_typing_byte_character_mismatch_2026-10-11.md
# Host-fixture evidence: request dispatch and callback events, not live HTTP or rendering.

use std.spec.{describe, it, expect, step, fail}
use common.ui.builder.{column, text_input, build_tree_with_title}
use common.ui.widget.{UIEvent}
use nogc_sync_mut.ui.session.{UISession}
use app.ui.test_api.mount.{dispatch_test_api}

var unicode_typing_events: [text] = []

# @inline
fn create_unicode_typing_fixture() -> UISession:
    unicode_typing_events = []
    val root = column("unicode_typing_root", [
        text_input("unicode_typing_input", "Enter text")
    ])
    val tree = build_tree_with_title(root, "Unicode typing fixture", "default")
    return UISession.new(tree)

fn record_unicode_typing_event(event: UIEvent):
    match event:
        UIEvent.Action(action_name):
            unicode_typing_events.push("action:" + action_name)
        UIEvent.KeyPress(key_text):
            unicode_typing_events.push("key:" + key_text)
        _:
            fail("Unicode typing injected an unexpected event kind")

# @inline
fn expect_unicode_typing_sequence():
    expect(unicode_typing_events.len()).to_equal(4)
    if unicode_typing_events.len() == 4:
        expect(unicode_typing_events[0]).to_equal("action:focus_unicode_typing_input")
        expect(unicode_typing_events[1]).to_equal("key:한")
        expect(unicode_typing_events[2]).to_equal("key:😀")
        expect(unicode_typing_events[3]).to_equal("key:A")

describe "Web UI Test API Unicode typing":
    # @manual scenario evidence
    it "should inject one key per raw Unicode character after focusing the input":
        step("Create the Unicode typing fixture")
        val session = create_unicode_typing_fixture()
        step("Dispatch raw Korean emoji and ASCII text")
        val response = dispatch_test_api(
            "/api/test/type", "POST",
            "{\"id\":\"unicode_typing_input\",\"text\":\"한😀A\"}",
            session, record_unicode_typing_event
        )
        expect(response.0).to_equal(200)
        expect(response.1).to_equal("application/json")
        expect(response.2).to_equal("{\"ok\":true}")
        step("Verify focus followed by exactly three complete character events")
        expect_unicode_typing_sequence()

    it "should inject the same complete characters after decoding JSON Unicode escapes":
        step("Create the Unicode typing fixture")
        val session = create_unicode_typing_fixture()
        step("Dispatch escaped Korean and surrogate-pair emoji text")
        val response = dispatch_test_api(
            "/api/test/type", "POST",
            "{\"id\":\"unicode_typing_input\",\"text\":\"\\uD55C\\uD83D\\uDE00A\"}",
            session, record_unicode_typing_event
        )
        expect(response.0).to_equal(200)
        expect(response.1).to_equal("application/json")
        expect(response.2).to_equal("{\"ok\":true}")
        step("Verify focus followed by exactly three complete character events")
        expect_unicode_typing_sequence()
```

</details>
