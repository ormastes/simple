# BrowserSession associated form controls

Executable scenario: `test/03_system/app/browser/feature/browser_associated_form_controls_spec.spl`

**Docgen:** pending. The available self-hosted runtime crashes before producing
SPipe output, so this checked-in manual mirrors the executable scenario.

| Requirement | Executable evidence |
| --- | --- |
| REQ-WEB-BROWSER-007 | DOM click callback changes the document title. |
| REQ-WEB-BROWSER-008 | UI-access click dispatches to the live visible submitter. |
| REQ-WEB-BROWSER-010 | The resulting POST has the expected URL, body, and content type. |
| REQ-WEB-BROWSER-021 | The visible `Send` button is found on the UI-access surface. |

## Submit an externally associated control

1. Open a profile form and assert the DOM was accepted. It has a visible
   **Send** button and a `role` input outside the form but associated through
   `form="profile"`. A `leak` input is explicitly owned by a different form.
2. Find **Send** on the BrowserSession UI-access surface and dispatch its click.
3. Verify the DOM click callback changes the title to `Sending`.
4. Verify the resulting POST request targets `/save` and contains, in document
   order, `name=Ada&role=editor&intent=publish`; it must not contain
   `leak=blocked`.
5. Verify the rendered 16×16 pixel buffer is unchanged by the non-navigated
   dispatch.

This scenario prevents the historical behavior where the submit button could
activate its form but external associated controls were silently omitted from
the serialized request body, while ensuring controls owned by another form are
not accidentally included.

## Executable source mirror

```simple
# codex-system-test
# @req REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008 REQ-WEB-BROWSER-010 REQ-WEB-BROWSER-021
use std.spec.*
use common.ui.access.{WinTextActionRequest, ui_access_find_nodes}
use std.gc_async_mut.web.browser_session.{BrowserSession}
use std.gc_async_mut.web.browser_session_ui_access.*

fn _same_pixels(left: [u32], right: [u32]) -> bool:
    if left.len() != right.len():
        return false
    var index = 0
    while index < left.len():
        if left[index] != right[index]:
            return false
        index = index + 1
    true

describe "BrowserSession associated form controls":
    it "should submit an externally associated control after its visible click":
        step("Render the browser form and locate its visible submit button")
        var session = BrowserSession.new()
        expect(session.open_html(
            "https://example.com/profile",
            "<html><body><form id='profile' action='/save' method='post'><input name='name' value='Ada'></form><input form='profile' name='role' value='editor'><input form='other' name='leak' value='blocked'><form id='other'></form><button form='profile' name='intent' value='publish' onclick=\"document.title='Sending'\">Send</button></body></html>"
        ).is_ok()).to_equal(true)
        val pixels_before = session.render_to_pixels(16, 16).pixels
        val buttons = ui_access_find_nodes(
            session.ui_access_snapshot(), "browser:session", "button", "Send", 1
        )
        expect(buttons.len()).to_equal(1)
        expect(pixels_before.len()).to_equal(256)

        step("Release the submit button through the DOM UI action route")
        val activated = session.ui_access_act(WinTextActionRequest(
            target_id: buttons[0].canonical_id, action: "click",
            text_value: "", x: 0, y: 0
        ))

        step("Observe click state, serialized POST event, and unchanged page pixels")
        expect(activated.ok).to_equal(true)
        expect(session.current_title).to_equal("Sending")
        if val request = session.take_pending_request():
            expect(request.method).to_equal("POST")
            expect(request.url).to_equal("https://example.com/save")
            expect(request.body).to_equal("name=Ada&role=editor&intent=publish")
            expect(request.body.contains("leak=blocked")).to_equal(false)
            expect(request.content_type).to_equal("application/x-www-form-urlencoded")
        else:
            fail("missing form request")
        expect(_same_pixels(
            session.render_to_pixels(16, 16).pixels, pixels_before
        )).to_equal(true)
```

Regenerate this manual with `simple spipe-docgen` once the self-hosted docgen
runtime is repaired.
