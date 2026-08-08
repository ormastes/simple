# BrowserSession focus editability ordering

Executable scenario: `test/03_system/app/browser/feature/browser_focus_editability_order_spec.spl`

**Docgen:** pending; the self-hosted docgen lane is currently unstable.

| Requirement | Evidence |
| --- | --- |
| REQ-WEB-BROWSER-007 | A focus-side state transition prevents the next default edit event. |
| REQ-WEB-BROWSER-008 | `set_value` routes through the live BrowserSession UI action. |
| REQ-WEB-BROWSER-021 | The post-focus UI snapshot exposes the field as disabled. |

1. Open a text field whose `focus` listener disables the field and records
   `Focused`; its `beforeinput` listener would record `WrongBeforeInput`.
2. Issue `set_value` through the public BrowserSession UI action.
3. Verify the action fails after exactly one callback, the focus callback.
4. Verify the value and pixels remain unchanged, `beforeinput` did not run,
   and the post-focus UI node is disabled rather than absent.

## Folded executable scenario

```simple
it "should stop beforeinput when focus makes a text field disabled":
    step("Open an editable field whose focus listener disables it")
    var session = BrowserSession.new()
    expect(session.open_html(
        "https://example.com/edit-order",
        "<html><body><input value='old' onfocus=\"set-attr:disabled=disabled;document.title='Focused'\" onbeforeinput=\"document.title='WrongBeforeInput'\"></body></html>"
    ).is_ok()).to_equal(true)
    val pixels_before = session.render_to_pixels(16, 16).pixels

    step("Request text mutation through the public UI action")
    val inputs = ui_access_find_nodes(
        session.ui_access_snapshot(), "browser:session",
        "textfield", "old", 1
    )
    val result = session.ui_access_act(WinTextActionRequest(
        target_id: inputs[0].canonical_id, action: "set_value",
        text_value: "new", x: 0, y: 0
    ))

    step("Observe focus only: no beforeinput callback, mutation, or pixels")
    expect(result.ok).to_equal(false)
    expect(result.code).to_equal("action_failed")
    expect(session.dom_callback_count).to_equal(1)
    expect(session.current_title).to_equal("Focused")
    expect(session.current_body_html).to_contain("value=\"old\"")
    expect(session.current_body_html.contains("value=\"new\"")).to_equal(false)
    val post_focus = ui_access_find_nodes(
        session.ui_access_snapshot(), "browser:session", "textfield", "old", 1
    )
    expect(post_focus.len()).to_equal(1)
    expect(post_focus[0].enabled).to_equal(false)
    expect(_pixels_same(
        session.render_to_pixels(16, 16).pixels, pixels_before
    )).to_equal(true)
```
