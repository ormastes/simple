# JavaScript error side-effect preservation

Executable scenario:
`test/03_system/app/browser/feature/browser_eval_error_side_effects_spec.spl`

**Manual status:** complete static mirror of the executable four-step scenario.

| Requirement | Evidence |
| --- | --- |
| REQ-WEB-BROWSER-005 | The original JavaScript error remains observable after earlier side effects commit. |
| REQ-WEB-BROWSER-009 | Back restores the first committed history entry without changing history length. |
| REQ-WEB-BROWSER-012 | Origin B observes only its own storage and cookie values. |
| REQ-WEB-BROWSER-013 | Local storage, session storage, and cookies remain partitioned by exact origin. |
| REQ-WEB-BROWSER-021 | This manual mirrors the executable four-step SSpec. |

1. Open `https://a.example/page`.
2. Write `A` to local storage, session storage, and `document.cookie`, then
   throw; verify the error and exact committed origin-A maps and cookie jar.
3. Navigate to `https://b.example/page`, commit `B`, and verify exact
   isolation, two origin maps, two cookies, and the two-entry history.
4. Go Back and verify JavaScript reads `A:A:sid=A` while the storage maps,
   cookie jar, and history remain intact.

## Folded executable scenario

```simple
describe "JavaScript error side-effect preservation":
    it "should preserve pre-error storage and cookies across isolated history traversal":
        step("Open origin A")
        var session = BrowserSession.new()
        expect(session.open_html(
            "https://a.example/page",
            "<html><body>Origin A</body></html>"
        ).is_ok()).to_be(true)

        step("Commit origin A writes before JavaScript throws")
        val failed = session.eval_script(
            "localStorage.setItem('key', 'A'); sessionStorage.setItem('key', 'A'); document.cookie = 'sid=A; Path=/'; throw 'after-write'"
        )
        match failed:
            Err(error):
                expect(error).to_equal("after-write")
            Ok(_):
                fail("Expected JavaScript to report after-write")
        expect(session.local_storage_by_origin.len()).to_equal(1)
        expect(session.local_storage_by_origin[0].origin).to_equal(
            "https://a.example"
        )
        expect(session.local_storage_by_origin[0].entries.len()).to_equal(1)
        expect(session.local_storage_by_origin[0].entries[0].first).to_equal("key")
        expect(session.local_storage_by_origin[0].entries[0].second).to_equal("A")
        expect(session.session_storage_by_origin.len()).to_equal(1)
        expect(session.session_storage_by_origin[0].origin).to_equal(
            "https://a.example"
        )
        expect(session.session_storage_by_origin[0].entries.len()).to_equal(1)
        expect(session.session_storage_by_origin[0].entries[0].first).to_equal("key")
        expect(session.session_storage_by_origin[0].entries[0].second).to_equal("A")
        expect(session.cookies.count()).to_equal(1)
        expect(session.document_cookie()).to_equal("sid=A")

        step("Navigate to isolated origin B and commit different values")
        expect(session.open_html(
            "https://b.example/page",
            "<html><body>Origin B</body></html>"
        ).is_ok()).to_be(true)
        expect(session.eval_script(
            "localStorage.setItem('key', 'B'); sessionStorage.setItem('key', 'B'); document.cookie = 'sid=B; Path=/'; 'committed'"
        ).is_ok()).to_be(true)
        expect(session.local_storage_item("key") ?? "").to_equal("B")
        expect(session.session_storage_item("key") ?? "").to_equal("B")
        expect(session.document_cookie()).to_equal("sid=B")
        expect(session.local_storage_by_origin.len()).to_equal(2)
        expect(session.local_storage_by_origin[0].origin).to_equal("https://a.example")
        expect(session.local_storage_by_origin[1].origin).to_equal("https://b.example")
        expect(session.session_storage_by_origin.len()).to_equal(2)
        expect(session.session_storage_by_origin[0].origin).to_equal("https://a.example")
        expect(session.session_storage_by_origin[1].origin).to_equal("https://b.example")
        expect(session.cookies.count()).to_equal(2)
        expect(session.history.len()).to_equal(2)
        expect(session.current_index).to_equal(1)
        expect(session.history[0].url).to_equal("https://a.example/page")
        expect(session.history[1].url).to_equal("https://b.example/page")

        step("Go Back and observe origin A values from JavaScript")
        expect(session.go_back().is_ok()).to_be(true)
        expect(session.current_index).to_equal(0)
        expect(session.current_url).to_equal("https://a.example/page")
        expect(session.history.len()).to_equal(2)
        expect(session.local_storage_by_origin.len()).to_equal(2)
        expect(session.session_storage_by_origin.len()).to_equal(2)
        expect(session.cookies.count()).to_equal(2)
        val restored = session.eval_script(
            "localStorage.getItem('key') + ':' + sessionStorage.getItem('key') + ':' + document.cookie"
        )
        match restored:
            Ok(JsValue.String(value)):
                expect(value).to_equal("A:A:sid=A")
            Ok(_):
                fail("Expected restored JavaScript values to be text")
            Err(error):
                fail("Expected restored JavaScript values: {error}")
```
