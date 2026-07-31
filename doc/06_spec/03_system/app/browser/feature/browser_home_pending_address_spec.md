# Pending Home address truth

Status: **DRAFT / EVIDENCE-BLOCKED**

Executable source:
`test/03_system/app/browser/feature/browser_home_pending_address_spec.spl`.
No runtime result is claimed until an admitted current pure-Simple runner
executes the scenario.

## Scope

An admitted Home action must publish its canonical pending URL immediately in
the address surface. It must not publish the document URL or history early.
Invalid Home configuration and failed admission must retain the prior draft,
focus/edit state, committed document, and history.

The scenario exercises the BrowserSession textual UI action, the hosted worker
SBR2 Home command, and the parent registry Home press/release path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

## Scenario: publish only an admitted Home target

### 1. Commit one old document and configure canonical Home owners

BrowserSession, hosted worker, and parent registry each start with committed
document and one-entry history at `https://old.test/page`. Their configured
Home target is `https://home.test/`. The exact history length/index or ledger
is retained as the pre-action oracle.

### 2. Leave a distinct abandoned address draft focused

Each address owner contains `https://abandoned.test/not-home`. Worker chrome
focus and registry editing/replace state are active, proving that a later
change is caused by Home admission rather than setup.

### 3. Admit Home through BrowserSession UI worker and parent registry

The scenario clicks `browser:session#home`, sends a decoded SBR2 `home`
navigation command to the hosted worker, and sends Home down/up through
`HostedBrowserRendererRegistry.dispatch_chrome_pointer`. No network response
or renderer frame is delivered.

The registry keeps editing active on pointer-down. Only a successful
press/release admission may publish the permit URL and clear edit/replace
state.

### 4. Show pending Home preserve commit and retain state on rejection

All three active address surfaces show exactly `https://home.test/`.
BrowserSession and worker pending URLs and the registry navigation permit agree
with that value. Worker chrome focus and registry edit/replace state are
cleared.

The committed document remains `https://old.test/page`; all retained history
lengths, indices, and ledgers remain unchanged.
BrowserSession advances `ui_access_revision` exactly once when the normalized
pending target replaces a different draft.

Four regression checks share this final step:

- BrowserSession rejects `javascript:alert(1)` as Home configuration and as a
  direct navigation target without replacing the abandoned draft, committed
  document, or history.
- A registry whose renderer rejected that invalid Home configuration returns
  `home-unconfigured`; its pointer-down and failed release retain the abandoned
  draft, edit/replace state, committed document, and history.
- A valid configured Home rejected as `renderer-busy` retains the abandoned
  draft, edit/replace state, mutation revision, committed document, and history.
- A non-Home address navigation publishes its normalized target and advances
  `ui_access_revision` once; re-admitting the unchanged target does not advance
  the revision again.

## Helper and step parity

Executable helpers:

- `home_registry`
- `close_home_registry`

The four visible manual steps exactly match the executable `step(...)` calls:

1. `Commit one old document and configure canonical Home owners`
2. `Leave a distinct abandoned address draft focused`
3. `Admit Home through BrowserSession UI worker and parent registry`
4. `Show pending Home preserve commit and retain state on rejection`

<details>
<summary>Executable SSpec</summary>

```simple
# codex-system-test
# @req REQ-WEB-BROWSER-009 REQ-WEB-BROWSER-010
"""# Pending Home address truth

An admitted Home action publishes its canonical pending target in the address
surface immediately. The committed document and history remain unchanged until
the response commits; invalid configuration and failed admission retain the
editable draft and focus state.
"""

use std.spec.*
use common.ui.access.{WinTextActionRequest}
use std.common.web.browser_renderer_protocol.{
    BrowserRendererMessage,
    browser_renderer_decoder_feed,
    browser_renderer_decoder_new,
    browser_renderer_navigation_encode
}
use std.gc_async_mut.web.browser_session.{BrowserSession}
use std.gc_async_mut.web.browser_session_ui_access.*
use os.compositor.compositor_engine2d.{Engine2dCompositorBackend}
use os.hosted.hosted_browser_renderer_process.{
    HostedBrowserRendererProcess
}
use os.hosted.hosted_browser_renderer_registry.{
    HostedBrowserRendererEntry, HostedBrowserRendererRegistry
}
use os.hosted.hosted_browser_renderer_worker.{
    HostedBrowserRendererWorkerSession
}

val HOME_OLD_URL = "https://old.test/page"
val HOME_TARGET_URL = "https://home.test/"
val HOME_ABANDONED_DRAFT = "https://abandoned.test/not-home"
val HOME_OLD_HTML = "<html><body><p>committed old page</p></body></html>"
val HOME_WINDOW_ID: i64 = 241

fn home_registry(
    configured_home: text
) -> HostedBrowserRendererRegistry:
    var renderer = HostedBrowserRendererProcess.create(24, 64, 48)
    renderer.state = "active"
    renderer.document_url = HOME_OLD_URL
    renderer.document_origin = "https://old.test"
    renderer.history_urls = [HOME_OLD_URL]
    renderer.history_csp_policies = [""]
    renderer.history_csp_ready = [false]
    renderer.history_index = 0
    val _ = renderer.set_home_url(configured_home)
    var entry = HostedBrowserRendererEntry.create(
        HOME_WINDOW_ID, renderer,
        Engine2dCompositorBackend.create_named(64, 48, "software"),
        0, ""
    )
    entry.ready = true
    entry.address_draft = HOME_ABANDONED_DRAFT
    entry.address_editing = true
    entry.address_replace_on_text = true
    var registry = HostedBrowserRendererRegistry.create(
        "", configured_home
    )
    registry.entries = [entry]
    registry

fn close_home_registry(registry: HostedBrowserRendererRegistry):
    var entry = registry.entries[0]
    entry.raster.shutdown()
    registry.entries[0] = entry

describe "Pending Home address truth":

    # @manual: show
    # @req REQ-WEB-BROWSER-009 REQ-WEB-BROWSER-010
    it "should publish only an admitted Home target without committing early":
        step("Commit one old document and configure canonical Home owners")
        var session = BrowserSession.new()
        expect(session.open_html(
            HOME_OLD_URL, HOME_OLD_HTML
        ).unwrap()).to_be(true)
        expect(session.try_set_home_url(HOME_TARGET_URL)).to_be(true)
        val session_history_len = session.history.len()
        val session_history_index = session.current_index

        var worker = HostedBrowserRendererWorkerSession.create(64, 48)
        expect(worker.handle(BrowserRendererMessage(
            kind: "init", generation: 7, request_id: 2,
            payload: HOME_OLD_HTML
        )).ok).to_be(true)
        expect(worker.browser.open_html(
            HOME_OLD_URL, HOME_OLD_HTML
        ).unwrap()).to_be(true)
        val worker_history_len = worker.browser.history.len()
        val worker_history_index = worker.browser.current_index

        var registry = home_registry(HOME_TARGET_URL)
        val registry_history_urls = (
            registry.entries[0].renderer.history_urls
        )
        val registry_history_index = (
            registry.entries[0].renderer.history_index
        )

        step("Leave a distinct abandoned address draft focused")
        expect(session.apply_address_update(
            "", HOME_ABANDONED_DRAFT, true
        ).unwrap()).to_equal(HOME_ABANDONED_DRAFT)
        val session_revision = session.ui_access_revision
        worker.browser.address_draft = HOME_ABANDONED_DRAFT
        worker.chrome_focus = "address"
        worker.address_replace_on_text = true
        val worker_revision = worker.browser.ui_access_revision
        expect(registry.address_text(HOME_WINDOW_ID)).to_equal(
            HOME_ABANDONED_DRAFT
        )
        expect(registry.entries[0].address_editing).to_be(true)

        step("Admit Home through BrowserSession UI worker and parent registry")
        val session_home = session.ui_access_act(
            WinTextActionRequest(
                target_id: "browser:session#home", action: "click",
                text_value: "", x: 0, y: 0
            )
        )
        expect(session_home.ok).to_be(true)

        val worker_home = browser_renderer_navigation_encode(
            7, 3, "home", HOME_TARGET_URL, "GET", "", "", ""
        )
        expect(worker_home.ok).to_be(true)
        val worker_message = browser_renderer_decoder_feed(
            browser_renderer_decoder_new(7), worker_home.wire
        )
        expect(worker.handle(worker_message.message).ok).to_be(true)

        val home_down = registry.dispatch_chrome_pointer(
            1, HOME_WINDOW_ID, "home", true
        )
        expect(home_down.reason).to_equal("chrome-pressed")
        expect(registry.entries[0].address_editing).to_be(true)
        val home_up = registry.dispatch_chrome_pointer(
            2, HOME_WINDOW_ID, "home", false
        )
        expect(home_up.callback_count).to_equal(1)
        expect(home_up.reason).to_equal("")

        step("Show pending Home preserve commit and retain state on rejection")
        expect(session.address_draft).to_equal(HOME_TARGET_URL)
        expect(session.ui_access_snapshot().nodes[6].text_value).to_equal(
            HOME_TARGET_URL
        )
        expect(session.ui_access_snapshot().nodes[6].focused).to_be(false)
        expect(session.pending_url).to_equal(HOME_TARGET_URL)
        expect(session.ui_access_revision).to_equal(
            session_revision + 1
        )
        expect(session.current_url).to_equal(HOME_OLD_URL)
        expect(session.history.len()).to_equal(session_history_len)
        expect(session.current_index).to_equal(session_history_index)

        expect(worker.chrome_focus).to_equal("")
        expect(worker.address_replace_on_text).to_be(false)
        expect(worker.browser.address_draft).to_equal(HOME_TARGET_URL)
        expect(worker.browser.pending_url).to_equal(HOME_TARGET_URL)
        expect(worker.browser.ui_access_revision).to_equal(
            worker_revision + 1
        )
        expect(worker.browser.current_url).to_equal(HOME_OLD_URL)
        expect(worker.browser.history.len()).to_equal(worker_history_len)
        expect(worker.browser.current_index).to_equal(
            worker_history_index
        )

        expect(registry.address_text(HOME_WINDOW_ID)).to_equal(
            HOME_TARGET_URL
        )
        expect(registry.entries[0].address_editing).to_be(false)
        expect(
            registry.entries[0].address_replace_on_text
        ).to_be(false)
        expect(
            registry.entries[0].renderer.navigation_permit.url
        ).to_equal(HOME_TARGET_URL)
        expect(registry.document_url(HOME_WINDOW_ID)).to_equal(
            HOME_OLD_URL
        )
        expect(
            registry.entries[0].renderer.history_urls
        ).to_equal(registry_history_urls)
        expect(
            registry.entries[0].renderer.history_index
        ).to_equal(registry_history_index)

        var rejected_session = BrowserSession.new()
        expect(rejected_session.open_html(
            HOME_OLD_URL, HOME_OLD_HTML
        ).unwrap()).to_be(true)
        expect(rejected_session.try_set_home_url(
            HOME_TARGET_URL
        )).to_be(true)
        rejected_session.address_draft = HOME_ABANDONED_DRAFT
        val rejected_revision = rejected_session.ui_access_revision
        expect(rejected_session.try_set_home_url(
            "javascript:alert(1)"
        )).to_be(false)
        expect(rejected_session.home_url).to_equal(HOME_TARGET_URL)
        expect(rejected_session.begin_network_navigation(
            "javascript:alert(1)", "GET", "", "", ""
        ).unwrap_err()).to_equal("unsupported navigation scheme")
        expect(rejected_session.address_draft).to_equal(
            HOME_ABANDONED_DRAFT
        )
        expect(rejected_session.ui_access_revision).to_equal(
            rejected_revision
        )
        expect(rejected_session.current_url).to_equal(HOME_OLD_URL)
        expect(rejected_session.history.len()).to_equal(1)

        var rejected_registry = home_registry(
            "javascript:alert(1)"
        )
        val rejected_down = rejected_registry.dispatch_chrome_pointer(
            3, HOME_WINDOW_ID, "home", true
        )
        expect(rejected_down.reason).to_equal("chrome-pressed")
        expect(rejected_registry.entries[0].address_editing).to_be(true)
        val rejected_up = rejected_registry.dispatch_chrome_pointer(
            4, HOME_WINDOW_ID, "home", false
        )
        expect(rejected_up.callback_count).to_equal(0)
        expect(rejected_up.reason).to_equal("home-unconfigured")
        expect(rejected_registry.address_text(
            HOME_WINDOW_ID
        )).to_equal(HOME_ABANDONED_DRAFT)
        expect(
            rejected_registry.entries[0].address_editing
        ).to_be(true)
        expect(
            rejected_registry.entries[0].address_replace_on_text
        ).to_be(true)
        expect(rejected_registry.document_url(
            HOME_WINDOW_ID
        )).to_equal(HOME_OLD_URL)
        expect(
            rejected_registry.entries[0].renderer.history_urls
        ).to_equal([HOME_OLD_URL])
        expect(
            rejected_registry.entries[0].renderer.history_index
        ).to_equal(0)

        var busy_registry = home_registry(HOME_TARGET_URL)
        var busy_entry = busy_registry.entries[0]
        busy_entry.renderer.pending_wire = "partially-written"
        busy_entry.renderer.pending_wire_offset = 1
        busy_registry.entries[0] = busy_entry
        val busy_revision = busy_entry.mutation_revision
        expect(busy_registry.dispatch_chrome_pointer(
            5, HOME_WINDOW_ID, "home", true
        ).reason).to_equal("chrome-pressed")
        val busy_home = busy_registry.dispatch_chrome_pointer(
            6, HOME_WINDOW_ID, "home", false
        )
        expect(busy_home.callback_count).to_equal(0)
        expect(busy_home.reason).to_equal("renderer-busy")
        expect(busy_registry.address_text(
            HOME_WINDOW_ID
        )).to_equal(HOME_ABANDONED_DRAFT)
        expect(busy_registry.entries[0].address_editing).to_be(true)
        expect(
            busy_registry.entries[0].address_replace_on_text
        ).to_be(true)
        expect(
            busy_registry.entries[0].mutation_revision
        ).to_equal(busy_revision)
        expect(busy_registry.document_url(
            HOME_WINDOW_ID
        )).to_equal(HOME_OLD_URL)
        expect(
            busy_registry.entries[0].renderer.history_urls
        ).to_equal([HOME_OLD_URL])

        var address_session = BrowserSession.new()
        expect(address_session.open_html(
            HOME_OLD_URL, HOME_OLD_HTML
        ).unwrap()).to_be(true)
        address_session.address_draft = HOME_ABANDONED_DRAFT
        val address_revision = address_session.ui_access_revision
        expect(address_session.begin_network_navigation(
            "Example.COM/next", "GET", "", "", ""
        ).unwrap()).to_be(true)
        expect(address_session.address_draft).to_equal(
            "https://Example.COM/next"
        )
        expect(address_session.ui_access_revision).to_equal(
            address_revision + 1
        )
        val unchanged_revision = address_session.ui_access_revision
        expect(address_session.begin_network_navigation(
            "https://Example.COM/next", "GET", "", "", ""
        ).unwrap()).to_be(true)
        expect(address_session.ui_access_revision).to_equal(
            unchanged_revision
        )

        close_home_registry(registry)
        close_home_registry(rejected_registry)
        close_home_registry(busy_registry)
```

</details>
