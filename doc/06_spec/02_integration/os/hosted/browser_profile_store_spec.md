# Browser Profile Store Specification

> Tests covering hosted browser profile store.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Profile Store Specification

## Scenarios

### hosted browser profile store

#### persists one validated Home through restart and hosted navigation

- Set the home page
- Restart the browser profile
- Navigate away and return home
- Verify visible Home state


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Set the home page")
expect(_set_home_page_receipt()?).to_equal(
    "legacy-default=https://example.com/; " +
    "legacy-title=Legacy title; saved=https://home.test/start; " +
    "corrupt-fallback=https://example.com/; empty-atomic=true; " +
    "file-atomic=true; javascript-atomic=true; " +
    "oversized-atomic=true"
)

step("Restart the browser profile")
expect(_restart_home_profile_receipt()?).to_equal(
    "reopened=https://home.test/start; " +
    "registry=https://home.test/start"
)

step("Navigate away and return home")
expect(_navigate_home_receipt()?).to_equal(
    "primary-seeded=true; primary-started=true; " +
    "primary-action=home; primary-method=GET; " +
    "primary-url=https://home.test/start; primary-csp=''; " +
    "primary-csp-ready=false; primary-title=''; " +
    "primary-history=2; primary-index=1; " +
    "secondary-seeded=true; secondary-started=true; " +
    "secondary-action=home; secondary-method=GET; " +
    "secondary-url=https://home.test/start; " +
    "secondary-history=2; secondary-index=1"
)

step("Verify visible Home state")
expect(_visible_home_receipt()?).to_equal(
    "target=home; title=https://home.test/start; " +
    "draw-ir=true; pixels=117600; home-pixel=true; " +
    "address-pixel=true"
)
```

</details>

#### reopens bounded bookmark titles through public registry actions

- check in process registry profile reopen


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check_in_process_registry_profile_reopen()
```

</details>

#### rolls back bookmark mutation when its canonical snapshot read fails

- remove profile files
- var profile = BrowserProfileStore open
- BrowserBookmarkStore from profile
   - Expected: down.reason equals `chrome-pressed`
- var bookmark owner = registry bookmark store unwrap
- bookmark owner inject post mutation bookmark snapshot read failure
- registry bookmark store = Some
   - Expected: rejected.callback_count equals `0`
   - Expected: rejected.mutation_revision equals `revision_before`
- profile before entries len
   - Expected: ui_after.nodes.len() equals `ui_before.nodes.len()`
   - Expected: registry.close() is true
- var restarted = BrowserProfileStore open
   - Expected: restarted_bookmarks.entries.len() equals `1`
- restarted close
- remove profile files


<details>
<summary>Executable SSpec</summary>

Runnable source: 70 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
remove_profile_files()
var profile = BrowserProfileStore.open(PROFILE_PATH)?
profile.set_bookmark(
    "https://atomic.test/page", "Committed title", true
)?
var registry = HostedWebContentRegistry.create_with_bookmark_store(
    BrowserBookmarkStore.from_profile(profile)
)
val _ = registry.advance_window(
    92, "<div>browser</div>", 64, 48, 100000, true
)
var session = registry.sessions[0]
expect(session.browser.open_html(
    "https://atomic.test/page",
    "<title>Replacement title</title><p>atomic</p>"
).is_ok()).to_equal(true)
registry.sessions[0] = session
val down = registry.dispatch_chrome_pointer(
    50, 92, "favorite", true
)
expect(down.reason).to_equal("chrome-pressed")
val revision_before = registry.sessions[0].mutation_revision
val ui_before = registry.sessions[0].browser.ui_access_snapshot()
val profile_before = registry.profile_bookmarks
var bookmark_owner = registry.bookmark_store.unwrap()
bookmark_owner.inject_post_mutation_bookmark_snapshot_read_failure()
registry.bookmark_store = Some(bookmark_owner)

val rejected = registry.dispatch_chrome_pointer(
    51, 92, "favorite", false
)
expect(rejected.callback_count).to_equal(0)
expect(rejected.reason).to_contain(
    "injected post-mutation bookmark snapshot read failure"
)
expect(rejected.mutation_revision).to_equal(revision_before)
expect(registry.sessions[0].mutation_revision).to_equal(
    revision_before
)
expect(registry.profile_bookmarks.entries.len()).to_equal(
    profile_before.entries.len()
)
expect(registry.profile_bookmarks.entries[0].first).to_equal(
    profile_before.entries[0].first
)
expect(registry.profile_bookmarks.entries[0].second).to_equal(
    "Committed title"
)
val ui_after = registry.sessions[0].browser.ui_access_snapshot()
expect(ui_after.snapshot_revision).to_equal(
    ui_before.snapshot_revision
)
expect(ui_after.nodes.len()).to_equal(ui_before.nodes.len())
expect(ui_after.nodes[5].selected).to_equal(
    ui_before.nodes[5].selected
)
expect(ui_after.nodes[5].selected).to_be(true)
expect(registry.close()).to_equal(true)

var restarted = BrowserProfileStore.open(PROFILE_PATH)?
val restarted_bookmarks = restarted.load_bookmarks()?
expect(restarted_bookmarks.entries.len()).to_equal(1)
expect(restarted_bookmarks.entries[0].first).to_equal(
    "https://atomic.test/page"
)
expect(restarted_bookmarks.entries[0].second).to_equal(
    "Committed title"
)
restarted.close()?
remove_profile_files()
```

</details>

#### cancels network jobs before fallible profile shutdown

- var closed store = BrowserBookmarkStore memory
- closed store close
   - Expected: favorite_down.reason equals `chrome-pressed`
   - Expected: favorite_up.callback_count equals `0`
   - Expected: registry.close() is false
   - Expected: registry.sessions[0].network_job_handle equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var closed_store = BrowserBookmarkStore.memory()?
closed_store.close()?
var registry = HostedWebContentRegistry.create_with_bookmark_store(
    closed_store
)
expect(registry.profile_failure_reason).to_contain("close:")
val _ = registry.advance_window(
    45, "<div>browser</div>", 64, 48, 100000, true
)
var session = registry.sessions[0]
expect(session.browser.open_html(
    "https://rollback.test/",
    "<html><body>rollback</body></html>"
).is_ok()).to_equal(true)
session.network_job_handle = 424242
registry.sessions[0] = session
val favorite_down = registry.dispatch_chrome_pointer(
    1, 45, "favorite", true
)
val favorite_up = registry.dispatch_chrome_pointer(
    2, 45, "favorite", false
)
expect(favorite_down.reason).to_equal("chrome-pressed")
expect(favorite_up.callback_count).to_equal(0)
expect(registry.sessions[0].browser.is_favorite(
    "https://rollback.test/"
)).to_equal(false)
expect(registry.close()).to_equal(false)
expect(registry.sessions[0].network_job_handle).to_equal(0)
```

</details>

#### releases hosted sessions after successful registry shutdown

- var registry = HostedWebContentRegistry create
   - Expected: registry.sessions.len() equals `1`
   - Expected: registry.close() is true
   - Expected: registry.sessions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = HostedWebContentRegistry.create()
val _ = registry.advance_window(
    46, "<div>browser</div>", 64, 48, 100000, false
)
expect(registry.sessions.len()).to_equal(1)
expect(registry.close()).to_equal(true)
expect(registry.sessions.len()).to_equal(0)
```

</details>

#### round trips add open and remove bookmark controls across host restarts

- remove profile files
- BrowserProfileStore open
   - Expected: first.close() is true
- BrowserProfileStore open
   - Expected: opened.ok is true
   - Expected: restarted.close() is true
- var removed = BrowserProfileStore open
   - Expected: removed.load_bookmarks()?.entries.len() equals `0`
- removed close
- remove profile files


<details>
<summary>Executable SSpec</summary>

Runnable source: 60 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
remove_profile_files()
var first = HostedWebContentRegistry.create_with_bookmark_store(
    BrowserBookmarkStore.from_profile(
        BrowserProfileStore.open(PROFILE_PATH)?
    )
)
val _ = first.advance_window(
    47, "<div>first host</div>", 64, 48, 100000, true
)
var first_session = first.sessions[0]
expect(first_session.browser.open_html(
    "https://restart.test/saved",
    "<html><body>Saved page</body></html>"
).is_ok()).to_equal(true)
first.sessions[0] = first_session
val _ = first.dispatch_chrome_pointer(1, 47, "favorite", true)
expect(first.dispatch_chrome_pointer(
    2, 47, "favorite", false
).callback_count).to_equal(1)
expect(first.close()).to_equal(true)

var restarted = HostedWebContentRegistry.create_with_bookmark_store(
    BrowserBookmarkStore.from_profile(
        BrowserProfileStore.open(PROFILE_PATH)?
    )
)
val _ = restarted.advance_window(
    48, "<div>restarted host</div>", 64, 48, 100000, true
)
var restarted_session = restarted.sessions[0]
restarted_session.browser.register_resource(
    "https://restart.test/saved",
    "<html><body>Reopened saved page</body></html>"
)
val restored_bookmarks = ui_access_find_nodes(
    restarted_session.browser.ui_access_snapshot(),
    "browser:session", "link",
    "https://restart.test/saved", 1
)
expect(restored_bookmarks.len()).to_equal(1)
val opened = restarted_session.browser.ui_access_act(
    WinTextActionRequest(
        target_id: restored_bookmarks[0].canonical_id,
        action: "click", text_value: "", x: 0, y: 0
    )
)
expect(opened.ok).to_equal(true)
expect(restarted_session.browser.current_url).to_equal(
    "https://restart.test/saved"
)
expect(restarted_session.browser.current_body_html).to_contain(
    "Reopened saved page"
)
restarted.sessions[0] = restarted_session
val _ = restarted.dispatch_chrome_pointer(
    3, 48, "favorite", true
)
expect(restarted.dispatch_chrome_pointer(
    4, 48, "favorite", false
).callback_count).to_equal(1)
expect(restarted.close()).to_equal(true)

var removed = BrowserProfileStore.open(PROFILE_PATH)?
expect(removed.load_bookmarks()?.entries.len()).to_equal(0)
removed.close()?
remove_profile_files()

```

</details>

#### persists validated bookmarks and HSTS across reopen and removal

- remove profile files
- var first = BrowserProfileStore open
- first save bookmarks
- first save hsts
- first close
- var reopened = BrowserProfileStore open
   - Expected: restored_bookmarks.entries.len() equals `1`
   - Expected: restored_hsts.entries.len() equals `1`
- "INSERT INTO browser bookmarks
- DbValue Integer
- DbValue Text
- DbValue Text
- ") VALUES
- DbValue Text
- DbValue Integer
- DbValue Integer
- DbValue Integer
- ") VALUES
- DbValue Text
- DbValue Integer
- DbValue Integer
- DbValue Integer
- "include subdomains) VALUES
- DbValue Text
- DbValue Integer
- DbValue Integer
- DbValue Integer
- "include subdomains) VALUES
- DbValue Text
- DbValue Integer
- DbValue Integer
- DbValue Integer
   - Expected: reopened.load_bookmarks()?.entries.len() equals `1`
   - Expected: reopened.load_hsts(100000)?.entries.len() equals `1`
- BrowserHstsSnapshot create
- Ok
- fail
- Err
   - Expected: reopened.load_hsts(100000)?.entries.len() equals `1`
- BrowserBookmarkStore from profile
   - Expected: changed is false
   - Expected: registry.sessions.len() equals `1`
- var bookmark owner = registry bookmark store unwrap
- registry bookmark store = Some
- var primary owner = BrowserProfileStore open
- BrowserHstsSnapshot create
- primary owner close
   - Expected: registry.close_window(44) is true
   - Expected: registry.close() is true
- var after removal = BrowserProfileStore open
   - Expected: after_removal.load_bookmarks()?.entries.len() equals `0`
   - Expected: after_removal.load_hsts(101001)?.entries.len() equals `1`
- after removal close
- remove profile files
- var writer one = BrowserProfileStore open
- var writer two = BrowserProfileStore open
   - Expected: merged.entries.len() equals `1`
   - Expected: merged.entries[0].first equals `https://two.test/`
- writer one close
- writer two close
- remove profile files


<details>
<summary>Executable SSpec</summary>

Runnable source: 158 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
remove_profile_files()
var bookmarks: [Pair<text, text>] = []
bookmarks.push(Pair(
    first: "https://simple.test/docs", second: "Simple docs"
))
var hsts_entries: [BrowserHstsSnapshotEntry] = []
hsts_entries.push(BrowserHstsSnapshotEntry(
    host: "simple.test",
    received_at_unix_ms: 99500,
    expires_at_unix_ms: 101000,
    include_subdomains: true
))

var first = BrowserProfileStore.open(PROFILE_PATH)?
first.save_bookmarks(BrowserBookmarkSnapshot.create(bookmarks))?
first.save_hsts(BrowserHstsSnapshot.create(hsts_entries), 100000)?
first.close()?

var reopened = BrowserProfileStore.open(PROFILE_PATH)?
val restored_bookmarks = reopened.load_bookmarks()?
val restored_hsts = reopened.load_hsts(100000)?
expect(restored_bookmarks.entries.len()).to_equal(1)
expect(restored_hsts.entries.len()).to_equal(1)

reopened.db.exec(
    "INSERT INTO browser_bookmarks (position, url, title) VALUES (?, ?, ?)",
    [
        DbValue.Integer(value: 99),
        DbValue.Text(value: "file:///etc/passwd"),
        DbValue.Text(value: "invalid")
    ]
)?
reopened.db.exec(
    "INSERT INTO browser_hsts (" +
    "host, received_at_unix_ms, expires_at_unix_ms, include_subdomains" +
    ") VALUES (?, ?, ?, ?)",
    [
        DbValue.Text(value: "com"),
        DbValue.Integer(value: 99500),
        DbValue.Integer(value: 101000),
        DbValue.Integer(value: 1)
    ]
)?
reopened.db.exec(
    "INSERT INTO browser_hsts (" +
    "host, received_at_unix_ms, expires_at_unix_ms, include_subdomains" +
    ") VALUES (?, ?, ?, ?)",
    [
        DbValue.Text(value: "user@simple.test"),
        DbValue.Integer(value: 99500),
        DbValue.Integer(value: 101000),
        DbValue.Integer(value: 1)
    ]
)?
for duplicate_host in ["Dupe.Test", "other.test"]:
    reopened.db.exec(
        "INSERT INTO browser_hsts (" +
        "host, received_at_unix_ms, expires_at_unix_ms, " +
        "include_subdomains) VALUES (?, ?, ?, ?)",
        [
            DbValue.Text(value: duplicate_host),
            DbValue.Integer(value: 99500),
            DbValue.Integer(value: 101000),
            DbValue.Integer(value: 1)
        ]
    )?
for duplicate_host in ["dupe.test", "Other.Test"]:
    reopened.db.exec(
        "INSERT INTO browser_hsts (" +
        "host, received_at_unix_ms, expires_at_unix_ms, " +
        "include_subdomains) VALUES (?, ?, ?, ?)",
        [
            DbValue.Text(value: duplicate_host),
            DbValue.Integer(value: 99500),
            DbValue.Integer(value: 99000),
            DbValue.Integer(value: 1)
        ]
    )?
expect(reopened.load_bookmarks()?.entries.len()).to_equal(1)
expect(reopened.load_hsts(100000)?.entries.len()).to_equal(1)

var invalid_hsts: [BrowserHstsSnapshotEntry] = []
invalid_hsts.push(BrowserHstsSnapshotEntry(
    host: "simple.test:443",
    received_at_unix_ms: 99500,
    expires_at_unix_ms: 101000,
    include_subdomains: true
))
match reopened.save_hsts(
    BrowserHstsSnapshot.create(invalid_hsts), 100000
):
    Ok(_):
        fail("Expected malformed HSTS host rejection")
    Err(_):
        expect(reopened.load_hsts(100000)?.entries.len()).to_equal(1)

var registry = HostedWebContentRegistry.create_with_bookmark_store(
    BrowserBookmarkStore.from_profile(reopened)
)
val changed = registry.advance_window(
    44, "<div>browser</div>", 64, 48, 100000, true
)
expect(changed).to_equal(false)
expect(registry.sessions.len()).to_equal(1)
expect(registry.sessions[0].browser.is_favorite(
    "https://simple.test/docs"
)).to_equal(true)
var bookmark_owner = registry.bookmark_store.unwrap()
expect(bookmark_owner.toggle_bookmark(
    "https://simple.test/docs", "Simple docs"
)?).to_equal(false)
registry.bookmark_store = Some(bookmark_owner)

var primary_owner = BrowserProfileStore.open(PROFILE_PATH)?
var current_hsts: [BrowserHstsSnapshotEntry] = []
current_hsts.push(BrowserHstsSnapshotEntry(
    host: "simple.test",
    received_at_unix_ms: 100500,
    expires_at_unix_ms: 200000,
    include_subdomains: true
))
primary_owner.save_hsts(
    BrowserHstsSnapshot.create(current_hsts), 100500
)?
primary_owner.close()?

expect(registry.close_window(44)).to_equal(true)
expect(registry.close()).to_equal(true)

var after_removal = BrowserProfileStore.open(PROFILE_PATH)?
expect(after_removal.load_bookmarks()?.entries.len()).to_equal(0)
expect(after_removal.load_hsts(101001)?.entries.len()).to_equal(1)
after_removal.close()?
remove_profile_files()

var writer_one = BrowserProfileStore.open(PROFILE_PATH)?
var writer_two = BrowserProfileStore.open(PROFILE_PATH)?
writer_one.set_bookmark(
    "https://one.test/", "One", true
)?
writer_two.set_bookmark(
    "https://two.test/", "Two", true
)?
writer_one.set_bookmark(
    "https://one.test/", "One", false
)?
expect(writer_one.toggle_bookmark(
    "https://shared.test/", "Shared"
)?).to_equal(true)
expect(writer_two.toggle_bookmark(
    "https://shared.test/", "Shared"
)?).to_equal(false)
val merged = writer_two.load_bookmarks()?
expect(merged.entries.len()).to_equal(1)
expect(merged.entries[0].first).to_equal("https://two.test/")
writer_one.close()?
writer_two.close()?
remove_profile_files()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/hosted/browser_profile_store_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering hosted browser profile store.
- hosted browser profile store

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
