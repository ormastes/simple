# browser_chrome_pointer_cancellation_spec

> Navigation chrome and page-to-page replacement release a renderer-owned page
> press with the prior press receipt before assigning new ownership.

| Tests | Active | Skipped | Pending |
|-------|-------:|--------:|--------:|
| 3 | 3 | 0 | 0 |

## At a Glance

| Field | Value |
|-------|-------|
| Status | Active |
| Requirements | REQ-WEB-BROWSER-007, 008, 009, 021 |
| Source | `test/03_system/app/browser/feature/browser_chrome_pointer_cancellation_spec.spl` |
| Updated | 2026-07-30 |
| Runtime gate | Admitted pure-Simple `HOSTED_WM_ARTIFACT` and matching SHA-256 |

## Scenario: cancel a page press before navigation chrome owns input

1. Press a renderer-owned page target.
   - The registry owns window `141` and press receipt `401`.
2. Cancel through navigation chrome state.
   - Address chrome becomes the new owner under receipt `402`.
3. Observe one canonical pointer release.
   - The pending release retains window `141` and event `401`, then the
     renderer reports no page pointer pressed and the receipt counter is
     exactly `1`.
4. Render without stale pressed state.
   - The page remains green in semantic Draw IR, the hosted frame, and
     Engine2D pixels; the red click discriminator remains absent.

<details>
<summary>Executable SSpec</summary>

```simple
var registry = setup_chrome_cancel_fixture()

step("Press a renderer-owned page target")
check_page_press_owned(registry, CHROME_CANCEL_WINDOW, 401)

step("Cancel through navigation chrome state")
val chrome = registry.dispatch_chrome_pointer(
    402, CHROME_CANCEL_WINDOW, "address", true
)
expect(chrome.reason).to_equal("chrome-pressed")
expect(registry.pressed_event_id).to_equal(402)

step("Observe one canonical pointer release")
check_renderer_release_sent(registry, CHROME_CANCEL_WINDOW, 401)

step("Render without stale pressed state")
check_pressed_state_cleared(registry)
expect(registry.dispatch_chrome_pointer(
    403, CHROME_CANCEL_WINDOW, "address", false
).reason).to_equal("address-focused")
expect(registry.pressed_window_id).to_equal(0)
expect(registry.pressed_event_id).to_equal(0)
expect(registry.close()).to_be(true)
```

</details>

<details>
<summary>Edge scenario: replace one page renderer with another</summary>

The first page owns receipt `501`. A press on the second page assigns receipt
`502` only after the shared clear path records a release for the first page
using its original window and event IDs. The second page then receives its
single ordinary release.

```simple
var registry = setup_chrome_cancel_fixture()
check_page_press_owned(registry, CHROME_CANCEL_WINDOW, 501)
val replacement = registry.dispatch_pointer(
    502, CHROME_CANCEL_SECOND_WINDOW, 4, 4, true
)
expect(replacement.callback_count).to_equal(1)
expect(registry.pressed_window_id).to_equal(CHROME_CANCEL_SECOND_WINDOW)
expect(registry.pressed_event_id).to_equal(502)
check_renderer_release_sent(registry, CHROME_CANCEL_WINDOW, 501)
_await_chrome_cancel_window(registry, CHROME_CANCEL_SECOND_WINDOW)
expect(registry.dispatch_pointer(
    503, CHROME_CANCEL_SECOND_WINDOW, 4, 4, false
).callback_count).to_equal(1)
expect(registry.close()).to_be(true)
```

</details>

<details>
<summary>Fixture and checker source</summary>

```simple
fn _count_chrome_cancel_color(pixels: [u32], color: u32) -> i64:
    var count: i64 = 0
    for pixel in pixels:
        if pixel == color:
            count = count + 1
    count

fn _await_chrome_cancel_window(
    registry: HostedBrowserRendererRegistry,
    window_id: i64
):
    var attempt: i64 = 0
    while attempt < 500:
        val state = registry.advance_window(
            window_id, "", CHROME_CANCEL_HTML, 32, 24,
            attempt * 1000, 100000, true
        )
        if state == "failed":
            fail("browser renderer failed while awaiting pointer evidence")
        if state == "frame":
            return
        thread_sleep_ms(1)
        attempt = attempt + 1
    fail("browser renderer did not produce pointer evidence")

fn setup_chrome_cancel_fixture() -> HostedBrowserRendererRegistry:
    val artifact = env_get("HOSTED_WM_ARTIFACT")
    val expected_sha = env_get("HOSTED_WM_ARTIFACT_SHA256")
    if artifact == "":
        fail("HOSTED_WM_ARTIFACT must name the hosted_entry native binary")
    if (expected_sha.len() != 64 or
        file_hash_sha256(artifact) != expected_sha):
        fail("HOSTED_WM_ARTIFACT does not match its admitted SHA-256")
    var registry = HostedBrowserRendererRegistry.create(
        artifact, "about:blank"
    )
    expect(registry.ensure(
        CHROME_CANCEL_WINDOW, CHROME_CANCEL_HTML,
        32, 24, 0, 100000
    )).to_equal("none")
    expect(registry.ensure(
        CHROME_CANCEL_SECOND_WINDOW, CHROME_CANCEL_HTML,
        32, 24, 0, 100000
    )).to_equal("none")
    _await_chrome_cancel_window(registry, CHROME_CANCEL_WINDOW)
    _await_chrome_cancel_window(registry, CHROME_CANCEL_SECOND_WINDOW)
    val _ = registry.take_frame(CHROME_CANCEL_WINDOW)
    val _ = registry.take_frame(CHROME_CANCEL_SECOND_WINDOW)
    registry

fn check_page_press_owned(
    registry: HostedBrowserRendererRegistry,
    window_id: i64,
    event_id: i64
):
    val pressed = registry.dispatch_pointer(
        event_id, window_id, 4, 4, true
    )
    expect(pressed.callback_count).to_equal(1)
    expect(pressed.reason).to_equal("")
    expect(registry.pressed_window_id).to_equal(window_id)
    expect(registry.pressed_event_id).to_equal(event_id)

fn check_renderer_release_sent(
    registry: HostedBrowserRendererRegistry,
    prior_window_id: i64,
    prior_event_id: i64
):
    expect(registry.pending_cancel_window_id).to_equal(prior_window_id)
    expect(registry.pending_cancel_event_id).to_equal(prior_event_id)
    var attempt: i64 = 0
    while attempt < 500:
        val state = registry.advance_window(
            prior_window_id, "", CHROME_CANCEL_HTML, 32, 24,
            1000000 + attempt * 1000, 100000, true
        )
        if state == "failed":
            fail("browser renderer failed while releasing page press")
        val index = registry._index(prior_window_id)
        if (registry.pending_cancel_window_id == 0 and
            registry.pending_cancel_event_id == 0 and
            index >= 0 and
            registry.entries[index].renderer.command_deadline_ms <= 0 and
            not registry.entries[index].renderer.pointer_pressed):
            expect(
                registry.pointer_cancel_receipt_count
            ).to_equal(1)
            return
        thread_sleep_ms(1)
        attempt = attempt + 1
    fail("browser renderer did not complete the canonical pointer release")

fn check_pressed_state_cleared(registry: HostedBrowserRendererRegistry):
    val index = registry._index(CHROME_CANCEL_WINDOW)
    expect(index).to_be_greater_than(-1)
    expect(registry.entries[index].renderer.pointer_pressed).to_be(false)
    val frame = registry.take_frame(CHROME_CANCEL_WINDOW)
    expect(frame.pixels.len()).to_equal(32 * 24)
    expect(_count_chrome_cancel_color(
        frame.pixels, 0xFF00FF00u32
    )).to_equal(16 * 16)
    expect(_count_chrome_cancel_color(
        frame.pixels, 0xFFFF0000u32
    )).to_equal(0)

    val composition = simple_web_layout_render_html_draw_ir_with_images(
        CHROME_CANCEL_HTML, 32, 24, []
    )
    var press_index: i32 = -1
    var command_index: i32 = 0
    while command_index < composition.batches[0].commands.len():
        if (
            composition.batches[0].commands[command_index].component_id ==
                "press"
        ):
            press_index = command_index
        command_index = command_index + 1
    expect(press_index).to_be_greater_than(-1)
    val press = composition.batches[0].commands[press_index]
    expect(press.kind).to_equal("rect")
    expect(press.x).to_equal(0)
    expect(press.y).to_equal(0)
    expect(press.width).to_equal(16)
    expect(press.height).to_equal(16)
    expect(press.color).to_equal(0xFF00FF00u32)
    val raster = Engine2dCompositorBackend.create_named(
        32, 24, "software"
    )
    val rendered = raster.render_draw_ir_composition(composition, [])
    raster.shutdown()
    expect(_count_chrome_cancel_color(
        rendered.pixels, 0xFF00FF00u32
    )).to_equal(16 * 16)
    expect(_count_chrome_cancel_color(
        rendered.pixels, 0xFFFF0000u32
    )).to_equal(0)
```

</details>

<details>
<summary>Generation boundary: reject a stale release after site swap</summary>

The old renderer generation owns page receipt `601` and its queued release.
The same-window site-swap boundary clears both records before closing the old
renderer. The replacement generation starts with no page press, no pending
release, and an unchanged release-receipt count of zero.

```simple
var registry = setup_chrome_cancel_fixture()
val index = registry._index(CHROME_CANCEL_WINDOW)
expect(index).to_be_greater_than(-1)
var entry = registry.entries[index]
val old_generation = entry.renderer.generation
entry.renderer.navigation_permit = HostedBrowserNavigationPermit(
    active: true,
    url: "https://replacement.test/page",
    method: "GET",
    headers: "",
    body: "",
    content_type: "",
    redirect_count: 0
)
entry.renderer.site_lock = "https://old.test"
entry.renderer.site_swap_pending = true
entry.renderer.site_swap_site = "https://replacement.test"
entry.renderer.pointer_pressed = true
registry.entries[index] = entry
registry.pressed_window_id = CHROME_CANCEL_WINDOW
registry.pressed_event_id = 601
registry.pending_cancel_window_id = CHROME_CANCEL_WINDOW
registry.pending_cancel_event_id = 601

expect(registry._begin_site_swap(index, 100000)).to_equal("none")
expect(
    registry.entries[index].renderer.generation
).to_be_greater_than(old_generation)
expect(registry.pressed_window_id).to_equal(0)
expect(registry.pressed_event_id).to_equal(0)
expect(registry.pending_cancel_window_id).to_equal(0)
expect(registry.pending_cancel_event_id).to_equal(0)

registry.cancel_pointer_state(999)
expect(registry.pointer_cancel_receipt_count).to_equal(0)
expect(registry.entries[index].renderer.pointer_pressed).to_be(false)
expect(
    registry.entries[index].renderer.pending_pointer_cancel_event_id
).to_equal(0)
expect(registry.close()).to_be(true)
```

</details>

## Evidence boundary

This scenario requires the admitted pure-Simple hosted artifact. Static source
review alone is not reported as runtime PASS. The red pixel is a click
discriminator; its absence proves cancellation did not synthesize a click.
