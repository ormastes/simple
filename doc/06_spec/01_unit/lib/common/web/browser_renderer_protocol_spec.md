# Browser Renderer Protocol Specification

> Tests covering isolated browser renderer protocol.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Protocol Specification

## Scenarios

### isolated browser renderer protocol

#### round-trips bounded document titles and rejects hostile SBRF8 fields

**Requirements:** `REQ-WEB-BROWSER-009`, `REQ-WEB-BROWSER-021`

- hosted browser title is valid
   - Expected: hosted_browser_title_is_valid(title_512) is `true`
   - Expected: hosted_browser_title_is_valid(title_513) is `false`
-  renderer protocol fixture
- browser renderer decoder new
   - Expected: decoded_message.status equals `message`
   - Expected: frame.document_title equals `title_512`
-  renderer protocol fixture
   - Expected: oversized.reason equals `invalid-document-title`
   - Expected: forged_title.len() equals `684`
- base64 encode
   - Expected: forged_rejection.document_title equals ``
-  renderer protocol fixture
- browser renderer decoder new
-  renderer protocol fixture
- browser renderer decoder new


<details>
<summary>Executable SSpec</summary>

Runnable source: 132 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val title_512 = "a".repeat(510) + "é"
val title_513 = "a".repeat(511) + "é"
expect(hosted_browser_title_is_valid(title_512)).to_be(true)
expect(hosted_browser_title_is_valid(title_513)).to_be(false)
val encoded = (
    browser_renderer_frame_encode_with_state_and_retained_images_and_title(
        _renderer_protocol_fixture(),
        7, 2, 41, -1, 0, "", 0, "", "",
        "https://title.test/", "", "", title_512,
        1, [], []
    )
)
expect(encoded.ok).to_be(true)
val decoded_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), encoded.wire
)
expect(decoded_message.status).to_equal("message")
expect(browser_renderer_frame_reply_to_request_id(
    decoded_message.message
)).to_equal(41)
val frame = browser_renderer_frame_decode(
    decoded_message.message, 64, 48
)
expect(frame.ok).to_be(true)
expect(frame.document_title_present).to_be(true)
expect(frame.document_title).to_equal(title_512)

val oversized = (
    browser_renderer_frame_encode_with_state_and_retained_images_and_title(
        _renderer_protocol_fixture(),
        7, 2, 41, -1, 0, "", 0, "", "",
        "https://title.test/", "", "", title_513,
        1, [], []
    )
)
expect(oversized.reason).to_equal("invalid-document-title")
val forged_title = base64_encode(title_513)
expect(forged_title.len()).to_equal(684)
val forged_oversized = BrowserRendererMessage(
    kind: "frame",
    generation: decoded_message.message.generation,
    request_id: decoded_message.message.request_id,
    payload: decoded_message.message.payload.replace(
        base64_encode(title_512), forged_title
    )
)
val forged_rejection = browser_renderer_frame_decode(
    forged_oversized, 64, 48
)
expect(forged_rejection.ok).to_be(false)
expect(forged_rejection.reason).to_equal(
    "invalid-document-title"
)
expect(forged_rejection.document_title_present).to_be(false)
expect(forged_rejection.document_title).to_equal("")
val noncanonical = BrowserRendererMessage(
    kind: "frame",
    generation: decoded_message.message.generation,
    request_id: decoded_message.message.request_id,
    payload: decoded_message.message.payload.replace(
        "\t684\t", "\t0684\t"
    )
)
expect(browser_renderer_frame_decode(
    noncanonical, 64, 48
).reason).to_equal("malformed-document-title")
val short_title = (
    browser_renderer_frame_encode_with_state_and_retained_images_and_title(
        _renderer_protocol_fixture(),
        7, 2, 41, -1, 0, "", 0, "", "",
        "https://title.test/", "", "", "ok",
        1, [], []
    )
)
val short_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), short_title.wire
)
val nul_title = BrowserRendererMessage(
    kind: "frame",
    generation: short_message.message.generation,
    request_id: short_message.message.request_id,
    payload: short_message.message.payload.replace(
        "b2s=", "AA=="
    )
)
expect(browser_renderer_frame_decode(
    nul_title, 64, 48
).reason).to_equal("invalid-document-title")
val invalid_padding = BrowserRendererMessage(
    kind: "frame",
    generation: short_message.message.generation,
    request_id: short_message.message.request_id,
    payload: short_message.message.payload.replace(
        "b2s=", "b=8="
    )
)
expect(browser_renderer_frame_decode(
    invalid_padding, 64, 48
).reason).to_equal("invalid-document-title")
val truncated_title = BrowserRendererMessage(
    kind: "frame",
    generation: short_message.message.generation,
    request_id: short_message.message.request_id,
    payload: short_message.message.payload.replace(
        "\t4\t0\t", "\t5\t0\t"
    )
)
expect(browser_renderer_frame_decode(
    truncated_title, 64, 48
).ok).to_be(false)
val overlapping_title = BrowserRendererMessage(
    kind: "frame",
    generation: short_message.message.generation,
    request_id: short_message.message.request_id,
    payload: short_message.message.payload.replace(
        "\t4\t0\t", "\t0\t0\t"
    )
)
expect(browser_renderer_frame_decode(
    overlapping_title, 64, 48
).ok).to_be(false)
val legacy = browser_renderer_frame_encode_with_state_and_retained_images(
    _renderer_protocol_fixture(),
    7, 2, 41, -1, 0, "", 0, "", "",
    "https://title.test/", "", "", 1, [], []
)
val legacy_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), legacy.wire
)
expect(browser_renderer_frame_decode(
    legacy_message.message, 64, 48
).document_title_present).to_be(false)
```

</details>

#### selects dense image resources once in first-reference order

- Encode a dense frame whose image resources arrive in reverse order
-  renderer protocol dense image fixture
- var reverse index = dense resources len
- reverse resources push
   - Expected: selected.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Encode a dense frame whose image resources arrive in reverse order")
val (dense_composition, dense_resources) = (
    _renderer_protocol_dense_image_fixture(1024, 64)
)
var reverse_resources: [SimpleOsHostGpuImageResource] = []
var reverse_index = dense_resources.len() - 1
while reverse_index >= 0:
    reverse_resources.push(dense_resources[reverse_index])
    reverse_index = reverse_index - 1
val selected = browser_renderer_referenced_image_resources(
    dense_composition, reverse_resources
)
expect(selected.len()).to_equal(64)
var selected_index = 0
while selected_index < selected.len():
    expect(selected[selected_index].image_uri).to_equal(
        "dense:{selected_index}"
    )
    selected_index = selected_index + 1
expect(browser_renderer_frame_encode_with_state_and_images(
    dense_composition, 7, 1, 1, -1, 0, "", 0, "",
    "", "", "", "", selected
).ok).to_be(true)
```

</details>

#### round-trips only bounded positive viewport resize commands

- Encode and decode valid and oversized viewport resize commands
- browser renderer decoder new
   - Expected: resize.width equals `800`
   - Expected: resize.height equals `600`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Encode and decode valid and oversized viewport resize commands")
val encoded = browser_renderer_resize_encode(7, 1, 800, 600)
expect(encoded.ok).to_be(true)
val message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), encoded.wire
)
val resize = browser_renderer_resize_decode(message.message)
expect(resize.ok).to_be(true)
expect(resize.width).to_equal(800)
expect(resize.height).to_equal(600)
expect(browser_renderer_resize_encode(
    7, 1, 4097, 600
).ok).to_be(false)
```

</details>

#### round-trips bounded network messages without delimiter ambiguity

- Round-trip bounded fetch and response messages across the renderer boundary
- browser renderer decoder new
   - Expected: request.reply_to_request_id equals `41`
   - Expected: request.request_id equals `fetch-1`
   - Expected: request.method equals `POST`
   - Expected: request.headers equals `X-Test: a\tb`
   - Expected: request.body equals `h\u00e9llo\nbody`
   - Expected: request.credentials equals `include`
   - Expected: request.initiator_origin equals `null`
   - Expected: request.script_cookie_writes.len() equals `2`
   - Expected: request.script_cookie_writes[0] equals `theme=dark`
   - Expected: request.script_cookie_writes[1] equals `lang=\u754c`
- "edge=" + "x" repeat
- browser renderer decoder new
- browser renderer decoder new
- browser renderer decoder new
- browser renderer decoder new
   - Expected: response.status equals `200`
   - Expected: response.body equals `ok\n\u754c`
   - Expected: response.credentials equals ``
   - Expected: response.script_cookie_writes.len() equals `0`
- str


<details>
<summary>Executable SSpec</summary>

Runnable source: 158 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Round-trip bounded fetch and response messages across the renderer boundary")
val request_wire = browser_renderer_fetch_request_encode(
    7, 1, 41, "fetch-1", "fetch", "https://example.test/a",
    "POST", "X-Test: a\tb", "h\u00e9llo\nbody", "text/plain",
    "include", ["theme=dark", "lang=\u754c"], "null"
)
expect(request_wire.ok).to_be(true)
val request_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), request_wire.wire
)
val request = browser_renderer_fetch_request_decode(
    request_message.message
)
expect(request.ok).to_be(true)
expect(request.reply_to_request_id).to_equal(41)
expect(request.request_id).to_equal("fetch-1")
expect(request.method).to_equal("POST")
expect(request.headers).to_equal("X-Test: a\tb")
expect(request.body).to_equal("h\u00e9llo\nbody")
expect(request.credentials).to_equal("include")
expect(request.initiator_origin).to_equal("null")
expect(request.script_cookie_writes.len()).to_equal(2)
expect(request.script_cookie_writes[0]).to_equal("theme=dark")
expect(request.script_cookie_writes[1]).to_equal("lang=\u754c")
val boundary_cookie = (
    "edge=" + "x".repeat(4091) + "; Path=/account"
)
val boundary_wire = browser_renderer_fetch_request_encode(
    7, 4, 44, "fetch-4", "fetch", "https://example.test/cookie",
    "GET", "", "", "", "include", [boundary_cookie],
    "https://example.test"
)
expect(boundary_wire.ok).to_be(true)
expect(browser_renderer_fetch_request_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(7), boundary_wire.wire
    ).message
).script_cookie_writes[0]).to_equal(boundary_cookie)
val empty_cookie_writes = browser_renderer_fetch_request_encode(
    7, 2, 42, "fetch-2", "fetch", "https://example.test/b",
    "GET", "", "", "", "omit", []
)
expect(empty_cookie_writes.ok).to_be(true)
expect(browser_renderer_fetch_request_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(7), empty_cookie_writes.wire
    ).message
).script_cookie_writes.len()).to_equal(0)
val image_request_wire = browser_renderer_fetch_request_encode(
    7, 3, 43, "image-1", "image",
    "https://example.test/pixel.png",
    "GET", "", "", "", "omit", []
)
expect(image_request_wire.ok).to_be(true)
expect(browser_renderer_fetch_request_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(7), image_request_wire.wire
    ).message
).kind).to_equal("image")

val response_wire = browser_renderer_network_response_encode(
    7, 1, "fetch-1", "fetch", "https://example.test/a",
    200, "Content-Type: text/plain", "ok\n\u754c", ""
)
expect(response_wire.ok).to_be(true)
val response_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), response_wire.wire
)
val response = browser_renderer_network_response_decode(
    response_message.message
)
expect(response.ok).to_be(true)
expect(response.status).to_equal(200)
expect(response.body).to_equal("ok\n\u754c")
expect(response.credentials).to_equal("")
expect(response.script_cookie_writes.len()).to_equal(0)

# SBRQ2 is intentionally not accepted: both endpoints ship together,
# and guessing legacy credential semantics would cross the boundary.
expect(browser_renderer_fetch_request_decode(
    BrowserRendererMessage(
        kind: "fetch_request", generation: 7, request_id: 1,
        payload: "SBRQ2\t1\t1\t5\t1\t3\t0\t0\t0\nxfetchuGETextra"
    )
).ok).to_be(false)
expect(browser_renderer_fetch_request_decode(
    BrowserRendererMessage(
        kind: "fetch_request", generation: 7, request_id: 1,
        payload: "SBRQ4\t1\t1\t5\t1\t3\t0\t0\t0\t7\t4\t2\n" +
            "xfetchuGETINCLUDEnull0\n"
    )
).ok).to_be(false)
for malformed_cookie_batch in [
    "02\t3\t3\nonetwo",
    "2\t3\none",
    "1\t03\none",
    "1\t3\nonetwo",
    "1\t3\na\nb",
    "1\t8193\n"
]:
    expect(browser_renderer_fetch_request_decode(
        BrowserRendererMessage(
            kind: "fetch_request", generation: 7, request_id: 1,
            payload: (
                "SBRQ4\t1\t1\t5\t1\t3\t0\t0\t0\t11\t4\t" +
                str(malformed_cookie_batch.len()) + "\n" +
                "xfetchuGETsame-originnull" +
                malformed_cookie_batch
            )
        )
    ).ok).to_be(false)
expect(browser_renderer_fetch_request_encode(
    7, 1, 1, "fetch-1", "fetch", "https://example.test/",
    "TRACE", "", "", "", "omit", []
).ok).to_be(false)
expect(browser_renderer_fetch_request_encode(
    7, 1, 0, "fetch-1", "fetch", "https://example.test/",
    "GET", "", "", "", "same-origin", []
).ok).to_be(false)
for invalid_credentials in ["", "INCLUDE", "same_origin", "credential\nforged"]:
    expect(browser_renderer_fetch_request_encode(
        7, 1, 1, "fetch-1", "fetch",
        "https://example.test/", "GET", "", "", "",
        invalid_credentials, []
    ).ok).to_be(false)
for invalid_cookie_write in ["nul\0write", "line\rreturn", "line\nfeed"]:
    expect(browser_renderer_fetch_request_encode(
        7, 1, 1, "fetch-1", "fetch",
        "https://example.test/", "GET", "", "", "",
        "same-origin", [invalid_cookie_write]
    ).ok).to_be(false)
val maximum_cookie_write = ["x"; 8192].join("")
expect(browser_renderer_fetch_request_encode(
    7, 1, 1, "fetch-1", "fetch", "https://example.test/",
    "GET", "", "", "", "same-origin", [maximum_cookie_write]
).ok).to_be(true)
val oversized_cookie_write = ["x"; 8193].join("")
expect(browser_renderer_fetch_request_encode(
    7, 1, 1, "fetch-1", "fetch", "https://example.test/",
    "GET", "", "", "", "same-origin", [oversized_cookie_write]
).ok).to_be(false)
expect(browser_renderer_fetch_request_encode(
    7, 1, 1, "fetch-1", "fetch", "https://example.test/",
    "GET", "", "", "", "same-origin", ["x"; 32]
).ok).to_be(true)
expect(browser_renderer_fetch_request_encode(
    7, 1, 1, "fetch-1", "fetch", "https://example.test/",
    "GET", "", "", "", "same-origin", ["x"; 33]
).ok).to_be(false)
val aggregate_cookie_write = ["x"; 4096].join("")
expect(browser_renderer_fetch_request_encode(
    7, 1, 1, "fetch-1", "fetch", "https://example.test/",
    "GET", "", "", "", "same-origin", [aggregate_cookie_write; 32]
).ok).to_be(true)
expect(browser_renderer_network_response_encode(
    7, 1, "fetch-1", "fetch", "https://example.test/",
    0, "", "", ""
).ok).to_be(false)
```

</details>

#### round-trips bounded actions and rejects ambiguous payloads

- Round-trip renderer actions and submit malformed payload shapes
- browser renderer decoder new
   - Expected: pointer.kind equals `pointer`
   - Expected: pointer.event_id equals `9`
   - Expected: pointer.x equals `-3`
   - Expected: pointer.y equals `4`
- browser renderer decoder new
   - Expected: scroll.kind equals `scroll`
   - Expected: scroll.event_id equals `10`
   - Expected: scroll.y equals `-1250`
- browser renderer decoder new
   - Expected: browser_renderer_action_decode(advance_message.message).now_ms equals `1234`
- browser renderer decoder new
   - Expected: browser_renderer_action_decode(key_message.message).key_code equals `65`
- browser renderer decoder new
   - Expected: shifted_key.key_code equals `9`
- browser renderer decoder new
   - Expected: browser_renderer_action_decode(text_message.message).value equals `h\u00e9llo\nworld`
- browser renderer decoder new
   - Expected: browser_renderer_action_decode(chrome_message.message).value equals `forward`


<details>
<summary>Executable SSpec</summary>

Runnable source: 85 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Round-trip renderer actions and submit malformed payload shapes")
val pointer_wire = browser_renderer_pointer_encode(7, 1, 9, -3, 4, true)
expect(pointer_wire.ok).to_be(true)
val pointer_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), pointer_wire.wire
)
val pointer = browser_renderer_action_decode(pointer_message.message)
expect(pointer.ok).to_be(true)
expect(pointer.kind).to_equal("pointer")
expect(pointer.event_id).to_equal(9)
expect(pointer.x).to_equal(-3)
expect(pointer.y).to_equal(4)
expect(pointer.pressed).to_be(true)

val scroll_wire = browser_renderer_scroll_encode(
    7, 1, 10, -1250
)
expect(scroll_wire.ok).to_be(true)
val scroll_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), scroll_wire.wire
)
val scroll = browser_renderer_action_decode(scroll_message.message)
expect(scroll.ok).to_be(true)
expect(scroll.kind).to_equal("scroll")
expect(scroll.event_id).to_equal(10)
expect(scroll.y).to_equal(-1250)
expect(browser_renderer_scroll_encode(
    7, 1, 10, 1048576001
).ok).to_be(false)

val advance_wire = browser_renderer_advance_encode(7, 1, 1234)
val advance_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), advance_wire.wire
)
expect(browser_renderer_action_decode(advance_message.message).now_ms).to_equal(1234)

val key_wire = browser_renderer_key_encode(7, 1, 10, 65, false)
val key_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), key_wire.wire
)
expect(browser_renderer_action_decode(key_message.message).key_code).to_equal(65)

val shifted_key_wire = browser_renderer_key_with_shift_encode(
    7, 1, 10, 9, true, true
)
val shifted_key_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), shifted_key_wire.wire
)
val shifted_key = browser_renderer_action_decode(
    shifted_key_message.message
)
expect(shifted_key.key_code).to_equal(9)
expect(shifted_key.shift_key).to_be(true)

val text_wire = browser_renderer_text_encode(7, 1, 11, "h\u00e9llo\nworld")
val text_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), text_wire.wire
)
expect(browser_renderer_action_decode(text_message.message).value).to_equal("h\u00e9llo\nworld")

val chrome_wire = browser_renderer_chrome_encode(
    7, 1, 12, "forward", false
)
val chrome_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), chrome_wire.wire
)
expect(browser_renderer_action_decode(chrome_message.message).value).to_equal("forward")
expect(browser_renderer_action_decode(chrome_message.message).pressed).to_be(false)

expect(browser_renderer_action_decode(BrowserRendererMessage(
    kind: "pointer", generation: 7, request_id: 1,
    payload: "P1\t09\t0\t0\t1"
)).ok).to_be(false)
expect(browser_renderer_action_decode(BrowserRendererMessage(
    kind: "text", generation: 7, request_id: 1,
    payload: "T1\t1\t2\nthree"
)).ok).to_be(false)
expect(browser_renderer_action_decode(BrowserRendererMessage(
    kind: "chrome", generation: 7, request_id: 1,
    payload: "C1\t1\t0\t6\nreload"
)).ok).to_be(false)
expect(browser_renderer_action_decode(BrowserRendererMessage(
    kind: "advance", generation: 7, request_id: 1,
    payload: "A1\t1\ttrailing"
)).ok).to_be(false)
```

</details>

#### round-trips typed navigation and rejects noncanonical shapes

- Round-trip typed navigation and submit noncanonical messages
- browser renderer decoder new
   - Expected: opened.action equals `open`
   - Expected: opened.url equals `https://example.test/form`
   - Expected: opened.method equals `POST`
   - Expected: opened.body equals `name=value`
- browser renderer decoder new


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Round-trip typed navigation and submit noncanonical messages")
val open_wire = browser_renderer_navigation_encode(
    7, 1, "open", "https://example.test/form", "POST",
    "X-Test: one", "name=value",
    "application/x-www-form-urlencoded"
)
expect(open_wire.ok).to_be(true)
val open_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), open_wire.wire
)
val opened = browser_renderer_navigation_decode(
    open_message.message
)
expect(opened.ok).to_be(true)
expect(opened.action).to_equal("open")
expect(opened.url).to_equal("https://example.test/form")
expect(opened.method).to_equal("POST")
expect(opened.body).to_equal("name=value")

val stop_wire = browser_renderer_navigation_encode(
    7, 1, "stop", "", "", "", "", ""
)
expect(stop_wire.ok).to_be(true)
val stop_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), stop_wire.wire
)
expect(browser_renderer_navigation_decode(
    stop_message.message
).action).to_equal("stop")

expect(browser_renderer_navigation_encode(
    7, 1, "back", "https://example.test/old", "POST",
    "", "", ""
).ok).to_be(false)
expect(browser_renderer_navigation_decode(BrowserRendererMessage(
    kind: "navigation", generation: 7, request_id: 1,
    payload: "SBN1\t4\t1\t3\t0\t0\t0\nopenxGETtrailing"
)).ok).to_be(false)
```

</details>

#### round-trips canonical DrawIR and fails closed on malformed stale duplicate or oversized frames

- Round-trip a canonical DrawIR frame and submit invalid frame variants
- var decoded = browser renderer decoder feed
   - Expected: decoded.status equals `need_more`
- decoded = browser renderer decoder feed
   - Expected: decoded.status equals `message`
   - Expected: decoded.message.kind equals `frame`
   - Expected: decoded.message.generation equals `7`
   - Expected: decoded.message.request_id equals `1`
   - Expected: frame.reply_to_request_id equals `1`
   - Expected: frame.next_animation_ms equals `-1`
   - Expected: frame.history_current_url equals ``
   - Expected: frame.history_back_url equals ``
   - Expected: frame.history_forward_url equals ``
   - Expected: frame.composition.backend_target equals `DRAW_IR_BACKEND_AUTO`
   - Expected: frame.composition.batches[0].backend_target equals `DRAW_IR_BACKEND_AUTO`
   - Expected: frame.cpu_composited_count equals `0`
   - Expected: frame.diagnostics equals ``
-  renderer protocol fixture
- browser renderer decoder new
   - Expected: witnessed_frame.reply_to_request_id equals `41`
   - Expected: witnessed_frame.next_animation_ms equals `33`
   - Expected: witnessed_frame.cpu_composited_count equals `1`
-  renderer protocol fixture
- browser renderer decoder new
   - Expected: diagnostic_frame.reply_to_request_id equals `42`
   - Expected: diagnostic_frame.history_current_url equals ``
   - Expected: diagnostic_frame.history_back_url equals ``
   - Expected: diagnostic_frame.history_forward_url equals ``
-  renderer protocol fixture
- browser renderer decoder new
   - Expected: state_frame.diagnostics equals `history diagnostics`
-  renderer protocol fixture
-  renderer protocol fixture
- 0, "", 0, "", "", ["x"; 8193] join
- state message message payload index of
- state message message payload len
   - Expected: malformed_state.reason equals `malformed-frame-state`
- browser renderer decoder new
   - Expected: image_frame.image_resources.len() equals `1`
   - Expected: image_frame.image_resources[0].image_uri equals `image_uri`
- image state wire len
- browser renderer decoder new
   - Expected: retained_image_frame.composition_revision equals `1`
- retained header slice
- retained image message message payload len
   - Expected: legacy_retained_frame.composition_revision equals `-1`
- browser renderer decoder new
   - Expected: changed_image_frame.composition_revision equals `2`
- browser renderer decoder new
   - Expected: mixed_image_frame.image_resources.len() equals `2`
-  renderer protocol image fixture
-  renderer protocol fixture
   - Expected: referenced_resources.len() equals `2`
   - Expected: referenced_resources[0].image_uri equals `image_uri`
   - Expected: referenced_resources[1].image_uri equals `second_uri`
   - Expected: missing_resources.len() equals `0`
-  renderer protocol fixture
- browser renderer decoder new
-  renderer protocol fixture
- duplicate resources push
- duplicate resources push
- browser renderer decoder new
-  renderer protocol fixture
- browser renderer decoder new
- empty header end + 1, empty message payload len
- var incomplete canvas =  renderer protocol fixture
- browser renderer decoder new
   - Expected: incomplete_frame.reason equals `invalid-canvas`
- browser renderer decoder new
   - Expected: unicode_decoded.message.payload equals `h\u00e9`
- unicode decoded = browser renderer decoder feed
   - Expected: unicode_decoded.message.request_id equals `2`
   - Expected: unicode_decoded.message.payload equals `ok`
- payload parts push
- browser renderer decoder new
- fragmented wire slice
- fragment end = fragmented wire len
- fragmented wire slice
   - Expected: fragmented.status equals `message`
   - Expected: fragmented.message.request_id equals `1`
   - Expected: fragmented.message.payload equals `maximum_payload`
- fragmented = browser renderer decoder feed
   - Expected: fragmented.status equals `message`
   - Expected: fragmented.message.request_id equals `2`
   - Expected: fragmented.message.payload equals `tail`
- BrowserRendererMessage
   - Expected: wrong_kind.reason equals `wrong-kind`
- var hostile composition =  renderer protocol fixture
   - Expected: hostile_message.status equals `message`
   - Expected: hostile_frame.reason equals `invalid-embedding`
- var coordinate composition =  renderer protocol fixture
   - Expected: coordinate_message.status equals `message`
   - Expected: coordinate_frame.reason equals `invalid-command-bounds`
- var metadata composition =  renderer protocol fixture
- draw ir style prop
   - Expected: metadata_frame.reason equals `invalid-command-metadata`
- var kind composition =  renderer protocol fixture
- browser renderer decoder new
- var overdraw composition =  renderer protocol fixture
- browser renderer decoder new
- browser renderer decoder new
- var style count composition =  renderer protocol fixture
- hostile styles push
   - Expected: style_count_frame.reason equals `invalid-command-metadata`
   - Expected: duplicate.status equals `violation`
   - Expected: duplicate.decoder.error equals `duplicate-request`
- browser renderer decoder new
- browser renderer message encode
- browser renderer message encode
   - Expected: skipped_sequence.status equals `violation`
- browser renderer message encode
   - Expected: next_sequence.status equals `message`
   - Expected: next_sequence.message.payload equals `two`
- browser renderer pointer encode
- browser renderer decoder new
   - Expected: resequenced_message.message.kind equals `pointer`
   - Expected: resequenced_message.message.request_id equals `4`
   - Expected: stale.status equals `violation`
   - Expected: stale.decoder.error equals `stale-generation`
   - Expected: malformed.status equals `violation`
   - Expected: malformed.decoder.error equals `malformed-header`
- browser renderer decoder new
   - Expected: oversized.status equals `violation`
   - Expected: oversized.decoder.error equals `payload-too-large`


<details>
<summary>Executable SSpec</summary>

Runnable source: 707 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Round-trip a canonical DrawIR frame and submit invalid frame variants")
val encoded = browser_renderer_frame_encode(_renderer_protocol_fixture(), 7, 1)
expect(encoded.ok).to_be(true)

var decoded = browser_renderer_decoder_feed(browser_renderer_decoder_new(7), encoded.wire.slice(0, 11))
expect(decoded.status).to_equal("need_more")
decoded = browser_renderer_decoder_feed(decoded.decoder, encoded.wire.slice(11, encoded.wire.len()))
expect(decoded.status).to_equal("message")
expect(decoded.message.kind).to_equal("frame")
expect(decoded.message.generation).to_equal(7)
expect(decoded.message.request_id).to_equal(1)

val frame = browser_renderer_frame_decode(decoded.message, 64, 48)
expect(frame.ok).to_be(true)
expect(frame.reply_to_request_id).to_equal(1)
expect(frame.next_animation_ms).to_equal(-1)
expect(frame.history_state_present).to_be(false)
expect(frame.history_current_url).to_equal("")
expect(frame.history_back_url).to_equal("")
expect(frame.history_forward_url).to_equal("")
expect(frame.composition.backend_target).to_equal(DRAW_IR_BACKEND_AUTO)
expect(frame.composition.batches[0].backend_target).to_equal(DRAW_IR_BACKEND_AUTO)
expect(frame.cpu_composited_count).to_equal(0)
expect(frame.diagnostics).to_equal("")

val witnessed = browser_renderer_frame_encode_with_witness(
    _renderer_protocol_fixture(),
    7,
    2,
    41,
    33,
    1,
    "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
    0,
    ""
)
val witnessed_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), witnessed.wire
)
val witnessed_frame = browser_renderer_frame_decode(
    witnessed_message.message, 64, 48
)
expect(witnessed_frame.ok).to_be(true)
expect(witnessed_frame.reply_to_request_id).to_equal(41)
expect(witnessed_frame.next_animation_ms).to_equal(33)
expect(witnessed_frame.cpu_composited_count).to_equal(1)
expect(witnessed_frame.cpu_composited_sha256).to_equal(
    "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
)

val diagnostic = browser_renderer_frame_encode_with_diagnostics(
    _renderer_protocol_fixture(),
    7,
    3,
    42,
    -1,
    0,
    "",
    0,
    "",
    "browser native globals: undefined:undefined:undefined"
)
expect(diagnostic.ok).to_be(true)
val diagnostic_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), diagnostic.wire
)
val diagnostic_frame = browser_renderer_frame_decode(
    diagnostic_message.message, 64, 48
)
expect(diagnostic_frame.ok).to_be(true)
expect(diagnostic_frame.reply_to_request_id).to_equal(42)
expect(diagnostic_frame.diagnostics).to_equal(
    "browser native globals: undefined:undefined:undefined"
)
expect(diagnostic_frame.history_state_present).to_be(false)
expect(diagnostic_frame.history_current_url).to_equal("")
expect(diagnostic_frame.history_back_url).to_equal("")
expect(diagnostic_frame.history_forward_url).to_equal("")

val state = browser_renderer_frame_encode_with_state(
    _renderer_protocol_fixture(),
    7,
    4,
    43,
    44,
    0,
    "",
    0,
    "",
    "history diagnostics",
    "https://example.test/caf\u00e9?q=1#section",
    "https://example.test/back?tab=a",
    "https://example.test/forward?tab=b"
)
expect(state.ok).to_be(true)
val state_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), state.wire
)
expect(browser_renderer_frame_reply_to_request_id(
    state_message.message
)).to_equal(43)
val state_frame = browser_renderer_frame_decode(
    state_message.message, 64, 48
)
expect(state_frame.ok).to_be(true)
expect(state_frame.history_state_present).to_be(true)
expect(state_frame.history_current_url).to_equal(
    "https://example.test/caf\u00e9?q=1#section"
)
expect(state_frame.history_back_url).to_equal(
    "https://example.test/back?tab=a"
)
expect(state_frame.history_forward_url).to_equal(
    "https://example.test/forward?tab=b"
)
expect(state_frame.diagnostics).to_equal("history diagnostics")
expect(browser_renderer_frame_encode_with_state(
    _renderer_protocol_fixture(), 7, 5, 44, -1,
    0, "", 0, "", "", "https://example.test/\nforged", "", ""
).ok).to_be(false)
expect(browser_renderer_frame_encode_with_state(
    _renderer_protocol_fixture(), 7, 5, 44, -1,
    0, "", 0, "", "", ["x"; 8193].join(""), "", ""
).ok).to_be(false)
val malformed_state = browser_renderer_frame_decode(
    BrowserRendererMessage(
        kind: "frame", generation: 7, request_id: 5,
        payload: "SBRF4\t44\t0\t-\t0\t-\t-1\t0\t10925\t0\t0\n" +
            state_message.message.payload.slice(
                state_message.message.payload.index_of("\n") + 1,
                state_message.message.payload.len()
            )
    ),
    64,
    48
)
expect(malformed_state.ok).to_be(false)
expect(malformed_state.reason).to_equal("malformed-frame-state")

val image_uri = "https://example.test/pixel.png"
val image_composition = _renderer_protocol_image_fixture(image_uri)
var image_resources: [SimpleOsHostGpuImageResource] = []
image_resources.push(simpleos_host_gpu_image_resource(
    image_uri, 4, 4, [0xffc080feu32; 16]
))
val image_state = browser_renderer_frame_encode_with_state_and_images(
    image_composition,
    7,
    5,
    45,
    -1,
    0,
    "",
    0,
    "",
    "",
    "https://example.test/image",
    "",
    "",
    image_resources
)
expect(image_state.ok).to_be(true)
val image_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), image_state.wire
)
expect(browser_renderer_frame_reply_to_request_id(
    image_message.message
)).to_equal(45)
val image_frame = browser_renderer_frame_decode(
    image_message.message, 64, 48
)
expect(image_frame.ok).to_be(true)
expect(image_frame.history_state_present).to_be(true)
expect(image_frame.image_resources.len()).to_equal(1)
expect(image_frame.image_resources[0].image_uri).to_equal(image_uri)
expect(image_frame.image_resources[0].pixels[0]).to_equal(
    0xffc080feu32
)
val image_revisions = browser_renderer_image_resource_revisions(
    image_resources
)
val retained_image_state = (
    browser_renderer_frame_encode_with_state_and_retained_images(
        image_composition, 7, 6, 46, 16, 0, "", 0, "",
        "", "https://example.test/image", "", "",
        1, image_resources, image_revisions
    )
)
expect(retained_image_state.ok).to_be(true)
expect(retained_image_state.wire.contains("SBRF7")).to_be(true)
expect(retained_image_state.wire.len()).to_be_less_than(
    image_state.wire.len()
)
val retained_image_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), retained_image_state.wire
)
expect(browser_renderer_frame_decode(
    retained_image_message.message, 64, 48
).reason).to_equal("image-resources-unknown-image-resource")
val retained_image_frame = (
    browser_renderer_frame_decode_with_retained_images(
        retained_image_message.message, 64, 48, image_resources
    )
)
expect(retained_image_frame.ok).to_be(true)
expect(retained_image_frame.composition_revision).to_equal(1)
expect(retained_image_frame.image_resources[0].pixels[0]).to_equal(
    0xffc080feu32
)
val retained_header_end = retained_image_message.message.payload.index_of(
    "\n"
)
val retained_header = retained_image_message.message.payload.slice(
    0, retained_header_end
)
val retained_revision_start = retained_header.last_index_of("\t")
expect(retained_header).to_start_with("SBRF7\t")
expect(retained_revision_start).to_be_greater_than(4)
val legacy_retained_message = BrowserRendererMessage(
    kind: "frame",
    generation: retained_image_message.message.generation,
    request_id: retained_image_message.message.request_id,
    payload: "SBRF6" +
        retained_header.slice(5, retained_revision_start) + "\n" +
        retained_image_message.message.payload.slice(
            retained_header_end + 1,
            retained_image_message.message.payload.len()
        )
)
val legacy_retained_frame = (
    browser_renderer_frame_decode_with_retained_images(
        legacy_retained_message, 64, 48, image_resources
    )
)
expect(legacy_retained_frame.ok).to_be(true)
expect(legacy_retained_frame.composition_revision).to_equal(-1)
expect(legacy_retained_frame.image_resources[0].pixels[0]).to_equal(
    0xffc080feu32
)
val changed_image_resources = [
    simpleos_host_gpu_image_resource(
        image_uri, 4, 4, [0xff010203u32; 16]
    )
]
val changed_image_state = (
    browser_renderer_frame_encode_with_state_and_retained_images(
        image_composition, 7, 7, 47, 32, 0, "", 0, "",
        "", "https://example.test/image", "", "",
        2, changed_image_resources, image_revisions
    )
)
expect(changed_image_state.ok).to_be(true)
expect(changed_image_state.wire.contains("SBRF7")).to_be(true)
val changed_image_frame = browser_renderer_frame_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(7), changed_image_state.wire
    ).message,
    64,
    48
)
expect(changed_image_frame.ok).to_be(true)
expect(changed_image_frame.composition_revision).to_equal(2)
expect(changed_image_frame.image_resources[0].pixels[0]).to_equal(
    0xff010203u32
)
val second_uri = "https://example.test/second.png"
var ordered_composition = image_composition
var ordered_batches = ordered_composition.batches
var ordered_batch = ordered_batches[0]
var ordered_commands = ordered_batch.commands
ordered_commands.push(draw_ir_image_command(
    "second-image", 8, 4, 1, 1, second_uri, []
))
ordered_commands.push(draw_ir_image_command(
    "duplicate-hero-image", 10, 4, 2, 1, image_uri, []
))
ordered_batch.commands = ordered_commands
ordered_batches[0] = ordered_batch
ordered_composition.batches = ordered_batches
val second_resource = simpleos_host_gpu_image_resource(
    second_uri, 1, 1, [0xff556677u32]
)
val unused_resource = simpleos_host_gpu_image_resource(
    "https://example.test/unused.png", 1, 1, [0xff778899u32]
)
val mixed_image_state = (
    browser_renderer_frame_encode_with_state_and_retained_images(
        ordered_composition, 7, 8, 48, 48, 0, "", 0, "",
        "", "https://example.test/image", "", "",
        3, [image_resources[0], second_resource], image_revisions
    )
)
expect(mixed_image_state.ok).to_be(true)
expect(mixed_image_state.wire.contains("SBRF7")).to_be(true)
val mixed_image_frame = (
    browser_renderer_frame_decode_with_retained_images(
        browser_renderer_decoder_feed(
            browser_renderer_decoder_new(7), mixed_image_state.wire
        ).message,
        64,
        48,
        image_resources
    )
)
expect(mixed_image_frame.ok).to_be(true)
expect(mixed_image_frame.image_resources.len()).to_equal(2)
expect(mixed_image_frame.image_resources[0].pixels[0]).to_equal(
    0xffc080feu32
)
expect(mixed_image_frame.image_resources[1].pixels[0]).to_equal(
    0xff556677u32
)
val tiny_revisions = browser_renderer_image_resource_revisions([
    second_resource
])
val tiny_image_state = (
    browser_renderer_frame_encode_with_state_and_retained_images(
        _renderer_protocol_image_fixture(second_uri),
        7, 9, 49, 64, 0, "", 0, "", "", "", "", "",
        4, [second_resource], tiny_revisions
    )
)
expect(tiny_image_state.ok).to_be(true)
expect(tiny_image_state.wire.contains("SBRF7")).to_be(true)
expect(
    browser_renderer_frame_encode_with_state_and_retained_images(
        _renderer_protocol_fixture(),
        7, 10, 50, -1, 0, "", 0, "", "", "", "", "",
        -1, [], []
    ).reason
).to_equal("invalid-composition-revision")
val referenced_resources = browser_renderer_referenced_image_resources(
    ordered_composition,
    [unused_resource, second_resource, image_resources[0]]
)
expect(referenced_resources.len()).to_equal(2)
expect(referenced_resources[0].image_uri).to_equal(image_uri)
expect(referenced_resources[1].image_uri).to_equal(second_uri)
val missing_resources = browser_renderer_referenced_image_resources(
    image_composition, []
)
expect(missing_resources.len()).to_equal(0)
expect(browser_renderer_frame_encode_with_state_and_images(
    image_composition, 7, 6, 46, -1, 0, "", 0, "",
    "", "", "", "", missing_resources
).reason).to_equal("image-resources-missing-image-resource")
val empty_image_state = browser_renderer_frame_encode_with_state_and_images(
    _renderer_protocol_fixture(), 7, 6, 46, -1,
    0, "", 0, "", "", "", "", "", []
)
expect(empty_image_state.ok).to_be(true)
expect(browser_renderer_frame_decode(
    browser_renderer_decoder_feed(
        browser_renderer_decoder_new(7), empty_image_state.wire
    ).message,
    64,
    48
).image_resources.len()).to_equal(0)

expect(browser_renderer_frame_encode_with_state_and_images(
    image_composition, 7, 6, 46, -1, 0, "", 0, "",
    "", "", "", "", []
).reason).to_equal("image-resources-missing-image-resource")
expect(browser_renderer_frame_encode_with_state_and_images(
    _renderer_protocol_fixture(), 7, 6, 46, -1, 0, "", 0, "",
    "", "", "", "", image_resources
).reason).to_equal("image-resources-unreferenced-image-resource")
var duplicate_resources: [SimpleOsHostGpuImageResource] = []
duplicate_resources.push(image_resources[0])
duplicate_resources.push(image_resources[0])
expect(browser_renderer_frame_encode_with_state_and_images(
    image_composition, 7, 6, 46, -1, 0, "", 0, "",
    "", "", "", "", duplicate_resources
).reason).to_equal("image-resources-duplicate-image-uri")
val oversized_resource = simpleos_host_gpu_image_resource(
    image_uri, 513, 256, [0xff112233u32; 131328]
)
expect(browser_renderer_frame_encode_with_state_and_images(
    image_composition, 7, 6, 46, -1, 0, "", 0, "",
    "", "", "", "", [oversized_resource]
).ok).to_be(false)

val unresolved_state = browser_renderer_frame_encode_with_state(
    image_composition, 7, 6, 46, -1, 0, "", 0, "",
    "", "", "", ""
)
val unresolved_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), unresolved_state.wire
)
expect(browser_renderer_frame_decode(
    unresolved_message.message, 64, 48
).reason).to_equal("image-resources-missing-image-resource")

val empty_state = browser_renderer_frame_encode_with_state(
    _renderer_protocol_fixture(), 7, 6, 46, -1, 0, "", 0, "",
    "", "", "", ""
)
val empty_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), empty_state.wire
).message
val empty_header_end = empty_message.payload.index_of("\n")
val empty_draw_ir = empty_message.payload.slice(
    empty_header_end + 1, empty_message.payload.len()
)
val trailing_image_bytes = BrowserRendererMessage(
    kind: "frame",
    generation: 7,
    request_id: 6,
    payload: "SBRF5\t46\t0\t-\t0\t-\t-1\t0\t0\t0\t0\t0\t1\t2\n" +
        "AA" + empty_draw_ir
)
expect(browser_renderer_frame_decode(
    trailing_image_bytes, 64, 48
).reason).to_equal("image-resources-trailing-bytes")
val noncanonical_image_bytes = BrowserRendererMessage(
    kind: "frame",
    generation: 7,
    request_id: 6,
    payload: "SBRF5\t46\t0\t-\t0\t-\t-1\t0\t0\t0\t0\t0\t1\t2\n" +
        "A=" + empty_draw_ir
)
expect(browser_renderer_frame_decode(
    noncanonical_image_bytes, 64, 48
).reason).to_equal("invalid-image-resources")
val oversized_image_header = BrowserRendererMessage(
    kind: "frame",
    generation: 7,
    request_id: 6,
    payload: "SBRF5\t46\t0\t-\t0\t-\t-1\t0\t0\t0\t0\t0\t1\t699052\n" +
        empty_draw_ir
)
expect(browser_renderer_frame_decode(
    oversized_image_header, 64, 48
).reason).to_equal("malformed-image-resources")
val excessive_resource_count = BrowserRendererMessage(
    kind: "frame",
    generation: 7,
    request_id: 6,
    payload: "SBRF5\t46\t0\t-\t0\t-\t-1\t0\t0\t0\t0\t65\t0\t0\n" +
        empty_draw_ir
)
expect(browser_renderer_frame_decode(
    excessive_resource_count, 64, 48
).reason).to_equal("malformed-image-resources")

var incomplete_canvas = _renderer_protocol_fixture()
var incomplete_batches = incomplete_canvas.batches
var incomplete_batch = incomplete_batches[0]
var incomplete_commands = incomplete_batch.commands
var incomplete_command = incomplete_commands[0]
incomplete_command.width = 63
incomplete_commands[0] = incomplete_command
incomplete_batch.commands = incomplete_commands
incomplete_batches[0] = incomplete_batch
incomplete_canvas.batches = incomplete_batches
val incomplete_wire = browser_renderer_frame_encode(
    incomplete_canvas, 7, 3
)
val incomplete_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), incomplete_wire.wire
)
val incomplete_frame = browser_renderer_frame_decode(
    incomplete_message.message, 64, 48
)
expect(incomplete_frame.ok).to_be(false)
expect(incomplete_frame.reason).to_equal("invalid-canvas")

val unicode_first = browser_renderer_message_encode("state", 7, 1, "h\u00e9")
val unicode_second = browser_renderer_message_encode("state", 7, 2, "ok")
var unicode_decoded = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7),
    unicode_first.wire + unicode_second.wire
)
expect(unicode_decoded.message.payload).to_equal("h\u00e9")
unicode_decoded = browser_renderer_decoder_feed(unicode_decoded.decoder, "")
expect(unicode_decoded.message.request_id).to_equal(2)
expect(unicode_decoded.message.payload).to_equal("ok")

var payload_piece = "x"
var doubling = 0
while doubling < 13:
    payload_piece = payload_piece + payload_piece
    doubling = doubling + 1
var payload_parts: [text] = []
while payload_parts.len() < 128:
    payload_parts.push(payload_piece)
val maximum_payload = payload_parts.join("")
expect(maximum_payload.len()).to_equal(
    BROWSER_RENDERER_MAX_PAYLOAD_BYTES
)
val maximum_wire = browser_renderer_message_encode(
    "state", 7, 1, maximum_payload
)
val trailing_wire = browser_renderer_message_encode(
    "state", 7, 2, "tail"
)
val fragmented_wire = maximum_wire.wire + trailing_wire.wire
var fragmented = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7),
    fragmented_wire.slice(0, 8191)
)
var fragment_start: i64 = 8191
while fragment_start < fragmented_wire.len():
    var fragment_end = fragment_start + 8191
    if fragment_end > fragmented_wire.len():
        fragment_end = fragmented_wire.len()
    fragmented = browser_renderer_decoder_feed(
        fragmented.decoder,
        fragmented_wire.slice(fragment_start, fragment_end)
    )
    fragment_start = fragment_end
expect(fragmented.status).to_equal("message")
expect(fragmented.message.request_id).to_equal(1)
expect(fragmented.message.payload).to_equal(maximum_payload)
fragmented = browser_renderer_decoder_feed(fragmented.decoder, "")
expect(fragmented.status).to_equal("message")
expect(fragmented.message.request_id).to_equal(2)
expect(fragmented.message.payload).to_equal("tail")

val wrong_kind = browser_renderer_frame_decode(
    BrowserRendererMessage(kind: "state", generation: 7, request_id: 1, payload: decoded.message.payload),
    64,
    48
)
expect(wrong_kind.ok).to_be(false)
expect(wrong_kind.reason).to_equal("wrong-kind")

var hostile_composition = _renderer_protocol_fixture()
var hostile_batches = hostile_composition.batches
var hostile_batch = hostile_batches[0]
var hostile_embedding = hostile_batch.embedding
hostile_embedding.x = 1
hostile_batch.embedding = hostile_embedding
hostile_batches[0] = hostile_batch
hostile_composition.batches = hostile_batches
val hostile_wire = browser_renderer_frame_encode(hostile_composition, 7, 2)
expect(hostile_wire.ok).to_be(true)
val hostile_message = browser_renderer_decoder_feed(browser_renderer_decoder_new(7), hostile_wire.wire)
expect(hostile_message.status).to_equal("message")
val hostile_frame = browser_renderer_frame_decode(hostile_message.message, 64, 48)
expect(hostile_frame.ok).to_be(false)
expect(hostile_frame.reason).to_equal("invalid-embedding")

var coordinate_composition = _renderer_protocol_fixture()
var coordinate_batches = coordinate_composition.batches
var coordinate_batch = coordinate_batches[0]
var coordinate_commands = coordinate_batch.commands
var coordinate_command = coordinate_commands[0]
coordinate_command.x = 2147483647
coordinate_commands[0] = coordinate_command
coordinate_batch.commands = coordinate_commands
coordinate_batches[0] = coordinate_batch
coordinate_composition.batches = coordinate_batches
val coordinate_wire = browser_renderer_frame_encode(coordinate_composition, 7, 2)
expect(coordinate_wire.ok).to_be(true)
val coordinate_message = browser_renderer_decoder_feed(browser_renderer_decoder_new(7), coordinate_wire.wire)
expect(coordinate_message.status).to_equal("message")
val coordinate_frame = browser_renderer_frame_decode(coordinate_message.message, 64, 48)
expect(coordinate_frame.ok).to_be(false)
expect(coordinate_frame.reason).to_equal("invalid-command-bounds")

var metadata_composition = _renderer_protocol_fixture()
var metadata_batches = metadata_composition.batches
var metadata_batch = metadata_batches[0]
var metadata_commands = metadata_batch.commands
var metadata_command = metadata_commands[0]
metadata_command.computed_style = [
    draw_ir_style_prop("font-size", "999999999999999999999999")
]
metadata_commands[0] = metadata_command
metadata_batch.commands = metadata_commands
metadata_batches[0] = metadata_batch
metadata_composition.batches = metadata_batches
val metadata_wire = browser_renderer_frame_encode(metadata_composition, 7, 2)
expect(metadata_wire.ok).to_be(true)
val metadata_message = browser_renderer_decoder_feed(browser_renderer_decoder_new(7), metadata_wire.wire)
val metadata_frame = browser_renderer_frame_decode(metadata_message.message, 64, 48)
expect(metadata_frame.ok).to_be(false)
expect(metadata_frame.reason).to_equal("invalid-command-metadata")

var kind_composition = _renderer_protocol_fixture()
var kind_batches = kind_composition.batches
var kind_batch = kind_batches[0]
var kind_commands = kind_batch.commands
var unsupported_command = kind_commands[1]
unsupported_command.kind = "path"
kind_commands[1] = unsupported_command
kind_batch.commands = kind_commands
kind_batches[0] = kind_batch
kind_composition.batches = kind_batches
val kind_wire = browser_renderer_frame_encode(
    kind_composition, 7, 2
)
val kind_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), kind_wire.wire
)
expect(browser_renderer_frame_decode(
    kind_message.message, 64, 48
).reason).to_equal("invalid-command-kind")

var overdraw_composition = _renderer_protocol_fixture()
var overdraw_batches = overdraw_composition.batches
var overdraw_batch = overdraw_batches[0]
val full_canvas = overdraw_batch.commands[0]
overdraw_batch.commands = [full_canvas; 16]
overdraw_batches[0] = overdraw_batch
overdraw_composition.batches = overdraw_batches
val bounded_overdraw_wire = browser_renderer_frame_encode(
    overdraw_composition, 7, 2
)
val bounded_overdraw_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), bounded_overdraw_wire.wire
)
expect(browser_renderer_frame_decode(
    bounded_overdraw_message.message, 64, 48
).ok).to_be(true)

overdraw_batch.commands = [full_canvas; 17]
overdraw_batches[0] = overdraw_batch
overdraw_composition.batches = overdraw_batches
val excessive_overdraw_wire = browser_renderer_frame_encode(
    overdraw_composition, 7, 2
)
val excessive_overdraw_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), excessive_overdraw_wire.wire
)
val excessive_overdraw_frame = browser_renderer_frame_decode(
    excessive_overdraw_message.message, 64, 48
)
expect(excessive_overdraw_frame.ok).to_be(false)
expect(excessive_overdraw_frame.reason).to_equal(
    "frame-work-budget-exceeded"
)

var style_count_composition = _renderer_protocol_fixture()
var style_count_batches = style_count_composition.batches
var style_count_batch = style_count_batches[0]
var style_count_commands = style_count_batch.commands
var style_count_command = style_count_commands[0]
var hostile_styles: [DrawIrStyleProp] = []
var style_index = 0
while style_index < 161:
    hostile_styles.push(draw_ir_style_prop("x{style_index}", "v"))
    style_index = style_index + 1
style_count_command.computed_style = hostile_styles
style_count_commands[0] = style_count_command
style_count_batch.commands = style_count_commands
style_count_batches[0] = style_count_batch
style_count_composition.batches = style_count_batches
val style_count_wire = browser_renderer_frame_encode(style_count_composition, 7, 2)
val style_count_message = browser_renderer_decoder_feed(browser_renderer_decoder_new(7), style_count_wire.wire)
val style_count_frame = browser_renderer_frame_decode(style_count_message.message, 64, 48)
expect(style_count_frame.ok).to_be(false)
expect(style_count_frame.reason).to_equal("invalid-command-metadata")

val duplicate = browser_renderer_decoder_feed(decoded.decoder, encoded.wire)
expect(duplicate.status).to_equal("violation")
expect(duplicate.decoder.error).to_equal("duplicate-request")

val first_sequence = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7),
    browser_renderer_message_encode("state", 7, 1, "one").wire
)
val skipped_sequence = browser_renderer_decoder_feed(
    first_sequence.decoder,
    browser_renderer_message_encode("state", 7, 3, "three").wire
)
expect(skipped_sequence.status).to_equal("violation")
expect(skipped_sequence.decoder.error).to_equal(
    "unexpected-request-id"
)
val next_sequence = browser_renderer_decoder_feed(
    first_sequence.decoder,
    browser_renderer_message_encode("state", 7, 2, "two").wire
)
expect(next_sequence.status).to_equal("message")
expect(next_sequence.message.payload).to_equal("two")

val resequenced = browser_renderer_message_resequence(
    browser_renderer_pointer_encode(7, 3, 9, 4, 5, true).wire,
    7, 4
)
expect(resequenced.ok).to_be(true)
val resequenced_message = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7), resequenced.wire
)
expect(resequenced_message.message.kind).to_equal("pointer")
expect(resequenced_message.message.request_id).to_equal(4)
expect(browser_renderer_message_resequence(
    resequenced.wire + resequenced.wire, 7, 5
).ok).to_be(false)

val stale_wire = browser_renderer_message_encode("state", 6, 2, "").wire
val stale = browser_renderer_decoder_feed(browser_renderer_decoder_new(7), stale_wire)
expect(stale.status).to_equal("violation")
expect(stale.decoder.error).to_equal("stale-generation")

val malformed = browser_renderer_decoder_feed(browser_renderer_decoder_new(7), "SBR1\tframe\t07\t2\t0\n")
expect(malformed.status).to_equal("violation")
expect(malformed.decoder.error).to_equal("malformed-header")

val oversized = browser_renderer_decoder_feed(
    browser_renderer_decoder_new(7),
    "SBR1\tframe\t7\t2\t{BROWSER_RENDERER_MAX_PAYLOAD_BYTES + 1}\n"
)
expect(oversized.status).to_equal("violation")
expect(oversized.decoder.error).to_equal("payload-too-large")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_renderer_protocol_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering isolated browser renderer protocol.
- isolated browser renderer protocol

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
