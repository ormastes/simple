# Simpleos Host Gpu Draw Ir Specification

> Tests covering SimpleOS host-GPU bounded Draw IR codec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Host Gpu Draw Ir Specification

## Scenarios

### SimpleOS host-GPU bounded Draw IR codec

#### round-trips the exact plain-rect subset with a deterministic checksum

- Encode one canonical Draw IR composition within the negotiated bounds
   - Expected: encoded.reason equals `ok`
   - Expected: encoded.command_count equals `1`
- Decode and verify exact schema IDs batch fields and command fields
   - Expected: decoded.composition.schema equals `DRAW_IR_SCHEMA_VERSION`
   - Expected: decoded.composition.composition_id equals `composition-1`
   - Expected: decoded.composition.scene_key equals `scene-1`
   - Expected: decoded.composition.backend_target equals `DRAW_IR_BACKEND_GPU`
   - Expected: decoded.composition.batches.len() equals `1`
   - Expected: decoded.composition.batches[0].schema equals `DRAW_IR_SCHEMA_VERSION`
   - Expected: decoded.composition.batches[0].batch_id equals `batch-1`
   - Expected: decoded.composition.batches[0].embedding.surface_id equals `surface-1`
   - Expected: decoded.composition.batches[0].embedding.component_id equals `window-1`
   - Expected: decoded.composition.batches[0].commands[0].kind equals `DRAW_IR_COMMAND_RECT`
   - Expected: decoded.composition.batches[0].commands[0].width equals `64`
- Re-encode the decoded value and require the same bytes and checksum
   - Expected: reencoded.bytes equals `encoded.bytes`
   - Expected: reencoded.checksum equals `encoded.checksum`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Encode one canonical Draw IR composition within the negotiated bounds")
val encoded = simpleos_host_gpu_draw_ir_encode(_host_gpu_draw_ir_fixture(), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(encoded.ok).to_be(true)
expect(encoded.reason).to_equal("ok")
expect(encoded.command_count).to_equal(1)
expect(encoded.checksum).to_be_greater_than(0)

step("Decode and verify exact schema IDs batch fields and command fields")
val decoded = simpleos_host_gpu_draw_ir_decode(encoded.bytes, DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(decoded.ok).to_be(true)
expect(decoded.composition.schema).to_equal(DRAW_IR_SCHEMA_VERSION)
expect(decoded.composition.composition_id).to_equal("composition-1")
expect(decoded.composition.scene_key).to_equal("scene-1")
expect(decoded.composition.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
expect(decoded.composition.batches.len()).to_equal(1)
expect(decoded.composition.batches[0].schema).to_equal(DRAW_IR_SCHEMA_VERSION)
expect(decoded.composition.batches[0].batch_id).to_equal("batch-1")
expect(decoded.composition.batches[0].embedding.surface_id).to_equal("surface-1")
expect(decoded.composition.batches[0].embedding.component_id).to_equal("window-1")
expect(decoded.composition.batches[0].commands[0].kind).to_equal(DRAW_IR_COMMAND_RECT)
expect(decoded.composition.batches[0].commands[0].width).to_equal(64)

step("Re-encode the decoded value and require the same bytes and checksum")
val reencoded = simpleos_host_gpu_draw_ir_encode(decoded.composition, DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(reencoded.bytes).to_equal(encoded.bytes)
expect(reencoded.checksum).to_equal(encoded.checksum)
```

</details>

#### rejects an encoded payload larger than the caller bound

- Set a byte bound smaller than the canonical SDN payload
   - Expected: encoded.reason equals `payload-too-large`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Set a byte bound smaller than the canonical SDN payload")
val encoded = simpleos_host_gpu_draw_ir_encode(_host_gpu_draw_ir_fixture(), 16, DRAW_IR_TEST_MAX_COMMANDS)
expect(encoded.ok).to_be(false)
expect(encoded.reason).to_equal("payload-too-large")
```

</details>

#### round-trips image semantics before resource attachment validation

- draw ir image command
   - Expected: decoded.composition.batches[0].commands[0].kind equals `DRAW_IR_COMMAND_IMAGE`
   - Expected: decoded.composition.batches[0].commands[0].image_uri equals `asset://image`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val embedding = draw_ir_embedding_config("surface-1", "window-1", 0, 0, 32, 32, 0, 1000, false)
val batch = draw_ir_batch("batch-image", DRAW_IR_BACKEND_GPU, embedding, [
    draw_ir_image_command("image-1", 0, 0, 16, 16, "asset://image", [])
])
val composition = draw_ir_composition("composition-image", "scene-image", DRAW_IR_BACKEND_GPU, [batch])
val encoded = simpleos_host_gpu_draw_ir_encode(composition, DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(encoded.ok).to_be(true)
val decoded = simpleos_host_gpu_draw_ir_decode(encoded.bytes, DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(decoded.ok).to_be(true)
expect(decoded.composition.batches[0].commands[0].kind).to_equal(DRAW_IR_COMMAND_IMAGE)
expect(decoded.composition.batches[0].commands[0].image_uri).to_equal("asset://image")
```

</details>

#### round-trips text and styled boxes exactly

- draw ir text
   - Expected: decoded_text.composition.batches[0].commands[0].kind equals `DRAW_IR_COMMAND_TEXT`
   - Expected: decoded_text.composition.batches[0].commands[0].text_value equals `SimpleOS`
   - Expected: decoded_styled.composition.batches[0].commands[0].computed_style[0].value equals `block`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val embedding = draw_ir_embedding_config("surface-1", "window-1", 0, 0, 32, 32, 0, 1000, false)
val text_batch = draw_ir_batch("batch-text", DRAW_IR_BACKEND_GPU, embedding, [
    draw_ir_text("title", 2, 12, "SimpleOS", 0xffffffffu32)
])
val text_payload = simpleos_host_gpu_draw_ir_encode(draw_ir_composition("composition-text", "scene-text", DRAW_IR_BACKEND_GPU, [text_batch]), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(text_payload.ok).to_be(true)
val decoded_text = simpleos_host_gpu_draw_ir_decode(text_payload.bytes, DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(decoded_text.ok).to_be(true)
expect(decoded_text.composition.batches[0].commands[0].kind).to_equal(DRAW_IR_COMMAND_TEXT)
expect(decoded_text.composition.batches[0].commands[0].text_value).to_equal("SimpleOS")

val styled_box = draw_ir_box_with_style("box", 0, 0, 32, 32, 0xff224466u32, draw_ir_rect_bounds(0, 0, 32, 32), draw_ir_rect_bounds(1, 1, 30, 30), draw_ir_rect_bounds(0, 0, 32, 32), draw_ir_rect_bounds(0, 0, 32, 32), [draw_ir_style_prop("display", "block")])
val styled_batch = draw_ir_batch("batch-styled", DRAW_IR_BACKEND_GPU, embedding, [styled_box])
val styled_payload = simpleos_host_gpu_draw_ir_encode(draw_ir_composition("composition-styled", "scene-styled", DRAW_IR_BACKEND_GPU, [styled_batch]), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(styled_payload.ok).to_be(true)
val decoded_styled = simpleos_host_gpu_draw_ir_decode(styled_payload.bytes, DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(decoded_styled.ok).to_be(true)
expect(decoded_styled.composition.batches[0].commands[0].border_rect.present).to_be(true)
expect(decoded_styled.composition.batches[0].commands[0].computed_style[0].value).to_equal("block")
```

</details>

#### rejects hierarchy commands until nested resource projection is supported

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val embedding = draw_ir_embedding_config("surface-1", "window-1", 0, 0, 32, 32, 0, 1000, false)
val batch = draw_ir_batch("batch-group", DRAW_IR_BACKEND_GPU, embedding, [draw_ir_group_command("child", "parent")])
val encoded = simpleos_host_gpu_draw_ir_encode(draw_ir_composition("composition-group", "scene-group", DRAW_IR_BACKEND_GPU, [batch]), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(encoded.ok).to_be(false)
expect(encoded.reason).to_equal("unsupported-command")
```

</details>

#### rejects empty compositions and empty payloads

- Reject a composition without batches
   - Expected: encoded.reason equals `empty-batches`
- Reject a zero-byte payload before SDN parsing
   - Expected: decoded.reason equals `empty-payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject a composition without batches")
val empty_composition = draw_ir_composition("composition-empty", "scene-empty", DRAW_IR_BACKEND_GPU, [])
val encoded = simpleos_host_gpu_draw_ir_encode(empty_composition, DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(encoded.ok).to_be(false)
expect(encoded.reason).to_equal("empty-batches")

step("Reject a zero-byte payload before SDN parsing")
val decoded = simpleos_host_gpu_draw_ir_decode([], DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(decoded.ok).to_be(false)
expect(decoded.reason).to_equal("empty-payload")
```

</details>

#### rejects a corrupted Draw IR schema before decoding

- Replace the exact schema version in an otherwise canonical payload
   - Expected: decoded.reason equals `schema-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Replace the exact schema version in an otherwise canonical payload")
val encoded = simpleos_host_gpu_draw_ir_encode(_host_gpu_draw_ir_fixture(), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
val corrupt_text = bytes_to_text(encoded.bytes).replace(DRAW_IR_SCHEMA_VERSION, "simple-draw-ir-v999")
val decoded = simpleos_host_gpu_draw_ir_decode(text_to_bytes(corrupt_text), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(decoded.ok).to_be(false)
expect(decoded.reason).to_equal("schema-mismatch")
```

</details>

#### rejects oversized offscreen batch dimensions before host execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = simpleos_host_gpu_draw_ir_encode(_host_gpu_draw_ir_fixture(), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
val hostile = bytes_to_text(encoded.bytes).replace(
    "surface=surface-1 component=window-1 x=4 y=6 width=64 height=48",
    "surface=surface-1 component=window-1 x=4 y=6 width={SIMPLEOS_HOST_GPU_MAX_WIDTH + 1} height=48"
)
val decoded = simpleos_host_gpu_draw_ir_decode(text_to_bytes(hostile), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(decoded.ok).to_be(false)
expect(decoded.reason).to_equal("batch-bounds-exceed-protocol")
```

</details>

#### rejects hostile inline metadata counts without expanding them

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val embedding = draw_ir_embedding_config("surface-1", "window-1", 0, 0, 32, 32, 0, 1000, false)
val styled = draw_ir_box_with_style("box", 0, 0, 32, 32, 0xff224466u32, draw_ir_rect_bounds(0, 0, 32, 32), draw_ir_rect_bounds(0, 0, 32, 32), draw_ir_rect_bounds(0, 0, 32, 32), draw_ir_rect_bounds(0, 0, 32, 32), [draw_ir_style_prop("display", "block")])
val encoded = simpleos_host_gpu_draw_ir_encode(draw_ir_composition("composition-styled", "scene-styled", DRAW_IR_BACKEND_GPU, [draw_ir_batch("batch-styled", DRAW_IR_BACKEND_GPU, embedding, [styled])]), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
val hostile = bytes_to_text(encoded.bytes).replace("style_count=1", "style_count=2147483647")
val decoded = simpleos_host_gpu_draw_ir_decode(text_to_bytes(hostile), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(decoded.ok).to_be(false)
expect(decoded.reason).to_equal("noncanonical-payload")
```

</details>

#### rejects an over-cap glyph count before expanding glyph fields

-  replace
-  replace
   - Expected: decoded.reason equals `noncanonical-payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = simpleos_host_gpu_draw_ir_encode(_host_gpu_draw_ir_fixture(), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
val hostile = bytes_to_text(encoded.bytes)
    .replace("glyph_valid=false", "glyph_valid=true")
    .replace("glyph_count=0", "glyph_count=4097")
val decoded = simpleos_host_gpu_draw_ir_decode(text_to_bytes(hostile), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(decoded.ok).to_be(false)
expect(decoded.reason).to_equal("noncanonical-payload")
```

</details>

#### rejects excess SDN records before splitting or allocating batches

- var hostile = bytes to text
   - Expected: decoded.reason equals `too-many-records`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = simpleos_host_gpu_draw_ir_encode(_host_gpu_draw_ir_fixture(), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
var hostile = bytes_to_text(encoded.bytes)
var index = 0
while index < 20:
    hostile = hostile + "\n\tbatch id=x backend=gpu"
    index = index + 1
val decoded = simpleos_host_gpu_draw_ir_decode(text_to_bytes(hostile), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(decoded.ok).to_be(false)
expect(decoded.reason).to_equal("too-many-records")
```

</details>

#### rejects a junk-heavy command record without token-array amplification

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = simpleos_host_gpu_draw_ir_encode(_host_gpu_draw_ir_fixture(), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
var junk = ""
var index = 0
while index < 1000:
    junk = junk + " junk{index}=x"
    index = index + 1
val hostile = bytes_to_text(encoded.bytes).replace("command kind=", "command{junk} kind=")
val decoded = simpleos_host_gpu_draw_ir_decode(text_to_bytes(hostile), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(decoded.ok).to_be(false)
expect(decoded.reason).to_equal("noncanonical-payload")
```

</details>

#### round-trips zero and one canonical image resource

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = simpleos_host_gpu_image_resources_encode([], DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(empty.ok).to_be(true)
expect(empty.bytes.len()).to_equal(0)
expect(empty.checksum).to_equal(0)
val decoded_empty = simpleos_host_gpu_image_resources_decode(empty.bytes, 0, empty.checksum, DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(decoded_empty.ok).to_be(true)
expect(decoded_empty.resources.len()).to_equal(0)

val resource = simpleos_host_gpu_image_resource("asset://icon-\u754c", 2, 1, [0xff112233u32, 0xff445566u32])
val encoded = simpleos_host_gpu_image_resources_encode([resource], DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(encoded.ok).to_be(true)
expect(encoded.resource_count).to_equal(1)
val decoded = simpleos_host_gpu_image_resources_decode(encoded.bytes, 1, encoded.checksum, DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(decoded.ok).to_be(true)
expect(decoded.resources[0].image_uri).to_equal("asset://icon-\u754c")
expect(decoded.resources[0].width).to_equal(2)
expect(decoded.resources[0].pixels).to_equal(resource.pixels)
```

</details>

#### round-trips multiple resources and requires exact unique image URI coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = simpleos_host_gpu_image_resource("asset://first", 1, 1, [0xff010203u32])
val second = simpleos_host_gpu_image_resource("asset://second", 1, 2, [0xff040506u32, 0xff070809u32])
val encoded = simpleos_host_gpu_image_resources_encode([first, second], DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
val decoded = simpleos_host_gpu_image_resources_decode(encoded.bytes, 2, encoded.checksum, DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(decoded.ok).to_be(true)
expect(decoded.resources.len()).to_equal(2)
expect(decoded.resources[1].pixels[1]).to_equal(0xff070809u32)

val composition = _host_gpu_image_composition(["asset://first", "asset://second"])
expect(simpleos_host_gpu_image_resource_coverage_reason(composition, [first, second])).to_equal("")
expect(simpleos_host_gpu_image_resource_coverage_reason(composition, [first])).to_equal("missing-image-resource")
val extra = simpleos_host_gpu_image_resource("asset://extra", 1, 1, [0xffffffffu32])
expect(simpleos_host_gpu_image_resource_coverage_reason(composition, [first, second, extra])).to_equal("unreferenced-image-resource")
val duplicate = simpleos_host_gpu_image_resources_encode([first, first], DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(duplicate.reason).to_equal("duplicate-image-uri")
```

</details>

#### validates image resources without payload allocation with encoder rejection parity

- near limit encoded bytes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 116 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = simpleos_host_gpu_image_resource(
    "asset://first", 1, 1, [0xff010203u32]
)
val second = simpleos_host_gpu_image_resource(
    "asset://second", 1, 2,
    [0xff040506u32, 0xff070809u32]
)
val valid = simpleos_host_gpu_image_resources_validate(
    [first, second],
    DRAW_IR_TEST_MAX_BYTES,
    DRAW_IR_TEST_MAX_COMMANDS
)
val encoded = simpleos_host_gpu_image_resources_encode(
    [first, second],
    DRAW_IR_TEST_MAX_BYTES,
    DRAW_IR_TEST_MAX_COMMANDS
)
expect(valid.ok).to_be(true)
expect(valid.reason).to_equal(encoded.reason)
expect(valid.resource_count).to_equal(encoded.resource_count)
expect(valid.total_bytes).to_equal(encoded.bytes.len().to_i64())

var near_limit_uri = ""
while near_limit_uri.len() + 3 <= (
    SIMPLEOS_HOST_GPU_MAX_IMAGE_URI_BYTES
):
    near_limit_uri = near_limit_uri + "\u754c"
while near_limit_uri.len() < SIMPLEOS_HOST_GPU_MAX_IMAGE_URI_BYTES:
    near_limit_uri = near_limit_uri + "x"
val near_limit = simpleos_host_gpu_image_resource(
    near_limit_uri, 1, 1, [0xff010203u32]
)
val near_limit_validation =
    simpleos_host_gpu_image_resources_validate(
        [near_limit],
        DRAW_IR_TEST_MAX_BYTES,
        DRAW_IR_TEST_MAX_COMMANDS
    )
val near_limit_encoded = simpleos_host_gpu_image_resources_encode(
    [near_limit],
    DRAW_IR_TEST_MAX_BYTES,
    DRAW_IR_TEST_MAX_COMMANDS
)
expect(near_limit_validation.ok).to_be(true)
expect(near_limit_validation.total_bytes).to_equal(
    near_limit_encoded.bytes.len().to_i64()
)

val malformed = SimpleOsHostGpuImageResource(
    image_uri: "asset://malformed",
    width: 2,
    height: 1,
    pixels: [0xff010203u32],
    pixel_checksum: first.pixel_checksum
)
_expect_image_resource_validation_parity(
    [first], -1, DRAW_IR_TEST_MAX_COMMANDS, "invalid-limits"
)
_expect_image_resource_validation_parity(
    [first, second], DRAW_IR_TEST_MAX_BYTES, 1,
    "too-many-resources"
)
_expect_image_resource_validation_parity(
    [first, first], DRAW_IR_TEST_MAX_BYTES,
    DRAW_IR_TEST_MAX_COMMANDS, "duplicate-image-uri"
)
_expect_image_resource_validation_parity(
    [first], 1, DRAW_IR_TEST_MAX_COMMANDS, "payload-too-large"
)
_expect_image_resource_validation_parity(
    [SimpleOsHostGpuImageResource(
        image_uri: "",
        width: 1,
        height: 1,
        pixels: [0xff010203u32],
        pixel_checksum: first.pixel_checksum
    )],
    DRAW_IR_TEST_MAX_BYTES,
    DRAW_IR_TEST_MAX_COMMANDS,
    "missing-image-uri"
)
var long_uri = ""
while long_uri.len().to_i64() <= (
    SIMPLEOS_HOST_GPU_MAX_IMAGE_URI_BYTES
):
    long_uri = long_uri + "x"
_expect_image_resource_validation_parity(
    [SimpleOsHostGpuImageResource(
        image_uri: long_uri,
        width: 1,
        height: 1,
        pixels: [0xff010203u32],
        pixel_checksum: first.pixel_checksum
    )],
    DRAW_IR_TEST_MAX_BYTES,
    DRAW_IR_TEST_MAX_COMMANDS,
    "invalid-image-uri"
)
_expect_image_resource_validation_parity(
    [SimpleOsHostGpuImageResource(
        image_uri: "asset://bad-dimensions",
        width: 0,
        height: 1,
        pixels: [],
        pixel_checksum: 0
    )],
    DRAW_IR_TEST_MAX_BYTES,
    DRAW_IR_TEST_MAX_COMMANDS,
    "invalid-image-dimensions"
)
_expect_image_resource_validation_parity(
    [malformed],
    DRAW_IR_TEST_MAX_BYTES,
    DRAW_IR_TEST_MAX_COMMANDS,
    "pixel-count-mismatch"
)
```

</details>

#### keeps image resource validation free of materialized byte buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text(
    "src/lib/common/gpu/simpleos_host_gpu_draw_ir.spl"
)
val validation_start = source.find(
    "fn simpleos_host_gpu_image_resources_validate("
)
val encoder_start = source.find(
    "fn simpleos_host_gpu_image_resources_encode(",
    validation_start
)
val reason_start = source.find(
    "fn _simpleos_host_gpu_image_resource_reason("
)
val reason_end = source.find(
    "fn _simpleos_host_gpu_draw_ir_validation_reason(",
    reason_start
)
expect(validation_start).to_be_greater_than(-1)
expect(encoder_start).to_be_greater_than(validation_start)
expect(reason_start).to_be_greater_than(-1)
expect(reason_end).to_be_greater_than(reason_start)
if validation_start >= 0 and encoder_start > validation_start:
    val validation_source = source.slice(
        validation_start, encoder_start
    )
    expect(validation_source.contains("text_to_bytes(")).to_be(false)
    expect(validation_source.contains(".push(")).to_be(false)
if reason_start >= 0 and reason_end > reason_start:
    val reason_source = source.slice(reason_start, reason_end)
    expect(reason_source.contains("text_to_bytes(")).to_be(false)
    expect(reason_source.contains(".push(")).to_be(false)
```

</details>

#### rejects malformed resource checksums padding records and trailing bytes

- var bad padding =  host gpu resource bytes copy
   - Expected: padding_result.reason equals `nonzero-padding`
- var bad pixel =  host gpu resource bytes copy
- bad pixel[pixel offset] =
   - Expected: pixel_result.reason equals `pixel-checksum-mismatch`
- var trailing =  host gpu resource bytes copy
- trailing push
   - Expected: trailing_result.reason equals `trailing-bytes`
- var bad record =  host gpu resource bytes copy
- bad record[0] =
   - Expected: record_result.reason equals `invalid-record-bytes`
   - Expected: checksum_result.reason equals `checksum-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resource = simpleos_host_gpu_image_resource("x", 1, 1, [0xff112233u32])
val encoded = simpleos_host_gpu_image_resources_encode([resource], DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)

var bad_padding = _host_gpu_resource_bytes_copy(encoded.bytes)
bad_padding[SIMPLEOS_HOST_GPU_IMAGE_RESOURCE_HEADER_BYTES + 1] = 1u8
val padding_result = simpleos_host_gpu_image_resources_decode(bad_padding, 1, _host_gpu_resource_checksum(bad_padding), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(padding_result.reason).to_equal("nonzero-padding")

var bad_pixel = _host_gpu_resource_bytes_copy(encoded.bytes)
val pixel_offset = SIMPLEOS_HOST_GPU_IMAGE_RESOURCE_HEADER_BYTES + 8
bad_pixel[pixel_offset] = (bad_pixel[pixel_offset].to_i64() ^ 1).to_u8()
val pixel_result = simpleos_host_gpu_image_resources_decode(bad_pixel, 1, _host_gpu_resource_checksum(bad_pixel), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(pixel_result.reason).to_equal("pixel-checksum-mismatch")

var trailing = _host_gpu_resource_bytes_copy(encoded.bytes)
trailing.push(0u8)
val trailing_result = simpleos_host_gpu_image_resources_decode(trailing, 1, _host_gpu_resource_checksum(trailing), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(trailing_result.reason).to_equal("trailing-bytes")

var bad_record = _host_gpu_resource_bytes_copy(encoded.bytes)
bad_record[0] = (bad_record[0].to_i64() + 1).to_u8()
val record_result = simpleos_host_gpu_image_resources_decode(bad_record, 1, _host_gpu_resource_checksum(bad_record), DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(record_result.reason).to_equal("invalid-record-bytes")

val checksum_result = simpleos_host_gpu_image_resources_decode(encoded.bytes, 1, encoded.checksum + 1, DRAW_IR_TEST_MAX_BYTES, DRAW_IR_TEST_MAX_COMMANDS)
expect(checksum_result.reason).to_equal("checksum-mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/gpu/simpleos_host_gpu_draw_ir_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS host-GPU bounded Draw IR codec.
- SimpleOS host-GPU bounded Draw IR codec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
