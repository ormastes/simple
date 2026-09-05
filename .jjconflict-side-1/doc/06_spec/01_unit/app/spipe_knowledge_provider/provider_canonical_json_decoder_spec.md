# Provider Canonical Json Decoder Specification

> Tests covering SPipe iterative canonical JSON decoder.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Canonical Json Decoder Specification

## Scenarios

### SPipe iterative canonical JSON decoder

#### emits closed events with exact nullable fields spans and counters

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-JSON
```

</details>

#### is invariant at every split and hashes exact raw bytes

- is invariant at every split and hashes exact raw bytes
   - Expected: divided.result.payload_sha256 equals `baseline.result.payload_sha256`
   - Expected: divided.events.len() equals `baseline.events.len()`
   - Expected: divided.events[i].kind equals `baseline.events[i].kind`
   - Expected: divided.events[i].byte_start equals `baseline.events[i].byte_start`
   - Expected: divided.events[i].byte_end equals `baseline.events[i].byte_end`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is invariant at every split and hashes exact raw bytes")
# Every possible split includes boundaries inside the two-, three-,
# and four-byte scalars. A partial prefix is resubmitted with enough
# following bytes to complete exactly one scalar.
val source = "{\"a\":123,\"b\":\"¢€😀\\n\"}"
val baseline = decode_json(source.bytes(), [source.bytes().len()]).unwrap()
expect(decode_json("{}".bytes(), [2]).unwrap().result.payload_sha256).to_equal(
    "44136fa355b3678a1146ad16f7e8649e94fb4fc21fe77e8310c060f61caaff8a")
var split = 1
while split < source.bytes().len():
    val divided = decode_json(source.bytes(), [split, source.bytes().len() - split]).unwrap()
    expect(divided.result.payload_sha256).to_equal(baseline.result.payload_sha256)
    expect(divided.events.len()).to_equal(baseline.events.len())
    var i = 0
    while i < baseline.events.len():
        expect(divided.events[i].kind).to_equal(baseline.events[i].kind)
        expect(divided.events[i].byte_start).to_equal(baseline.events[i].byte_start)
        expect(divided.events[i].byte_end).to_equal(baseline.events[i].byte_end)
        i = i + 1
    split = split + 1
```

</details>

#### resubmits a primitive closer after moving its event

- resubmits a primitive closer after moving its event
   - Expected: decoder.push(payload, 0, 3, true, budget, checkpoint).unwrap().consumed_bytes equals `1`
   - Expected: decoder.push(payload, 1, 2, true, budget, checkpoint).unwrap().consumed_bytes equals `0`
   - Expected: decoder.raw_bytes equals `pending_raw`
   - Expected: decoder.sha.total_length equals `pending_sha`
   - Expected: decoder.next_event().unwrap().unwrap().kind equals `start_array`
   - Expected: decoder.push(payload, 1, 2, true, budget, checkpoint).unwrap().consumed_bytes equals `1`
   - Expected: decoder.next_event().unwrap().unwrap().kind equals `integer`
   - Expected: decoder.push(payload, 2, 1, true, budget, checkpoint).unwrap().consumed_bytes equals `1`
   - Expected: decoder.next_event().unwrap().unwrap().kind equals `end_array`
   - Expected: decoder.finish(budget, checkpoint).unwrap().raw_bytes equals `3`
   - Expected: object_decoder.next_event().unwrap().unwrap().kind equals `key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("resubmits a primitive closer after moving its event")
var decoder = ProviderCanonicalJsonDecoderV1.configured(
    provider_json_limits_v1(), Sha256StreamV1.begin([]).unwrap()).unwrap()
var budget = json_budget()
var checkpoint = json_checkpoint()
val payload = "[1]".bytes()
expect(decoder.push(payload, 0, 3, true, budget, checkpoint).unwrap().consumed_bytes).to_equal(1)
val pending_raw = decoder.raw_bytes
val pending_sha = decoder.sha.total_length
expect(decoder.push(payload, 1, 2, true, budget, checkpoint).unwrap().consumed_bytes).to_equal(0)
expect(decoder.raw_bytes).to_equal(pending_raw)
expect(decoder.sha.total_length).to_equal(pending_sha)
expect(decoder.next_event().unwrap().unwrap().kind).to_equal("start_array")
expect(decoder.push(payload, 1, 2, true, budget, checkpoint).unwrap().consumed_bytes).to_equal(1)
expect(decoder.next_event().unwrap().unwrap().kind).to_equal("integer")
expect(decoder.push(payload, 2, 1, true, budget, checkpoint).unwrap().consumed_bytes).to_equal(1)
expect(decoder.next_event().unwrap().unwrap().kind).to_equal("end_array")
expect(decoder.finish(budget, checkpoint).unwrap().raw_bytes).to_equal(3)

# The object closer follows the same two-prefix rule even when the
# colon and primitive share the offered slice with that closer.
var object_decoder = ProviderCanonicalJsonDecoderV1.configured(
    provider_json_limits_v1(), Sha256StreamV1.begin([]).unwrap()).unwrap()
var object_budget = json_budget()
var object_checkpoint = json_checkpoint()
val object_payload = "{\"a\":1}".bytes()
expect(object_decoder.push(object_payload, 0, object_payload.len(),
    true, object_budget, object_checkpoint).unwrap().consumed_bytes).to_equal(1)
expect(object_decoder.next_event().unwrap().unwrap().kind).to_equal(
    "start_object")
expect(object_decoder.push(object_payload, 1, 6, true,
    object_budget, object_checkpoint).unwrap().consumed_bytes).to_equal(3)
expect(object_decoder.next_event().unwrap().unwrap().kind).to_equal("key")
expect(object_decoder.push(object_payload, 4, 3, true,
    object_budget, object_checkpoint).unwrap().consumed_bytes).to_equal(2)
expect(object_decoder.next_event().unwrap().unwrap().kind).to_equal(
    "integer")
expect(object_decoder.push(object_payload, 6, 1, true,
    object_budget, object_checkpoint).unwrap().consumed_bytes).to_equal(1)
expect(object_decoder.next_event().unwrap().unwrap().kind).to_equal(
    "end_object")
expect(object_decoder.finish(object_budget,
    object_checkpoint).unwrap().raw_bytes).to_equal(7)
```

</details>

#### rejects noncanonical escapes keys commas numbers suffixes and NFC

- rejects noncanonical escapes keys commas numbers suffixes and NFC
   - Expected: control_text.bytes().len() equals `35`
   - Expected: invalid_split.raw_bytes equals `1`
   - Expected: invalid_split.sha.total_length equals `1`
   - Expected: invalid_split.raw_bytes equals `1`
   - Expected: invalid_split.sha.total_length equals `1`
   - Expected: valid_split.raw_bytes equals `1`
   - Expected: valid_split.raw_bytes equals `3`
   - Expected: valid_split.sha.total_length equals `3`
   - Expected: valid_split.next_event().unwrap().unwrap().text_value equals `¢`
   - Expected: valid_split.finish(valid_budget, valid_checkpoint).unwrap().raw_bytes equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects noncanonical escapes keys commas numbers suffixes and NFC")
val controls = "\"\\\"\\\\\\b\\t\\n\\f\\r\\u0000\\u0001\\u0002\\u0003\\u0004\\u0005\\u0006\\u0007\\u000b\\u000e\\u000f\\u0010\\u0011\\u0012\\u0013\\u0014\\u0015\\u0016\\u0017\\u0018\\u0019\\u001a\\u001b\\u001c\\u001d\\u001e\\u001f/\""
val control = decode_json(controls.bytes(), [1, 2, 3, 4]).unwrap()
val control_text = control.events[0].text_value.unwrap()
expect(control_text.bytes().len()).to_equal(35)
expect(decode_json("{\"z\":1,\"¢\":2,\"€\":3}".bytes(),
    [1, 2, 4]).is_ok()).to_equal(true)
expect_json_error("{\"¢\":1,\"z\":2}")
expect_json_error("{\"é\":1,\"é\":2}")
var invalid_split = ProviderCanonicalJsonDecoderV1.configured(
    provider_json_limits_v1(), Sha256StreamV1.begin([]).unwrap()).unwrap()
var invalid_budget = json_budget()
var invalid_checkpoint = json_checkpoint()
expect(invalid_split.push([34u8, 194u8], 0, 2, false,
    invalid_budget, invalid_checkpoint).unwrap().consumed_bytes).to_equal(1)
expect(invalid_split.raw_bytes).to_equal(1)
expect(invalid_split.sha.total_length).to_equal(1)
expect(invalid_budget.consumed(
    provider_budget_category_raw_bytes())).to_equal(1)
expect(invalid_split.push([194u8, 32u8], 0, 2, true,
    invalid_budget, invalid_checkpoint)).to_equal(Err("invalid_utf8"))
expect(invalid_split.raw_bytes).to_equal(1)
expect(invalid_split.sha.total_length).to_equal(1)
expect(invalid_budget.consumed(
    provider_budget_category_raw_bytes())).to_equal(1)
expect(invalid_split.finish(invalid_budget, invalid_checkpoint)).to_equal(
    Err("invalid_utf8"))

var valid_split = ProviderCanonicalJsonDecoderV1.configured(
    provider_json_limits_v1(), Sha256StreamV1.begin([]).unwrap()).unwrap()
var valid_budget = json_budget()
var valid_checkpoint = json_checkpoint()
expect(valid_split.push([34u8, 194u8], 0, 2, false,
    valid_budget, valid_checkpoint).unwrap().consumed_bytes).to_equal(1)
expect(valid_split.raw_bytes).to_equal(1)
expect(valid_split.push([194u8, 162u8], 0, 2, false,
    valid_budget, valid_checkpoint).unwrap().consumed_bytes).to_equal(2)
expect(valid_split.raw_bytes).to_equal(3)
expect(valid_split.sha.total_length).to_equal(3)
expect(valid_split.push([34u8], 0, 1, true,
    valid_budget, valid_checkpoint).unwrap().consumed_bytes).to_equal(1)
expect(valid_split.next_event().unwrap().unwrap().text_value).to_equal("¢")
expect(valid_split.finish(valid_budget, valid_checkpoint).unwrap().raw_bytes).to_equal(4)
for bad in ["\"\\u000A\"", "\"\\u00AF\"", "\"\\u0020\"", "\"\\/\"",
            "{ \"a\":1}", "{\"b\":1,\"a\":2}", "{\"a\":1,\"a\":2}",
            "{\"\":1,\"\":2}", "{\"a\":1,}", "[1,]", "01", "-0", "1.0",
            "9007199254740992", "-9007199254740992", "truefalse", "[]x", "\"é\""]:
    expect_json_error(bad)
```

</details>

#### accepts all root kinds and signed safe-integer boundaries

- accepts all root kinds and signed safe-integer boundaries
   - Expected: decode_json("{}".bytes(), [1]).unwrap().events[0].kind equals `start_object`
   - Expected: decode_json("[]".bytes(), [1]).unwrap().events[0].kind equals `start_array`
   - Expected: decode_json("9007199254740991".bytes(), [1]).unwrap().events[0].integer_value equals `9007199254740991`
   - Expected: decode_json("-9007199254740991".bytes(), [2]).unwrap().events[0].integer_value equals `-9007199254740991`
   - Expected: decode_json("\"root\"".bytes(), [1]).unwrap().events[0].kind equals `string`
   - Expected: decode_json("false".bytes(), [1]).unwrap().events[0].boolean_value is false
   - Expected: decode_json("null".bytes(), [1]).unwrap().events[0].kind equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts all root kinds and signed safe-integer boundaries")
expect(decode_json("{}".bytes(), [1]).unwrap().events[0].kind).to_equal("start_object")
expect(decode_json("[]".bytes(), [1]).unwrap().events[0].kind).to_equal("start_array")
expect(decode_json("9007199254740991".bytes(), [1]).unwrap().events[0].integer_value).to_equal(9007199254740991)
expect(decode_json("-9007199254740991".bytes(), [2]).unwrap().events[0].integer_value).to_equal(-9007199254740991)
expect(decode_json("\"root\"".bytes(), [1]).unwrap().events[0].kind).to_equal("string")
expect(decode_json("false".bytes(), [1]).unwrap().events[0].boolean_value).to_equal(false)
expect(decode_json("null".bytes(), [1]).unwrap().events[0].kind).to_equal("null")
```

</details>

#### enforces under at and over depth token member and decoded limits

- enforces under at and over depth token member and decoded limits
   - Expected: decode_json(depth16.bytes(), [1]).unwrap().result.maximum_depth equals `16`
   - Expected: decode_json("[]".bytes(), [1], limits(2, 8, 8)).is_ok() is true
   - Expected: decode_json("[[]]".bytes(), [1], limits(2, 8, 8)).is_ok() is true
   - Expected: decode_json("[]".bytes(), [1], limits(16, 3, 8)).is_ok() is true
   - Expected: decode_json("[]".bytes(), [1], limits(16, 2, 8)).is_ok() is true
   - Expected: decode_json("[]".bytes(), [1], limits(16, 8, 2)).is_ok() is true
   - Expected: decode_json("[1]".bytes(), [1], limits(16, 8, 1)).is_ok() is true
   - Expected: decode_json("\"a\"".bytes(), [1], limits(16, 8, 8, 2, 2)).is_ok() is true
   - Expected: decode_json("\"ab\"".bytes(), [1], limits(16, 8, 8, 2, 2)).is_ok() is true
   - Expected: depth_decoder.maximum_depth equals `16`
   - Expected: depth_decoder.stack.len() equals `16`
   - Expected: depth_decoder.raw_bytes equals `16`
   - Expected: depth_decoder.maximum_depth equals `16`
   - Expected: depth_decoder.stack.len() equals `16`
   - Expected: depth_decoder.raw_bytes equals `16`
   - Expected: token_decoder.token_count equals `262144`
   - Expected: token_decoder.token_count equals `262144`
   - Expected: token_decoder.stack.len() equals `1`
   - Expected: token_decoder.raw_bytes equals `1`
   - Expected: member_decoder.aggregate_members equals `65536`
   - Expected: member_decoder.next_event().unwrap().unwrap().integer_value equals `0`
   - Expected: member_decoder.aggregate_members equals `65536`
   - Expected: member_decoder.stack.len() equals `1`
   - Expected: member_decoder.raw_bytes equals `member_raw`
   - Expected: member_decoder.sha.total_length equals `member_sha`


<details>
<summary>Executable SSpec</summary>

Runnable source: 86 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("enforces under at and over depth token member and decoded limits")
val depth16 = "[" * 16 + "]" * 16
val depth17 = "[" * 17 + "]" * 17
expect(decode_json(depth16.bytes(), [1]).unwrap().result.maximum_depth).to_equal(16)
expect_json_error(depth17, "limit_exceeded")
expect(decode_json("[]".bytes(), [1], limits(2, 8, 8)).is_ok()).to_equal(true)
expect(decode_json("[[]]".bytes(), [1], limits(2, 8, 8)).is_ok()).to_equal(true)
expect_json_error("[[[]]]", "limit_exceeded", limits(2, 8, 8))
expect(decode_json("[]".bytes(), [1], limits(16, 3, 8)).is_ok()).to_equal(true)
expect(decode_json("[]".bytes(), [1], limits(16, 2, 8)).is_ok()).to_equal(true)
expect_json_error("[1]", "limit_exceeded", limits(16, 2, 8))
expect(decode_json("[]".bytes(), [1], limits(16, 8, 2)).is_ok()).to_equal(true)
expect(decode_json("[1]".bytes(), [1], limits(16, 8, 1)).is_ok()).to_equal(true)
expect_json_error("[1,2]", "limit_exceeded", limits(16, 8, 1))
expect(decode_json("\"a\"".bytes(), [1], limits(16, 8, 8, 2, 2)).is_ok()).to_equal(true)
expect(decode_json("\"ab\"".bytes(), [1], limits(16, 8, 8, 2, 2)).is_ok()).to_equal(true)
expect_json_error("\"abc\"", "limit_exceeded", limits(16, 8, 8, 2, 2))

# Protocol-limit guards use the real frozen maxima. Directly seeding
# the immediately preceding counter keeps this unit bounded while the
# production transition performs the exact at/plus-one decision.
var depth_decoder = ProviderCanonicalJsonDecoderV1.configured(
    provider_json_limits_v1(), Sha256StreamV1.begin([]).unwrap()).unwrap()
var depth_budget = json_budget()
var depth_checkpoint = json_checkpoint()
var depth = 0
while depth < 16:
    expect(depth_decoder.push([91u8], 0, 1, false,
        depth_budget, depth_checkpoint).unwrap().consumed_bytes).to_equal(1)
    expect(depth_decoder.next_event().unwrap().unwrap().kind).to_equal(
        "start_array")
    depth = depth + 1
expect(depth_decoder.maximum_depth).to_equal(16)
expect(depth_decoder.stack.len()).to_equal(16)
expect(depth_decoder.raw_bytes).to_equal(16)
expect(depth_decoder.push([91u8], 0, 1, false,
    depth_budget, depth_checkpoint)).to_equal(Err("limit_exceeded"))
expect(depth_decoder.maximum_depth).to_equal(16)
expect(depth_decoder.stack.len()).to_equal(16)
expect(depth_decoder.raw_bytes).to_equal(16)
expect(depth_decoder.pending_event).to_be_nil()

var token_decoder = ProviderCanonicalJsonDecoderV1.configured(
    provider_json_limits_v1(), Sha256StreamV1.begin([]).unwrap()).unwrap()
var token_budget = json_budget()
token_decoder.token_count = 262143
expect(token_decoder.push([123u8], 0, 1, false,
    token_budget, depth_checkpoint).unwrap().consumed_bytes).to_equal(1)
expect(token_decoder.token_count).to_equal(262144)
expect(token_decoder.next_event().unwrap().unwrap().kind).to_equal(
    "start_object")
expect(token_decoder.push([125u8], 0, 1, true,
    token_budget, depth_checkpoint)).to_equal(Err("limit_exceeded"))
expect(token_decoder.token_count).to_equal(262144)
expect(token_decoder.stack.len()).to_equal(1)
expect(token_decoder.raw_bytes).to_equal(1)
expect(token_decoder.pending_event).to_be_nil()

var member_decoder = ProviderCanonicalJsonDecoderV1.configured(
    provider_json_limits_v1(), Sha256StreamV1.begin([]).unwrap()).unwrap()
var member_budget = json_budget()
expect(member_decoder.push([91u8], 0, 1, false,
    member_budget, depth_checkpoint).unwrap().consumed_bytes).to_equal(1)
expect(member_decoder.next_event().unwrap().unwrap().kind).to_equal(
    "start_array")
member_decoder.aggregate_members = 65535
expect(member_decoder.push([48u8], 0, 1, false,
    member_budget, depth_checkpoint).unwrap().consumed_bytes).to_equal(1)
expect(member_decoder.push([44u8], 0, 1, false,
    member_budget, depth_checkpoint).unwrap().consumed_bytes).to_equal(0)
expect(member_decoder.aggregate_members).to_equal(65536)
expect(member_decoder.next_event().unwrap().unwrap().integer_value).to_equal(0)
expect(member_decoder.push([44u8], 0, 1, false,
    member_budget, depth_checkpoint).unwrap().consumed_bytes).to_equal(1)
expect(member_decoder.push([49u8], 0, 1, false,
    member_budget, depth_checkpoint).unwrap().consumed_bytes).to_equal(1)
val member_raw = member_decoder.raw_bytes
val member_sha = member_decoder.sha.total_length
expect(member_decoder.push([93u8], 0, 1, true,
    member_budget, depth_checkpoint)).to_equal(Err("limit_exceeded"))
expect(member_decoder.aggregate_members).to_equal(65536)
expect(member_decoder.stack.len()).to_equal(1)
expect(member_decoder.raw_bytes).to_equal(member_raw)
expect(member_decoder.sha.total_length).to_equal(member_sha)
expect(member_decoder.pending_event).to_be_nil()
```

</details>

#### latches incomplete budget and checkpoint failures without a digest

- latches incomplete budget and checkpoint failures without a digest
   - Expected: incomplete.push([123u8], 0, 1, false, budget, checkpoint).is_ok() is true
   - Expected: incomplete.next_event().unwrap().unwrap().kind equals `start_object`
   - Expected: incomplete.finish(budget, checkpoint) equals `Err("incomplete_json")`
   - Expected: incomplete.finish(budget, checkpoint) equals `Err("incomplete_json")`
   - Expected: incomplete.next_event() equals `Err("incomplete_json")`
   - Expected: denied.push([123u8], 0, 1, false, denied_budget, checkpoint) equals `Err("limit_exceeded")`
   - Expected: denied.finish(denied_budget, checkpoint) equals `Err("limit_exceeded")`
   - Expected: event_denied.raw_bytes equals `0`
   - Expected: event_denied.sha.total_length equals `0`
   - Expected: event_denied.stack.len() equals `0`
   - Expected: stopped.push([123u8], 0, 1, false, stopped_budget, stopped_checkpoint) equals `Err("deadline_exceeded")`
   - Expected: stopped.finish(stopped_budget, stopped_checkpoint) equals `Err("deadline_exceeded")`
   - Expected: block_denied.raw_bytes equals `63`
   - Expected: block_denied.sha.total_length equals `63`
   - Expected: block_denied.string_value equals `block_string`
   - Expected: block_denied.stack.len() equals `0`
   - Expected: block_denied.root_kind equals ``
   - Expected: block_denied.token_count equals `0`
   - Expected: block_denied.aggregate_members equals `0`
   - Expected: checkpoint_denied.raw_bytes equals `63`
   - Expected: checkpoint_denied.sha.total_length equals `63`
   - Expected: checkpoint_denied.string_value equals `checkpoint_string`
   - Expected: checkpoint_denied.stack.len() equals `0`
   - Expected: checkpoint_denied.root_kind equals ``
   - Expected: checkpoint_denied.token_count equals `0`
   - Expected: checkpoint_denied.aggregate_members equals `0`
   - Expected: finalize_denied.raw_bytes equals `2`
   - Expected: finalize_denied.sha.total_length equals `2`
   - Expected: finalize_denied.next_event() equals `Err("limit_exceeded")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 118 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("latches incomplete budget and checkpoint failures without a digest")
var incomplete = ProviderCanonicalJsonDecoderV1.configured(provider_json_limits_v1(), Sha256StreamV1.begin([]).unwrap()).unwrap()
var budget = json_budget()
var checkpoint = json_checkpoint()
expect(incomplete.push([123u8], 0, 1, false, budget, checkpoint).is_ok()).to_equal(true)
expect(incomplete.next_event().unwrap().unwrap().kind).to_equal("start_object")
expect(incomplete.finish(budget, checkpoint)).to_equal(Err("incomplete_json"))
expect(incomplete.finish(budget, checkpoint)).to_equal(Err("incomplete_json"))
expect(incomplete.next_event()).to_equal(Err("incomplete_json"))
var denied = ProviderCanonicalJsonDecoderV1.configured(provider_json_limits_v1(), Sha256StreamV1.begin([]).unwrap()).unwrap()
var denied_budget = json_budget(0)
expect(denied.push([123u8], 0, 1, false, denied_budget, checkpoint)).to_equal(Err("limit_exceeded"))
expect(denied.finish(denied_budget, checkpoint)).to_equal(Err("limit_exceeded"))

# The event category is deliberately the later failing category in
# the one external batch. Neither token/event nor raw/SHA/parser state
# may commit when that second event reservation is rejected.
var event_denied = ProviderCanonicalJsonDecoderV1.configured(
    provider_json_limits_v1(), Sha256StreamV1.begin([]).unwrap()).unwrap()
var event_budget = json_budget_with_event_limit(1, 0)
expect(event_denied.push([123u8], 0, 1, false,
    event_budget, checkpoint)).to_equal(Err("limit_exceeded"))
expect(event_budget.consumed(
    provider_budget_category_tokens())).to_equal(0)
expect(event_budget.consumed(
    provider_budget_category_json_events())).to_equal(0)
expect(event_budget.consumed(
    provider_budget_category_raw_bytes())).to_equal(0)
expect(event_denied.raw_bytes).to_equal(0)
expect(event_denied.sha.total_length).to_equal(0)
expect(event_denied.stack.len()).to_equal(0)
expect(event_denied.pending_event).to_be_nil()
expect(event_denied.finish(event_budget, checkpoint)).to_equal(
    Err("limit_exceeded"))

expect_invalid_range_latched([123u8], -1, 1)
expect_invalid_range_latched([123u8], 0, -1)
expect_invalid_range_latched([123u8], 2, 0)
expect_invalid_range_latched([123u8], 0, 2)
expect_invalid_range_latched([0u8; 4097], 0, 4097)
var stopped = ProviderCanonicalJsonDecoderV1.configured(provider_json_limits_v1(), Sha256StreamV1.begin([]).unwrap()).unwrap()
var stopped_budget = json_budget()
var stopped_checkpoint = json_checkpoint(0, "deadline_exceeded")
expect(stopped.push([123u8], 0, 1, false, stopped_budget, stopped_checkpoint)).to_equal(Err("deadline_exceeded"))
expect(stopped.finish(stopped_budget, stopped_checkpoint)).to_equal(Err("deadline_exceeded"))

# The 64th byte completes the first SHA block. A denied block charge
# must discard the child transition without publishing parser or hash
# state to the decoder owner.
val prefix_text = "\"" + "a" * 62
val prefix = prefix_text.bytes()
var block_denied = ProviderCanonicalJsonDecoderV1.configured(
    provider_json_limits_v1(), Sha256StreamV1.begin([]).unwrap()).unwrap()
var block_budget = json_budget_with_hash_limit(2000000, 0)
var block_checkpoint = json_checkpoint()
expect(block_denied.push(prefix, 0, prefix.len(), false,
    block_budget, block_checkpoint).unwrap().consumed_bytes).to_equal(63)
val block_string = block_denied.string_value
expect(block_denied.push([98u8], 0, 1, false,
    block_budget, block_checkpoint)).to_equal(Err("limit_exceeded"))
expect(block_denied.raw_bytes).to_equal(63)
expect(block_denied.sha.total_length).to_equal(63)
expect(block_denied.string_value).to_equal(block_string)
expect(block_denied.stack.len()).to_equal(0)
expect(block_denied.root_kind).to_equal("")
expect(block_denied.pending_event).to_be_nil()
expect(block_denied.token_count).to_equal(0)
expect(block_denied.aggregate_members).to_equal(0)
expect(block_denied.finish(block_budget, block_checkpoint)).to_equal(
    Err("limit_exceeded"))

# The same ownership rule applies when the external checkpoint rejects
# the otherwise valid block-boundary transition.
var checkpoint_denied = ProviderCanonicalJsonDecoderV1.configured(
    provider_json_limits_v1(), Sha256StreamV1.begin([]).unwrap()).unwrap()
var checkpoint_budget = json_budget()
var boundary_checkpoint = json_checkpoint(63, "deadline_exceeded")
expect(checkpoint_denied.push(prefix, 0, prefix.len(), false,
    checkpoint_budget, boundary_checkpoint).unwrap().consumed_bytes).to_equal(63)
val checkpoint_string = checkpoint_denied.string_value
expect(checkpoint_denied.push([98u8], 0, 1, false,
    checkpoint_budget, boundary_checkpoint)).to_equal(
    Err("deadline_exceeded"))
expect(checkpoint_denied.raw_bytes).to_equal(63)
expect(checkpoint_denied.sha.total_length).to_equal(63)
expect(checkpoint_denied.string_value).to_equal(checkpoint_string)
expect(checkpoint_denied.stack.len()).to_equal(0)
expect(checkpoint_denied.root_kind).to_equal("")
expect(checkpoint_denied.pending_event).to_be_nil()
expect(checkpoint_denied.token_count).to_equal(0)
expect(checkpoint_denied.aggregate_members).to_equal(0)
expect(checkpoint_denied.finish(checkpoint_budget,
    boundary_checkpoint)).to_equal(Err("deadline_exceeded"))

# SHA tail/finalization is still downstream of complete JSON. A
# denied final block publishes neither digest nor a retry surface.
var finalize_denied = ProviderCanonicalJsonDecoderV1.configured(
    provider_json_limits_v1(), Sha256StreamV1.begin([]).unwrap()).unwrap()
var finalize_budget = json_budget_with_hash_limit(2000000, 0)
var finalize_checkpoint = json_checkpoint()
expect(finalize_denied.push([123u8], 0, 1, false,
    finalize_budget, finalize_checkpoint).unwrap().consumed_bytes).to_equal(1)
expect(finalize_denied.next_event().unwrap().unwrap().kind).to_equal(
    "start_object")
expect(finalize_denied.push([125u8], 0, 1, true,
    finalize_budget, finalize_checkpoint).unwrap().consumed_bytes).to_equal(1)
expect(finalize_denied.next_event().unwrap().unwrap().kind).to_equal(
    "end_object")
expect(finalize_denied.finish(finalize_budget,
    finalize_checkpoint)).to_equal(Err("limit_exceeded"))
expect(finalize_denied.raw_bytes).to_equal(2)
expect(finalize_denied.sha.total_length).to_equal(2)
expect(finalize_denied.push([123u8], 0, 1, false,
    finalize_budget, finalize_checkpoint)).to_equal(Err("limit_exceeded"))
expect(finalize_denied.next_event()).to_equal(Err("limit_exceeded"))
expect(finalize_denied.finish(finalize_budget,
    finalize_checkpoint)).to_equal(Err("limit_exceeded"))
```

</details>

#### blocks pending finish then latches successful finish

- blocks pending finish then latches successful finish
   - Expected: decoder.push("null".bytes(), 0, 4, true, budget, checkpoint).is_ok() is true
   - Expected: pending.kind equals `event`
   - Expected: pending.consumed_bytes equals `0`
   - Expected: decoder.raw_bytes equals `pending_raw`
   - Expected: decoder.sha.total_length equals `pending_sha`
   - Expected: decoder.finish(budget, checkpoint) equals `Err("event_pending")`
   - Expected: decoder.next_event().unwrap().unwrap().kind equals `null`
   - Expected: decoder.finish(budget, checkpoint).is_ok() is true
   - Expected: decoder.finish(budget, checkpoint) equals `Err("decoder_complete")`
   - Expected: decoder.next_event() equals `Err("decoder_complete")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("blocks pending finish then latches successful finish")
var decoder = ProviderCanonicalJsonDecoderV1.configured(provider_json_limits_v1(), Sha256StreamV1.begin([]).unwrap()).unwrap()
var budget = json_budget()
var checkpoint = json_checkpoint()
expect(decoder.push("null".bytes(), 0, 4, true, budget, checkpoint).is_ok()).to_equal(true)
val pending_raw = decoder.raw_bytes
val pending_sha = decoder.sha.total_length
val pending = decoder.push([120u8], 0, 1, false,
    budget, checkpoint).unwrap()
expect(pending.kind).to_equal("event")
expect(pending.consumed_bytes).to_equal(0)
expect(decoder.raw_bytes).to_equal(pending_raw)
expect(decoder.sha.total_length).to_equal(pending_sha)
expect(decoder.finish(budget, checkpoint)).to_equal(Err("event_pending"))
expect(decoder.next_event().unwrap().unwrap().kind).to_equal("null")
expect(decoder.finish(budget, checkpoint).is_ok()).to_equal(true)
expect(decoder.push([123u8], 0, 1, false,
    budget, checkpoint)).to_equal(Err("decoder_complete"))
expect(decoder.finish(budget, checkpoint)).to_equal(Err("decoder_complete"))
expect(decoder.next_event()).to_equal(Err("decoder_complete"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spipe_knowledge_provider/provider_canonical_json_decoder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SPipe iterative canonical JSON decoder.
- SPipe iterative canonical JSON decoder

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-JSON`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b889a33e927793f3a5d537936497fc37b59c82463fa6a6897966eed200ede604`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b889a33e927793f3a5d537936497fc37b59c82463fa6a6897966eed200ede604`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b889a33e927793f3a5d537936497fc37b59c82463fa6a6897966eed200ede604`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/01_unit/app/spipe_knowledge_provider/provider_canonical_json_decoder_spec.spl
mirror: doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_canonical_json_decoder_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_canonical_json_decoder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_canonical_json_decoder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/spipe_knowledge_provider/provider_canonical_json_decoder_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 47 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/spipe_knowledge_provider/provider_canonical_json_decoder_spec.spl:128:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'emits closed events with exact nullable fields spans and counters' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/spipe_knowledge_provider/provider_canonical_json_decoder_spec.spl:167:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is invariant at every split and hashes exact raw bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spipe_knowledge_provider/provider_canonical_json_decoder_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resubmits a primitive closer after moving its event' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spipe_knowledge_provider/provider_canonical_json_decoder_spec.spl:236:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects noncanonical escapes keys commas numbers suffixes and NFC' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
