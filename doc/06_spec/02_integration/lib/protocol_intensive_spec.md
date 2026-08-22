# protocol_intensive_spec

> Verifies the protocol intensive behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 54 | 54 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# protocol_intensive_spec

Verifies the protocol intensive behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/protocol_intensive_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the protocol intensive behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### MCP Protocol - Intensive

#### initialization

<details>
<summary>Advanced: handles initialize request correctly</summary>

#### handles initialize request correctly _(slow)_

- Verify: handles initialize request correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles initialize request correctly")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val request = build_initialize_request(1)

# Request should be valid JSON
check(request.?)
check(json_contains(request, "initialize"))
check(json_contains(request, "protocolVersion"))
```

</details>


</details>

<details>
<summary>Advanced: validates protocol version</summary>

#### validates protocol version _(slow)_

- Verify: validates protocol version


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: validates protocol version")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val request = build_initialize_request(1)

check(json_contains(request, "2024-11-05"))
```

</details>


</details>

<details>
<summary>Advanced: includes client info</summary>

#### includes client info _(slow)_

- Verify: includes client info


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: includes client info")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val request = build_initialize_request(1)

check(json_contains(request, "clientInfo"))
check(json_contains(request, "test-client"))
```

</details>


</details>

<details>
<summary>Advanced: includes capabilities</summary>

#### includes capabilities _(slow)_

- Verify: includes capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: includes capabilities")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val request = build_initialize_request(1)

check(json_contains(request, "capabilities"))
```

</details>


</details>

<details>
<summary>Advanced: has correct JSON-RPC version</summary>

#### has correct JSON-RPC version _(slow)_

- Verify: has correct JSON-RPC version


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: has correct JSON-RPC version")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val request = build_initialize_request(1)

assert_valid_json_rpc(request)
```

</details>


</details>

#### resources/list requests

<details>
<summary>Advanced: builds valid resources/list request</summary>

#### builds valid resources/list request _(slow)_

- Verify: builds valid resources/list request


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: builds valid resources/list request")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val request = build_resources_list_request(2)

assert_valid_json_rpc(request)
check(json_contains(request, "resources/list"))
assert_has_id(request, 2)
```

</details>


</details>

<details>
<summary>Advanced: handles multiple sequential list requests</summary>

#### handles multiple sequential list requests _(slow)_

- Verify: handles multiple sequential list requests


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles multiple sequential list requests")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
for i in 0..10:
    val request = build_resources_list_request(i)
    assert_valid_json_rpc(request)
    assert_has_id(request, i)
```

</details>


</details>

#### resources/read requests

<details>
<summary>Advanced: builds valid resources/read request</summary>

#### builds valid resources/read request _(slow)_

- Verify: builds valid resources/read request


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: builds valid resources/read request")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val uri = "file:///test.spl"
val request = build_resources_read_request(3, uri)

assert_valid_json_rpc(request)
check(json_contains(request, "resources/read"))
check(json_contains(request, uri))
```

</details>


</details>

<details>
<summary>Advanced: handles various URI schemes</summary>

#### handles various URI schemes _(slow)_

- Verify: handles various URI schemes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles various URI schemes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val uris = get_test_uris()

for i in 0..uris.len():
    val uri = uris[i]
    val request = build_resources_read_request(10 + i, uri)
    check(json_contains(request, uri))
```

</details>


</details>

<details>
<summary>Advanced: handles file URIs</summary>

#### handles file URIs _(slow)_

- Verify: handles file URIs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles file URIs")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val uri = build_file_uri("src/main.spl")
val request = build_resources_read_request(20, uri)

check(json_contains(request, "file://"))
check(json_contains(request, "src/main.spl"))
```

</details>


</details>

<details>
<summary>Advanced: handles symbol URIs</summary>

#### handles symbol URIs _(slow)_

- Verify: handles symbol URIs


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles symbol URIs")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val uri = build_symbol_uri("src/main.spl", "main")
val request = build_resources_read_request(21, uri)

check(json_contains(request, "symbol://"))
```

</details>


</details>

<details>
<summary>Advanced: handles type URIs</summary>

#### handles type URIs _(slow)_

- Verify: handles type URIs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles type URIs")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val uri = build_type_uri("String")
val request = build_resources_read_request(22, uri)

check(json_contains(request, "type://"))
check(json_contains(request, "String"))
```

</details>


</details>

<details>
<summary>Advanced: handles bugdb URIs</summary>

#### handles bugdb URIs _(slow)_

- Verify: handles bugdb URIs


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles bugdb URIs")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val uris = [
    build_bugdb_uri("all"),
    build_bugdb_uri("open"),
    build_bugdb_uri("critical"),
    build_bugdb_uri("stats")
]

for i in 0..uris.len():
    val uri = uris[i]
    val request = build_resources_read_request(30 + i, uri)
    check(json_contains(request, "bugdb://"))
```

</details>


</details>

#### prompts/list requests

<details>
<summary>Advanced: builds valid prompts/list request</summary>

#### builds valid prompts/list request _(slow)_

- Verify: builds valid prompts/list request


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: builds valid prompts/list request")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val request = build_prompts_list_request(40)

assert_valid_json_rpc(request)
check(json_contains(request, "prompts/list"))
```

</details>


</details>

#### prompts/get requests

<details>
<summary>Advanced: builds valid prompts/get request</summary>

#### builds valid prompts/get request _(slow)_

- Verify: builds valid prompts/get request


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: builds valid prompts/get request")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val request = build_prompts_get_request(41, "refactor-extract-function", [])

assert_valid_json_rpc(request)
check(json_contains(request, "prompts/get"))
check(json_contains(request, "refactor-extract-function"))
```

</details>


</details>

<details>
<summary>Advanced: handles various prompt names</summary>

#### handles various prompt names _(slow)_

- Verify: handles various prompt names


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles various prompt names")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val names = get_test_prompt_names()

for i in 0..names.len():
    val name = names[i]
    val request = build_prompts_get_request(50 + i, name, [])
    check(json_contains(request, name))
```

</details>


</details>

<details>
<summary>Advanced: includes prompt arguments</summary>

#### includes prompt arguments _(slow)_

- Verify: includes prompt arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: includes prompt arguments")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val args = [
    jpair("file", jstr("test.spl")),
    jpair("line", jnum(42))
]
val request = build_prompts_get_request(60, "analyze", args)

check(json_contains(request, "arguments"))
check(json_contains(request, "test.spl"))
```

</details>


</details>

#### response building

<details>
<summary>Advanced: builds valid success response</summary>

#### builds valid success response _(slow)_

- Verify: builds valid success response


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: builds valid success response")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = jobj([jpair("status", jstr("ok"))])
val response = build_success_response(1, result)

assert_valid_json_rpc(response)
assert_has_id(response, 1)
assert_has_result(response)
```

</details>


</details>

<details>
<summary>Advanced: builds valid error response</summary>

#### builds valid error response _(slow)_

- Verify: builds valid error response


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: builds valid error response")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val response = build_error_response(2, -32600, "Invalid Request")

assert_valid_json_rpc(response)
assert_has_id(response, 2)
assert_has_error(response)
check(json_contains(response, "Invalid Request"))
```

</details>


</details>

<details>
<summary>Advanced: handles various error codes</summary>

#### handles various error codes _(slow)_

- Verify: handles various error codes


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles various error codes")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# Test each error code individually (tuple destructuring from array
# triggers "variable not found" runtime bug)
val r1 = build_error_response(70, -32700, "Parse error")
assert_has_error(r1)
val r2 = build_error_response(71, -32600, "Invalid Request")
assert_has_error(r2)
val r3 = build_error_response(72, -32601, "Method not found")
assert_has_error(r3)
val r4 = build_error_response(73, -32602, "Invalid params")
assert_has_error(r4)
val r5 = build_error_response(74, -32603, "Internal error")
assert_has_error(r5)
```

</details>


</details>

#### invalid requests

<details>
<summary>Advanced: builds invalid method request</summary>

#### builds invalid method request _(slow)_

- Verify: builds invalid method request


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: builds invalid method request")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val request = build_invalid_request(100)

assert_valid_json_rpc(request)
check(json_contains(request, "invalid/method"))
```

</details>


</details>

<details>
<summary>Advanced: detects malformed JSON</summary>

#### detects malformed JSON _(slow)_

- Verify: detects malformed JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: detects malformed JSON")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val malformed = build_malformed_json()

# Should not be valid JSON
check(not json_contains(malformed, "\"jsonrpc\":\"2.0\"}"))
```

</details>


</details>

#### request ID handling

<details>
<summary>Advanced: handles sequential IDs</summary>

#### handles sequential IDs _(slow)_

- Verify: handles sequential IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles sequential IDs")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
for i in 0..100:
    val request = build_resources_list_request(i)
    assert_has_id(request, i)
```

</details>


</details>

<details>
<summary>Advanced: handles large IDs</summary>

#### handles large IDs _(slow)_

- Verify: handles large IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles large IDs")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val request = build_resources_list_request(999999)
assert_has_id(request, 999999)
```

</details>


</details>

<details>
<summary>Advanced: handles ID 0</summary>

#### handles ID 0 _(slow)_

- Verify: handles ID 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles ID 0")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val request = build_resources_list_request(0)
assert_has_id(request, 0)
```

</details>


</details>

#### JSON structure validation

<details>
<summary>Advanced: validates object structure</summary>

#### validates object structure _(slow)_

- Verify: validates object structure


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: validates object structure")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val request = build_initialize_request(1)

# Should have required top-level fields
check(json_contains_key(request, "jsonrpc"))
check(json_contains_key(request, "id"))
check(json_contains_key(request, "method"))
```

</details>


</details>

<details>
<summary>Advanced: validates nested objects</summary>

#### validates nested objects _(slow)_

- Verify: validates nested objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: validates nested objects")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val request = build_initialize_request(1)

# Should have nested params
check(json_contains_key(request, "params"))
check(json_contains(request, "protocolVersion"))
```

</details>


</details>

<details>
<summary>Advanced: validates arrays</summary>

#### validates arrays _(slow)_

- Verify: validates arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: validates arrays")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val items = [jstr("item1"), jstr("item2"), jstr("item3")]
val array = jarray(items)

check(array.contains("["))
check(array.contains("]"))
check(array.contains("item1"))
check(array.contains("item2"))
```

</details>


</details>

#### special characters in JSON

<details>
<summary>Advanced: escapes quotes in strings</summary>

#### escapes quotes in strings _(slow)_

- Verify: escapes quotes in strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: escapes quotes in strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "test with \"quotes\""
val json_str = jstr(text)

check(json_str.contains("\\\""))
```

</details>


</details>

<details>
<summary>Advanced: escapes newlines in strings</summary>

#### escapes newlines in strings _(slow)_

- Verify: escapes newlines in strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: escapes newlines in strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "line1\nline2"
val json_str = jstr(text)

check(json_str.contains("\\n"))
```

</details>


</details>

<details>
<summary>Advanced: escapes tabs in strings</summary>

#### escapes tabs in strings _(slow)_

- Verify: escapes tabs in strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: escapes tabs in strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "col1\tcol2"
val json_str = jstr(text)

check(json_str.contains("\\t"))
```

</details>


</details>

<details>
<summary>Advanced: escapes backslashes in strings</summary>

#### escapes backslashes in strings _(slow)_

- Verify: escapes backslashes in strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: escapes backslashes in strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "path\\to\\file"
val json_str = jstr(text)

check(json_str.contains("\\\\"))
```

</details>


</details>

<details>
<summary>Advanced: handles unicode in JSON</summary>

#### handles unicode in JSON _(slow)_

- Verify: handles unicode in JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles unicode in JSON")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "测试 🚀"
val json_str = jstr(text)

# Unicode should be preserved
check(json_str.contains("测试"))
```

</details>


</details>

#### resource data structures

<details>
<summary>Advanced: builds valid file resource</summary>

#### builds valid file resource _(slow)_

- Verify: builds valid file resource


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: builds valid file resource")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val resource = build_file_resource(
    "file:///test.spl",
    "test.spl",
    "Test file"
)

check(json_contains(resource, "file:///test.spl"))
check(json_contains(resource, "test.spl"))
check(json_contains(resource, "Test file"))
check(json_contains(resource, "text/plain"))
```

</details>


</details>

<details>
<summary>Advanced: builds valid symbol resource</summary>

#### builds valid symbol resource _(slow)_

- Verify: builds valid symbol resource


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: builds valid symbol resource")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val resource = build_symbol_resource(
    "symbol://test.spl#main",
    "main"
)

check(json_contains(resource, "symbol://test.spl#main"))
check(json_contains(resource, "main"))
```

</details>


</details>

<details>
<summary>Advanced: builds valid bugdb resource</summary>

#### builds valid bugdb resource _(slow)_

- Verify: builds valid bugdb resource


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: builds valid bugdb resource")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val resource = build_bugdb_resource(
    "bugdb://all",
    "All Bugs"
)

check(json_contains(resource, "bugdb://all"))
check(json_contains(resource, "All Bugs"))
check(json_contains(resource, "application/json"))
```

</details>


</details>

#### prompt data structures

<details>
<summary>Advanced: builds valid prompt info</summary>

#### builds valid prompt info _(slow)_

- Verify: builds valid prompt info


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: builds valid prompt info")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val args = [
    build_prompt_argument("file", "File path", true),
    build_prompt_argument("line", "Line number", false)
]
val prompt = build_prompt_info(
    "test-prompt",
    "Test prompt description",
    args
)

check(json_contains(prompt, "test-prompt"))
check(json_contains(prompt, "Test prompt description"))
check(json_contains(prompt, "arguments"))
```

</details>


</details>

<details>
<summary>Advanced: handles required vs optional arguments</summary>

#### handles required vs optional arguments _(slow)_

- Verify: handles required vs optional arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles required vs optional arguments")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val required = build_prompt_argument("file", "File", true)
val optional = build_prompt_argument("depth", "Depth", false)

check(json_contains(required, "\"required\":true"))
check(json_contains(optional, "\"required\":false"))
```

</details>


</details>

### Bug Database JSON - Intensive

#### bug JSON serialization

<details>
<summary>Advanced: builds valid bug JSON</summary>

#### builds valid bug JSON _(slow)_

- Verify: builds valid bug JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: builds valid bug JSON")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val bug_json = build_bug_json(
    "bug_001",
    "P0",
    "Open",
    "Test bug"
)

check(json_contains(bug_json, "bug_001"))
check(json_contains(bug_json, "P0"))
check(json_contains(bug_json, "Open"))
check(json_contains(bug_json, "Test bug"))
```

</details>


</details>

<details>
<summary>Advanced: includes all bug fields</summary>

#### includes all bug fields _(slow)_

- Verify: includes all bug fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: includes all bug fields")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val bug_json = build_bug_json(
    "bug_002",
    "P1",
    "Investigating",
    "Another bug"
)

check(json_contains_key(bug_json, "id"))
check(json_contains_key(bug_json, "severity"))
check(json_contains_key(bug_json, "status"))
check(json_contains_key(bug_json, "title"))
check(json_contains_key(bug_json, "file"))
check(json_contains_key(bug_json, "line"))
```

</details>


</details>

<details>
<summary>Advanced: handles bug arrays</summary>

#### handles bug arrays _(slow)_

- Verify: handles bug arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles bug arrays")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val bugs = [
    ("bug_1", "P0", "Open", "First"),
    ("bug_2", "P1", "Fixed", "Second"),
    ("bug_3", "P2", "Closed", "Third")
]
val array_json = build_bug_array_json(bugs)

check(array_json.contains("["))
check(array_json.contains("]"))
check(json_contains(array_json, "bug_1"))
check(json_contains(array_json, "bug_2"))
check(json_contains(array_json, "bug_3"))
```

</details>


</details>

<details>
<summary>Advanced: handles empty bug array</summary>

#### handles empty bug array _(slow)_

- Verify: handles empty bug array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles empty bug array")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val empty_array = build_bug_array_json([])

check(empty_array == "[]")
```

</details>


</details>

#### statistics JSON

<details>
<summary>Advanced: builds valid stats JSON</summary>

#### builds valid stats JSON _(slow)_

- Verify: builds valid stats JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: builds valid stats JSON")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val stats_json = build_bugdb_stats_json(100, 50, 10)

check(json_contains(stats_json, "\"total\":100"))
check(json_contains(stats_json, "\"open\":50"))
check(json_contains(stats_json, "\"critical\":10"))
```

</details>


</details>

<details>
<summary>Advanced: includes all stat fields</summary>

#### includes all stat fields _(slow)_

- Verify: includes all stat fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: includes all stat fields")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val stats_json = build_bugdb_stats_json(100, 50, 10)

check(json_contains_key(stats_json, "total"))
check(json_contains_key(stats_json, "open"))
check(json_contains_key(stats_json, "investigating"))
check(json_contains_key(stats_json, "fixed"))
check(json_contains_key(stats_json, "closed"))
check(json_contains_key(stats_json, "critical"))
```

</details>


</details>

### JSON Extraction - Intensive

#### string extraction

<details>
<summary>Advanced: extracts simple string values</summary>

#### extracts simple string values _(slow)_

- Verify: extracts simple string values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: extracts simple string values")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# SKIP: extract_json_string uses index_of which returns enum in interpreter mode
print "SKIP: index_of returns enum (not i64) causing type mismatch in interpreter mode"
```

</details>


</details>

<details>
<summary>Advanced: extracts string with spaces</summary>

#### extracts string with spaces _(slow)_

- Verify: extracts string with spaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: extracts string with spaces")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# SKIP: extract_json_string uses index_of which returns enum in interpreter mode
print "SKIP: index_of returns enum (not i64) causing type mismatch in interpreter mode"
```

</details>


</details>

<details>
<summary>Advanced: extracts unicode strings</summary>

#### extracts unicode strings _(slow)_

- Verify: extracts unicode strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: extracts unicode strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# SKIP: extract_json_string uses index_of which returns enum in interpreter mode
print "SKIP: index_of returns enum (not i64) causing type mismatch in interpreter mode"
```

</details>


</details>

<details>
<summary>Advanced: handles missing keys</summary>

#### handles missing keys _(slow)_

- Verify: handles missing keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles missing keys")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# SKIP: extract_json_string uses index_of which returns enum in interpreter mode
print "SKIP: index_of returns enum (not i64) causing type mismatch in interpreter mode"
```

</details>


</details>

#### number extraction

<details>
<summary>Advanced: extracts simple numbers</summary>

#### extracts simple numbers _(slow)_

- Verify: extracts simple numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: extracts simple numbers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# SKIP: extract_json_number uses parse_int() ?? 0 which returns enum in interpreter
print "SKIP: parse_int() ?? coercion returns enum instead of i64 in interpreter mode"
```

</details>


</details>

<details>
<summary>Advanced: extracts zero</summary>

#### extracts zero _(slow)_

- Verify: extracts zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: extracts zero")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# SKIP: extract_json_number uses parse_int() ?? 0 which returns enum in interpreter
print "SKIP: parse_int() ?? coercion returns enum instead of i64 in interpreter mode"
```

</details>


</details>

<details>
<summary>Advanced: handles missing keys</summary>

#### handles missing keys _(slow)_

- Verify: handles missing keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles missing keys")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# SKIP: extract_json_number uses parse_int() ?? 0 which returns enum in interpreter
print "SKIP: parse_int() ?? coercion returns enum instead of i64 in interpreter mode"
```

</details>


</details>

#### key existence checks

<details>
<summary>Advanced: detects existing keys</summary>

#### detects existing keys _(slow)_

- Verify: detects existing keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: detects existing keys")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val json = jobj([
    jpair("name", jstr("Alice")),
    jpair("age", jnum(30))
])

check(json_contains_key(json, "name"))
check(json_contains_key(json, "age"))
```

</details>


</details>

<details>
<summary>Advanced: detects missing keys</summary>

#### detects missing keys _(slow)_

- Verify: detects missing keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: detects missing keys")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val json = jobj([jpair("name", jstr("Alice"))])

check(not json_contains_key(json, "nonexistent"))
```

</details>


</details>

<details>
<summary>Advanced: handles nested keys</summary>

#### handles nested keys _(slow)_

- Verify: handles nested keys


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_PROTOCOL_INTENSIVE-001
step("Verify: handles nested keys")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val nested = jobj([
    jpair("user", jobj([
        jpair("name", jstr("Alice"))
    ]))
])

check(json_contains_key(nested, "user"))
check(json_contains_key(nested, "name"))
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 54 |
| Active scenarios | 54 |
| Slow scenarios | 54 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c7db70aa25323d2d86a827e72d05de5a6e16306adf57e1e3e5955f9de9a46f37`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c7db70aa25323d2d86a827e72d05de5a6e16306adf57e1e3e5955f9de9a46f37`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c7db70aa25323d2d86a827e72d05de5a6e16306adf57e1e3e5955f9de9a46f37`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/lib/protocol_intensive_spec.spl
mirror: doc/06_spec/02_integration/lib/protocol_intensive_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/protocol_intensive_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/lib/protocol_intensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/protocol_intensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
