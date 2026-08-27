# Browser Session Storage Specification

> Tests covering BrowserSession storage API.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Storage Specification

## Scenarios

### BrowserSession storage API

#### updates pair lists without changing first-match order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- updates pair lists without changing first-match order
   - Expected: appended.len() equals `2`
   - Expected: appended[0].first equals `theme`
   - Expected: appended[1].first equals `mode`
   - Expected: pair_value(replaced, "theme") ?? "" equals `dark`
   - Expected: pair_value(replaced, "mode") ?? "" equals `reader`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("updates pair lists without changing first-match order")
val first = Pair(first: "theme", second: "light")
val second = Pair(first: "mode", second: "reader")
val appended = upsert_pair([first], "mode", "reader")
val replaced = upsert_pair(appended, "theme", "dark")

expect(appended.len()).to_equal(2)
expect(appended[0].first).to_equal("theme")
expect(appended[1].first).to_equal("mode")
expect(pair_value(replaced, "theme") ?? "").to_equal("dark")
expect(pair_value(replaced, "mode") ?? "").to_equal("reader")
expect(pair_value(replaced, "missing")).to_be_nil()
```

</details>

#### keeps internal names for storage API property collisions

- keeps internal names for storage API property collisions
   - Expected: is_storage_api_property("getItem") is true
   - Expected: storage_public_key_from_internal(stored_key) equals `getItem`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps internal names for storage API property collisions")
val stored_key = storage_internal_key("getItem")

expect(is_storage_api_property("getItem")).to_equal(true)
expect(storage_public_key_from_internal(stored_key)).to_equal("getItem")
```

</details>

#### keeps storage API methods callable when stored keys use method names

- keeps storage API methods callable when stored keys use method names
   - Expected: _display_js(value) equals `function:stored:manual:2`
   - Expected: session.session_storage_item("getItem") ?? "" equals `stored`
   - Expected: session.session_storage_item("length") ?? "" equals `manual`
   - Expected: _display_js(value) equals `function:true:1:length`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps storage API methods callable when stored keys use method names")
var session = BrowserSession.new()
session.open_html("about:storage-collision", "<html><body>Storage</body></html>")

val set_result = session.eval_script(
    "sessionStorage.setItem('getItem', 'stored'); sessionStorage.setItem('length', 'manual'); typeof sessionStorage.getItem + ':' + sessionStorage.getItem('getItem') + ':' + sessionStorage.getItem('length') + ':' + sessionStorage.length"
)
match set_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("function:stored:manual:2")
        expect(session.session_storage_item("getItem") ?? "").to_equal("stored")
        expect(session.session_storage_item("length") ?? "").to_equal("manual")
    Err(e) =>
        fail("Expected storage collision script to evaluate successfully: {e}")

val remove_result = session.eval_script(
    "sessionStorage.removeItem('getItem'); typeof sessionStorage.getItem + ':' + (sessionStorage.getItem('getItem') === null) + ':' + sessionStorage.length + ':' + sessionStorage.key(0)"
)
match remove_result:
    Ok(value) =>
        expect(_display_js(value)).to_equal("function:true:1:length")
        expect(session.session_storage_item("getItem")).to_be_nil()
    Err(e) =>
        fail("Expected storage removeItem script to evaluate successfully: {e}")
```

</details>

#### partitions Web Storage by origin

- partitions Web Storage by origin
   - Expected: bank.is_ok() is true
   - Expected: evil.is_ok() is true
   - Expected: session.current_body_html equals `null:null`
   - Expected: bank_again.is_ok() is true
   - Expected: session.current_body_html equals `secret:bank`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("partitions Web Storage by origin")
var session = BrowserSession.new()
val bank = session.open_html(
    "https://bank.example/app",
    "<html><body><script>localStorage.token = 'secret'; sessionStorage.tab = 'bank';</script></body></html>"
)
expect(bank.is_ok()).to_equal(true)

val evil = session.open_html(
    "https://evil.example/app",
    "<html><body><script>document.body.textContent = localStorage.getItem('token') + ':' + sessionStorage.getItem('tab');</script></body></html>"
)
expect(evil.is_ok()).to_equal(true)
expect(session.current_body_html).to_equal("null:null")

val bank_again = session.open_html(
    "https://bank.example/next",
    "<html><body><script>document.body.textContent = localStorage.getItem('token') + ':' + sessionStorage.getItem('tab');</script></body></html>"
)
expect(bank_again.is_ok()).to_equal(true)
expect(session.current_body_html).to_equal("secret:bank")
```

</details>

#### bounds Web Storage entries across method and property writes

- bounds Web Storage entries across method and property writes
   - Expected: length equals `1024.0`
   - Expected: _display_js(value) equals `updated:null:1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bounds Web Storage entries across method and property writes")
var session = BrowserSession.new()
session.open_html(
    "https://quota.example/app", "<html><body>Storage</body></html>"
)

val filled = session.eval_script(
    "for (var i = 0; i < 1030; i = i + 1) { localStorage.setItem('k' + i, 'v'); } localStorage.length"
)
match filled:
    Ok(JsValue.Number(length)):
        expect(length).to_equal(1024.0)
    _:
        fail("Expected bounded Web Storage length")

val property_write = session.eval_script(
    "localStorage.k0 = 'updated'; localStorage.extra = 'denied'; localStorage.getItem('k0') + ':' + localStorage.getItem('extra') + ':' + localStorage.length"
)
match property_write:
    Ok(value):
        expect(_display_js(value)).to_equal("updated:null:1024")
    Err(e):
        fail("Expected bounded direct storage property write: {e}")
```

</details>

#### bounds retained origin storage and drops empty buckets

- bounds retained origin storage and drops empty buckets
   - Expected: session.local_storage_by_origin.len() equals `64`
   - Expected: retained_oldest is false
   - Expected: retained_newest is true
   - Expected: session.session_storage_by_origin.len() equals `0`
   - Expected: session.local_storage_by_origin.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bounds retained origin storage and drops empty buckets")
var session = BrowserSession.new()
var index = 0
while index < 70:
    val opened = session.open_html(
        "https://store{index}.example/page",
        "<html><body><script>localStorage.setItem('key', 'value-{index}');</script></body></html>"
    )
    expect(opened.is_ok()).to_be(true)
    index = index + 1
val final_navigation = session.open_html(
    "https://empty.example/page", "<html><body>Empty</body></html>"
)
expect(final_navigation.is_ok()).to_be(true)

var retained_oldest = false
var retained_newest = false
for bucket in session.local_storage_by_origin:
    if bucket.origin == "https://store0.example":
        retained_oldest = true
    if bucket.origin == "https://store69.example":
        retained_newest = true
expect(session.local_storage_by_origin.len()).to_equal(64)
expect(retained_oldest).to_equal(false)
expect(retained_newest).to_equal(true)
expect(session.session_storage_by_origin.len()).to_equal(0)

val revisit = session.open_html(
    "https://store6.example/revisit",
    "<html><body><script>localStorage.setItem('key', 'updated');</script></body></html>"
)
expect(revisit.is_ok()).to_be(true)
val leave_revisit = session.open_html(
    "https://after.example/page", "<html><body>After</body></html>"
)
expect(leave_revisit.is_ok()).to_be(true)
expect(session.local_storage_by_origin.len()).to_equal(64)
expect(session.local_storage_by_origin[63].origin).to_equal(
    "https://store6.example"
)
```

</details>

#### bounds aggregate retained Web Storage bytes

- bounds aggregate retained Web Storage bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bounds aggregate retained Web Storage bytes")
val aggregate_limit_bytes: i64 = 16 * 1024 * 1024
val origin_payload_bytes: i64 = 4 * 1024 * 1024
var payload = "x"
while payload.len() < origin_payload_bytes:
    payload = payload + payload

var session = BrowserSession.new()
expect(session.open_html(
    "https://bytes0.example/page", "<html><body>Zero</body></html>"
).is_ok()).to_be(true)
var index = 0
while index < 4:
    val next_index = index + 1
    session.local_storage = [Pair(
        first: "blob", second: payload
    )]
    expect(session.open_html(
        "https://bytes{next_index}.example/page",
        "<html><body>Next</body></html>"
    ).is_ok()).to_be(true)
    index = index + 1

var retained_bytes: i64 = 0
var retained_oldest = false
var retained_newest = false
for bucket in session.local_storage_by_origin:
    retained_bytes = retained_bytes + bucket.origin.len()
    for entry in bucket.entries:
        retained_bytes = (
            retained_bytes + entry.first.len() + entry.second.len()
        )
    if bucket.origin == "https://bytes0.example":
        retained_oldest = true
    if bucket.origin == "https://bytes3.example":
        retained_newest = true
expect(retained_bytes).to_be_less_than(
    aggregate_limit_bytes + 1
)
expect(retained_oldest).to_be(false)
expect(retained_newest).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_storage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserSession storage API.
- BrowserSession storage API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4a55940620a66ced512ec324a653c3ac5975bbacd921d0f785874baf38eead59`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4a55940620a66ced512ec324a653c3ac5975bbacd921d0f785874baf38eead59`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4a55940620a66ced512ec324a653c3ac5975bbacd921d0f785874baf38eead59`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/web/browser_session_storage_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_storage_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/web/browser_session_storage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_storage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_storage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/web/browser_session_storage_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'updates pair lists without changing first-match order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_storage_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps internal names for storage API property collisions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_storage_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps storage API methods callable when stored keys use method names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
