# web_product_state_spec

> Verifies the web product state behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# web_product_state_spec

Verifies the web product state behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/web_product_state_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the web product state behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### tiny Web product state and boundary receipts

#### extracts quoted unquoted and boolean-like tag attributes

- Verify: extracts quoted unquoted and boolean-like tag attributes
   - Expected: tiny_html_attribute("a href='/guide' class=nav", "href") equals `/guide`
   - Expected: tiny_html_attribute("a href='/guide' class=nav", "class") equals `nav`
   - Expected: tiny_html_attribute("input checked", "checked") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_PRODUCT_STATE-001
step("Verify: extracts quoted unquoted and boolean-like tag attributes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(tiny_html_attribute("a href='/guide' class=nav", "href")).to_equal("/guide")
expect(tiny_html_attribute("a href='/guide' class=nav", "class")).to_equal("nav")
expect(tiny_html_attribute("input checked", "checked")).to_equal("")
```

</details>

#### accepts local navigation and rejects network navigation

- Verify: accepts local navigation and rejects network navigation
   - Expected: local.kind equals `TINY_NAV_LOCAL`
   - Expected: fragment.kind equals `TINY_NAV_FRAGMENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_PRODUCT_STATE-001
step("Verify: accepts local navigation and rejects network navigation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val local = tiny_navigation_request("/guide/index.html")
val fragment = tiny_navigation_request("#details")
expect(local.status.is_ok()).to_be(true)
expect(local.kind).to_equal(TINY_NAV_LOCAL)
expect(fragment.kind).to_equal(TINY_NAV_FRAGMENT)
expect(tiny_navigation_request("https://example.com").status.is_ok()).to_be(false)
expect(tiny_navigation_request("/../secret").status.is_ok()).to_be(false)
```

</details>

#### validates bounded built-in ROM and VFS resource requests

- Verify: validates bounded built-in ROM and VFS resource requests
   - Expected: tiny_resource_request(TINY_RESOURCE_BUILTIN, "/index.html", 32, 64).bytes_read equals `32)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_PRODUCT_STATE-001
step("Verify: validates bounded built-in ROM and VFS resource requests")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(tiny_resource_request(TINY_RESOURCE_BUILTIN, "/index.html", 32, 64).bytes_read).to_equal(32)  # oracle: pinned constant asserted by this scenario
expect(tiny_resource_request(TINY_RESOURCE_ROM, "/page.html", 65, 64).status.is_ok()).to_be(false)
expect(tiny_resource_request(99, "/page.html", 1, 64).status.is_ok()).to_be(false)
expect(tiny_resource_request(TINY_RESOURCE_ROM, "../page.html", 1, 64).status.is_ok()).to_be(false)
```

</details>

#### implements the frozen host port with bounded built-in ROM and VFS resources

- Verify: implements the frozen host port with bounded built-in ROM and VFS resources
   - Expected: host.viewport_width() equals `320)  # oracle: pinned constant asserted by this scenario`
   - Expected: host.viewport_height() equals `200)  # oracle: pinned constant asserted by this scenario`
   - Expected: host.resource_bytes(10).len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: tiny_web_host_read(host, 10, 8).bytes.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: host.load(TINY_RESOURCE_VFS, "/vfs.html", 8).bytes.len() equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_PRODUCT_STATE-001
step("Verify: implements the frozen host port with bounded built-in ROM and VFS resources")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var host = TinyWebMemoryHost.bounded(320, 200, 3, 8)
expect(host.register(10, TINY_RESOURCE_BUILTIN, "/index.html", [1u8, 2u8]).is_ok()).to_be(true)
expect(host.register(11, TINY_RESOURCE_ROM, "/rom.html", [3u8]).is_ok()).to_be(true)
expect(host.register(12, TINY_RESOURCE_VFS, "/vfs.html", [4u8, 5u8]).is_ok()).to_be(true)
host.seal()
expect(host.viewport_width()).to_equal(320)  # oracle: pinned constant asserted by this scenario
expect(host.viewport_height()).to_equal(200)  # oracle: pinned constant asserted by this scenario
expect(host.resource_bytes(10).len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(tiny_web_host_read(host, 10, 8).bytes.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(tiny_web_host_read(host, 10, 1).status.is_ok()).to_be(false)
expect(tiny_web_host_read(host, 99, 8).status.is_ok()).to_be(false)
expect(host.load(TINY_RESOURCE_VFS, "/vfs.html", 8).bytes.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(host.load(TINY_RESOURCE_ROM, "/missing.html", 8).status.is_ok()).to_be(false)
expect(host.register(13, TINY_RESOURCE_ROM, "/overflow.html", [1u8]).is_ok()).to_be(false)
```

</details>

#### distinguishes an admitted empty V2 resource from a missing resource

- Verify: distinguishes an admitted empty V2 resource from a missing resource
   - Expected: tiny_web_host_read_v2(host, 20, 8).bytes.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_PRODUCT_STATE-001
step("Verify: distinguishes an admitted empty V2 resource from a missing resource")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var host = TinyWebMemoryHost.bounded(80, 60, 2, 8)
expect(host.register(20, TINY_RESOURCE_BUILTIN, "/empty.html", []).is_ok()).to_be(true)
host.seal()
expect(tiny_web_host_read_v2(host, 20, 8).status.is_ok()).to_be(true)
expect(tiny_web_host_read_v2(host, 20, 8).bytes.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(tiny_web_host_read_v2(host, 21, 8).status.is_ok()).to_be(false)
```

</details>

#### clamps scrolling and reports whether the offset changed

- Verify: clamps scrolling and reports whether the offset changed
   - Expected: moved.state.offset_y equals `60)  # oracle: pinned constant asserted by this scenario`
   - Expected: tiny_scroll_to(moved.state, 999).state.offset_y equals `150)  # oracle: pinned constant asserted by this scenario`
   - Expected: tiny_scroll_to(state, -5).state.offset_y equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_PRODUCT_STATE-001
step("Verify: clamps scrolling and reports whether the offset changed")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val state = TinyScrollState(offset_y: 0, viewport_height: 100, content_height: 250)
val moved = tiny_scroll_by(state, 60)
expect(moved.state.offset_y).to_equal(60)  # oracle: pinned constant asserted by this scenario
expect(moved.changed).to_be(true)
expect(tiny_scroll_to(moved.state, 999).state.offset_y).to_equal(150)  # oracle: pinned constant asserted by this scenario
expect(tiny_scroll_to(state, -5).state.offset_y).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(tiny_scroll_to(TinyScrollState(offset_y: 0, viewport_height: 0, content_height: 10), 1).status.is_ok()).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d75b81d7b6a952fe826ffd7eae2b08753265a895d952807c17e632dfcf8dae93`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d75b81d7b6a952fe826ffd7eae2b08753265a895d952807c17e632dfcf8dae93`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d75b81d7b6a952fe826ffd7eae2b08753265a895d952807c17e632dfcf8dae93`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/tiny/web_product_state_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/web_product_state_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/web_product_state_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/tiny/web_product_state_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/web_product_state_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
