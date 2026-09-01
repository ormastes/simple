# Web Product State Specification

> Tests covering tiny Web product state and boundary receipts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Product State Specification

## Scenarios

### tiny Web product state and boundary receipts

#### extracts quoted unquoted and boolean-like tag attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### accepts local navigation and rejects network navigation

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tiny_resource_request(TINY_RESOURCE_BUILTIN, "/index.html", 32, 64).bytes_read).to_equal(32)
expect(tiny_resource_request(TINY_RESOURCE_ROM, "/page.html", 65, 64).status.is_ok()).to_be(false)
expect(tiny_resource_request(99, "/page.html", 1, 64).status.is_ok()).to_be(false)
expect(tiny_resource_request(TINY_RESOURCE_ROM, "../page.html", 1, 64).status.is_ok()).to_be(false)
```

</details>

#### implements the frozen host port with bounded built-in ROM and VFS resources

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = TinyWebMemoryHost.bounded(320, 200, 3, 8)
expect(host.register(10, TINY_RESOURCE_BUILTIN, "/index.html", [1u8, 2u8]).is_ok()).to_be(true)
expect(host.register(11, TINY_RESOURCE_ROM, "/rom.html", [3u8]).is_ok()).to_be(true)
expect(host.register(12, TINY_RESOURCE_VFS, "/vfs.html", [4u8, 5u8]).is_ok()).to_be(true)
host.seal()
expect(host.viewport_width()).to_equal(320)
expect(host.viewport_height()).to_equal(200)
expect(host.resource_bytes(10).len()).to_equal(2)
expect(tiny_web_host_read(host, 10, 8).bytes.len()).to_equal(2)
expect(tiny_web_host_read(host, 10, 1).status.is_ok()).to_be(false)
expect(tiny_web_host_read(host, 99, 8).status.is_ok()).to_be(false)
expect(host.load(TINY_RESOURCE_VFS, "/vfs.html", 8).bytes.len()).to_equal(2)
expect(host.load(TINY_RESOURCE_ROM, "/missing.html", 8).status.is_ok()).to_be(false)
expect(host.register(13, TINY_RESOURCE_ROM, "/overflow.html", [1u8]).is_ok()).to_be(false)
```

</details>

#### distinguishes an admitted empty V2 resource from a missing resource

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = TinyWebMemoryHost.bounded(80, 60, 2, 8)
expect(host.register(20, TINY_RESOURCE_BUILTIN, "/empty.html", []).is_ok()).to_be(true)
host.seal()
expect(tiny_web_host_read_v2(host, 20, 8).status.is_ok()).to_be(true)
expect(tiny_web_host_read_v2(host, 20, 8).bytes.len()).to_equal(0)
expect(tiny_web_host_read_v2(host, 21, 8).status.is_ok()).to_be(false)
```

</details>

#### clamps scrolling and reports whether the offset changed

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = TinyScrollState(offset_y: 0, viewport_height: 100, content_height: 250)
val moved = tiny_scroll_by(state, 60)
expect(moved.state.offset_y).to_equal(60)
expect(moved.changed).to_be(true)
expect(tiny_scroll_to(moved.state, 999).state.offset_y).to_equal(150)
expect(tiny_scroll_to(state, -5).state.offset_y).to_equal(0)
expect(tiny_scroll_to(TinyScrollState(offset_y: 0, viewport_height: 0, content_height: 10), 1).status.is_ok()).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/web_product_state_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering tiny Web product state and boundary receipts.
- tiny Web product state and boundary receipts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3a878e58236e5ec9ca512a3bc74cf0da301a48499e0a97b04e768960cff6b5bd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3a878e58236e5ec9ca512a3bc74cf0da301a48499e0a97b04e768960cff6b5bd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3a878e58236e5ec9ca512a3bc74cf0da301a48499e0a97b04e768960cff6b5bd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/lib/tiny/web_product_state_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/web_product_state_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/web_product_state_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/web_product_state_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/tiny/web_product_state_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/tiny/web_product_state_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/tiny/web_product_state_spec.spl:16:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'extracts quoted unquoted and boolean-like tag attributes' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/web_product_state_spec.spl:23:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'accepts local navigation and rejects network navigation' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/web_product_state_spec.spl:32:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'validates bounded built-in ROM and VFS resource requests' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/web_product_state_spec.spl:38:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'implements the frozen host port with bounded built-in ROM and VFS resources' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
