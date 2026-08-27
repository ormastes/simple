# Host Compositor Content Cache Specification

> Tests covering HostCompositor per-window content pixel cache (task #15 remainder item 4).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Compositor Content Cache Specification

## Scenarios

### HostCompositor per-window content pixel cache (task #15 remainder item 4)

#### hits on frame 2 with unchanged content and misses again after a content change

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- hits on frame 2 with unchanged content and misses again after a content change
   - Expected: cache1.stores() equals `1`
   - Expected: cache1.hits() equals `0`
   - Expected: cache2.stores() equals `1`
   - Expected: cache2.hits() equals `1`
   - Expected: cache3.stores() equals `1`
   - Expected: cache3.hits() equals `2`
   - Expected: cache4.stores() equals `2`
   - Expected: cache4.hits() equals `2`
   - Expected: cache5.stores() equals `2`
   - Expected: cache5.hits() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("hits on frame 2 with unchanged content and misses again after a content change")
host_wm_force_direct_chrome(true)
val backend = BrowserCompositorBackend.with_color(640, 480, 0xFF000000u32)
val comp = HostCompositor.new(backend, Size.wh(640, 480))
comp.apply_bridge_request(1, 77, COMP_CREATE_WINDOW.to_i64(), 0, "Terminal", 40, 60, 200, 140, "ready", 1, "/sys/apps/one")
val wid = comp.windows[0].id

# Frame 1: no cache yet for this window -> first content paint stores.
comp.render_frame()
val cache1 = comp.content_caches.get(wid)
assert_not_equal(cache1, nil)
expect(cache1.stores()).to_equal(1)
expect(cache1.hits()).to_equal(0)

# Frame 2: same window, same content, same size -> cache HIT (same
# cache object instance, since (width, height, backend) unchanged).
comp.render_frame()
val cache2 = comp.content_caches.get(wid)
expect(cache2.stores()).to_equal(1)
expect(cache2.hits()).to_equal(1)

# Frame 3: same content again -> another hit.
comp.render_frame()
val cache3 = comp.content_caches.get(wid)
expect(cache3.stores()).to_equal(1)
expect(cache3.hits()).to_equal(2)

# Content change (COMP_UPDATE_TREE) -> next frame is a genuine
# content-hash miss: a new store, hit count does not grow.
comp.apply_bridge_request(2, 77, COMP_UPDATE_TREE.to_i64(), wid, "", 0, 0, 0, 0, "changed", 0, "")
comp.render_frame()
val cache4 = comp.content_caches.get(wid)
expect(cache4.stores()).to_equal(2)
expect(cache4.hits()).to_equal(2)

# Unchanged again after the content settles -> hits resume growing.
comp.render_frame()
val cache5 = comp.content_caches.get(wid)
expect(cache5.stores()).to_equal(2)
expect(cache5.hits()).to_equal(3)
```

</details>

#### replaces (not reuses) the cache when the window is resized

- replaces (not reuses) the cache when the window is resized
   - Expected: before.hits() equals `1`
   - Expected: after.stores() equals `1`
   - Expected: after.hits() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("replaces (not reuses) the cache when the window is resized")
host_wm_force_direct_chrome(true)
val backend = BrowserCompositorBackend.with_color(640, 480, 0xFF000000u32)
val comp = HostCompositor.new(backend, Size.wh(640, 480))
comp.apply_bridge_request(1, 77, COMP_CREATE_WINDOW.to_i64(), 0, "Terminal", 40, 60, 200, 140, "ready", 1, "/sys/apps/one")
val wid = comp.windows[0].id

comp.render_frame()
comp.render_frame()
val before = comp.content_caches.get(wid)
expect(before.hits()).to_equal(1)

comp.apply_bridge_request(2, 77, COMP_RESIZE.to_i64(), wid, "", 0, 0, 260, 180, "", 0, "")
comp.render_frame()
val after = comp.content_caches.get(wid)
# A fresh cache for the new size starts at 0 hits / 1 store, not a
# stale hit carried over from the old (width, height) cache.
expect(after.stores()).to_equal(1)
expect(after.hits()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/host_compositor_content_cache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HostCompositor per-window content pixel cache (task #15 remainder item 4).
- HostCompositor per-window content pixel cache (task #15 remainder item 4)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `941c6afc770cb2c8067e2a96ce6008dd846c7dbbe8383a3835ed61a32342a28c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `941c6afc770cb2c8067e2a96ce6008dd846c7dbbe8383a3835ed61a32342a28c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `941c6afc770cb2c8067e2a96ce6008dd846c7dbbe8383a3835ed61a32342a28c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/compositor/host_compositor_content_cache_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/host_compositor_content_cache_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/host_compositor_content_cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/host_compositor_content_cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/host_compositor_content_cache_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/compositor/host_compositor_content_cache_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hits on frame 2 with unchanged content and misses again after a content change' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/host_compositor_content_cache_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces (not reuses) the cache when the window is resized' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
