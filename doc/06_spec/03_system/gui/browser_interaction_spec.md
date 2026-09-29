# Browser Interaction Capture Evidence

> Verifies capture-backed browser evidence produced by `scripts/check/check-browser-interaction.shs`:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Interaction Capture Evidence

Verifies capture-backed browser evidence produced by `scripts/check/check-browser-interaction.shs`:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | W4, G2.3, G2.4 |
| Category | Testing \| Infrastructure \| GUI |
| Status | In Progress |
| Requirements | doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W4) |
| Design | N/A |
| Source | `test/03_system/gui/browser_interaction_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies capture-backed browser evidence produced by
`scripts/check/check-browser-interaction.shs`:

1. **Scroll (G2.4):** a long page rendered offscreen through the pure-Simple
   web layout renderer at scroll offsets 0 and 120 px; the marker row must
   shift up by exactly 120 px and both framebuffers stay viewport-sized.
2. **Low-res text (G2.3):** a text-heavy page rendered at 640x480 and
   800x600 must pass the readability oracle.
3. **Link-click + back/forward (G2.4):** a two-page local corpus
   (`browser_nav_corpus/page_a.html` → `page_b.html`). The layout-layer
   `hit_test_anchor` maps the anchor's box center back to its `<a>` node, the
   href resolves against the `file://` base, and a back/forward history drives
   navigation. Page A (grey) and page B (green) render to distinct viewport
   framebuffers; the after-click frame is dominated by page B's marker, back
   returns to page A's URL and frame, forward returns to page B.

The test runner masks child/expectation failures for repo-path system specs
(doc/08_tracking/bug/test_runner_masks_child_and_expectation_failures_2026-07-02.md),
so the authoritative gate is the check script's own grep-based exit; this
spec asserts on the persisted evidence contents.

## Related Specifications

- [Production Readiness Master Plan](../../../doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md) — W4
- [GUI Low-Res Readability](../check/gui_low_res_readability_spec.spl)

## Scenarios

### Browser Interaction Capture Evidence

#### browser interaction check produced evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- browser interaction check produced evidence
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("browser interaction check produced evidence")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-browser-interaction.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()
```

</details>

#### scroll offset shifts marker row by exactly 120px

- browser interaction check produced evidence
- scroll offset shifts marker row by exactly 120px
   - Expected: get_env_value(entries, "scroll_status") equals `pass`
   - Expected: get_env_value(entries, "scroll_marker_shift") equals `120`
   - Expected: get_env_value(entries, "scroll_pixels_offset0") equals `172800`
   - Expected: get_env_value(entries, "scroll_pixels_offset120") equals `172800`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("browser interaction check produced evidence")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-browser-interaction.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

# @req REQ-SSPEC-SYSTEM
step("scroll offset shifts marker row by exactly 120px")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "scroll_status")).to_equal("pass")
    expect(get_env_value(entries, "scroll_marker_shift")).to_equal("120")
    expect(get_env_value(entries, "scroll_pixels_offset0")).to_equal("172800")
    expect(get_env_value(entries, "scroll_pixels_offset120")).to_equal("172800")
```

</details>

#### scroll captures both viewport PPMs

- browser interaction check produced evidence
- scroll captures both viewport PPMs


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("browser interaction check produced evidence")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-browser-interaction.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

# @req REQ-SSPEC-SYSTEM
step("scroll captures both viewport PPMs")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "scroll_ppm_offset0_file")).to_contain("scroll_offset0.ppm")
    expect(get_env_value(entries, "scroll_ppm_offset120_file")).to_contain("scroll_offset120.ppm")
```

</details>

#### 640x480 browser text passes readability oracle

- browser interaction check produced evidence
- 640x480 browser text passes readability oracle
   - Expected: get_env_value(entries, "lowres_640x480_status") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("browser interaction check produced evidence")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-browser-interaction.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

# @req REQ-SSPEC-SYSTEM
step("640x480 browser text passes readability oracle")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "lowres_640x480_status")).to_equal("pass")
```

</details>

#### 800x600 browser text passes readability oracle

- browser interaction check produced evidence
- 800x600 browser text passes readability oracle
   - Expected: get_env_value(entries, "lowres_800x600_status") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("browser interaction check produced evidence")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-browser-interaction.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

# @req REQ-SSPEC-SYSTEM
step("800x600 browser text passes readability oracle")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "lowres_800x600_status")).to_equal("pass")
```

</details>

#### link-click hit-test resolves the anchor href and navigates

- browser interaction check produced evidence
- link-click hit-test resolves the anchor href and navigates
   - Expected: get_env_value(entries, "link_click_status") equals `pass`
   - Expected: get_env_value(entries, "link_click_miss_href") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("browser interaction check produced evidence")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-browser-interaction.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

# @req REQ-SSPEC-SYSTEM
step("link-click hit-test resolves the anchor href and navigates")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "link_click_status")).to_equal("pass")
    expect(get_env_value(entries, "link_click_href")).to_end_with("page_b.html")
    # Negative control: a point off the link resolves to no href.
    expect(get_env_value(entries, "link_click_miss_href")).to_equal("")
```

</details>

#### back/forward history returns to page A then page B

- browser interaction check produced evidence
- back/forward history returns to page A then page B
   - Expected: get_env_value(entries, "link_click_after_click_url") equals `href`
   - Expected: get_env_value(entries, "link_click_after_forward_url") equals `href`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("browser interaction check produced evidence")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-browser-interaction.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

# @req REQ-SSPEC-SYSTEM
step("back/forward history returns to page A then page B")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_ok():
    val entries = result.unwrap()
    val href = get_env_value(entries, "link_click_href")
    expect(get_env_value(entries, "link_click_after_click_url")).to_equal(href)
    expect(get_env_value(entries, "link_click_after_back_url")).to_end_with("page_a.html")
    expect(get_env_value(entries, "link_click_after_forward_url")).to_equal(href)
```

</details>

#### navigation renders page A and page B to distinct framebuffers

- browser interaction check produced evidence
- navigation renders page A and page B to distinct framebuffers


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("browser interaction check produced evidence")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_err():
    print "Note: evidence.env not yet generated; run scripts/check/check-browser-interaction.shs"
else:
    val entries = result.unwrap()
    print "Loaded evidence with {entries.len()} entries"
    expect(get_env_value(entries, "overall")).to_be_truthy()

# @req REQ-SSPEC-SYSTEM
step("navigation renders page A and page B to distinct framebuffers")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "link_click_ppm_a_initial")).to_contain("nav_a_initial.ppm")
    expect(get_env_value(entries, "link_click_ppm_b_after_click")).to_contain("nav_b_after_click.ppm")
```

</details>

#### overall status is pass

- 800x600 browser text passes readability oracle
   - Expected: get_env_value(entries, "lowres_800x600_status") equals `pass`
- overall status is pass
   - Expected: get_env_value(entries, "overall") equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("800x600 browser text passes readability oracle")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "lowres_800x600_status")).to_equal("pass")

# @req REQ-SSPEC-SYSTEM
step("overall status is pass")
val result = read_evidence_env(EVIDENCE_PATH)
if result.is_ok():
    val entries = result.unwrap()
    expect(get_env_value(entries, "overall")).to_equal("pass")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W4)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `50dc2c92a3f794ed1cec664055be190c0df2e050f5f575d83807c005dbab0823`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `50dc2c92a3f794ed1cec664055be190c0df2e050f5f575d83807c005dbab0823`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `50dc2c92a3f794ed1cec664055be190c0df2e050f5f575d83807c005dbab0823`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/browser_interaction_spec.spl
mirror: doc/06_spec/03_system/gui/browser_interaction_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/browser_interaction_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/browser_interaction_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/browser_interaction_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'browser interaction check produced evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/browser_interaction_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scroll offset shifts marker row by exactly 120px' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/browser_interaction_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scroll captures both viewport PPMs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
