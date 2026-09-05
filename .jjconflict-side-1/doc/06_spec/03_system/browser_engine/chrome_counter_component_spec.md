# Chrome <-> Simple Counter Component IO Differential

> Phase-4 per-COMPONENT harness: one interactive counter widget is loaded by

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chrome <-> Simple Counter Component IO Differential

Phase-4 per-COMPONENT harness: one interactive counter widget is loaded by

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | In Progress |
| Source | `test/03_system/browser_engine/chrome_counter_component_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Phase-4 per-COMPONENT harness: one interactive counter widget is loaded by
Chrome and by Simple's browser_engine, its IO is driven through each engine's
REAL event path (Chrome: `page.click` + real inline JS; Simple:
`be_dom_dispatch_event_to_route` + `script_host_apply_action_to_route`), and
box geometry is compared per interaction state as canonical sorted text via
the std `layout_text_diff` tool. Audience: anyone changing the browser_engine
layout, DOM event dispatch, or DOM mutation paths.

## Scope and Preconditions

Requires Chrome/Chromium and node. Driver:
`sh tools/component_diff/run_component_diff.shs` (runs 2 `bin/simple run`
extractions; cannot be nested inside `bin/simple test`). This spec gates on
the driver's retained evidence (`tools/component_diff/out/counter/summary.txt`),
fail-closed: missing evidence, evidence older than fixture/extractors/differ,
or a chrome side without a real `Chrome/<version>` string all FAIL. There is
deliberately no "chrome absent, therefore pass" path.

## Primary Workflow

1. Run the driver; read `out/counter/summary.txt`.
2. Assert non-vacuity (3 states, >0 node lines compared).
3. Assert the IO chain on the Simple side: click dispatch collected the real
   inline onclick and the button-activate default action; display text then
   matches Chrome's real-JS display text at every state.
4. Assert per-engine IO invariants: increment CHANGES geometry, decrement
   returns it EXACTLY to the initial state.
5. Pin the measured geometry divergence fail-closed (may shrink, not grow).

## Key Concepts

| Concept | Description |
|---------|-------------|
| Canonical geometry text | `<key> [x,y wxh] "text"`, sorted; keys per layout_diff CONTRACT |
| Counter model | Simple does not execute inline JS; the extractor mirrors bump()/setCount() after real dispatch — see tools/component_diff/CONTRACT.md |
| Divergence pin | 8 diff lines/state, 24 total (body box, button text centering, line height) |

## Related Specifications

- [Component IO differential contract](../../../tools/component_diff/CONTRACT.md)
- [Layout differential](chrome_layout_differential_spec.spl)

## Evidence and Provenance

Measured against Google Chrome for Testing 151.0.7922.34, viewport 800x600.
Retained evidence: `tools/component_diff/out/counter/summary.txt` and per-state
diffs `tools/component_diff/out/counter/counter.stateK.diff.txt`.

## Recovery and Troubleshooting

`UNAVAILABLE: no chrome executable found` — pass `--chrome` or set
`COMPONENT_DIFF_CHROME`. A missing `node_modules` under
`tools/pixel_compare/` can be symlinked from the main worktree.

## Compatibility and Limitations

Two engine defects are recorded in the contract: the path-based
`be_dom_dispatch_event_path` family is unusable (`BeDomEvent.create` arity
mismatch), and `be_dom_serialize_html` drops `<style>` text content, so
mutated states re-layout with the pristine fixture's static CSS.

## Scenarios

### Chrome to Simple counter component IO differential

#### has fresh component evidence produced against a real Chrome

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has fresh component evidence produced against a real Chrome
- The summary must exist and be newer than the fixture and every extractor source
   - Expected: evidence_is_stale() is false
- A real Chrome must have produced the chrome side
   - Expected: summary_value("chrome_version") contains `Chrome/`
- All three interaction states must have been compared
   - Expected: summary_i64("states_compared") equals `3`
- A nonzero node-line count must have been compared
   - Expected: summary_i64("nodes_compared") > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has fresh component evidence produced against a real Chrome")
step("The summary must exist and be newer than the fixture and every extractor source")
expect(evidence_is_stale()).to_equal(false)  # oracle: missing/stale FAILS; run sh tools/component_diff/run_component_diff.shs
step("A real Chrome must have produced the chrome side")
expect(summary_value("chrome_version").contains("Chrome/")).to_equal(true)  # oracle: never a vacuous pass
step("All three interaction states must have been compared")
expect(summary_i64("states_compared")).to_equal(3)
step("A nonzero node-line count must have been compared")
expect(summary_i64("nodes_compared") > 0).to_equal(true)  # oracle: 0 divergences over 0 lines is not a pass
```

</details>

#### drives the click through the real Simple session event path

- has fresh component evidence produced against a real Chrome
- The summary must exist and be newer than the fixture and every extractor source
   - Expected: evidence_is_stale() is false
- A real Chrome must have produced the chrome side
   - Expected: summary_value("chrome_version") contains `Chrome/`
- All three interaction states must have been compared
   - Expected: summary_i64("states_compared") equals `3`
- A nonzero node-line count must have been compared
   - Expected: summary_i64("nodes_compared") > 0 is true
- drives the click through the real Simple session event path
- The inc click dispatch must collect exactly the fixture's inline onclick action
   - Expected: summary_i64("dispatch_inc_actions") equals `1`
   - Expected: summary_value("dispatch_inc_inline_onclick") equals `yes`
- The button default action must be button-activate
   - Expected: summary_value("dispatch_inc_default") equals `button-activate`
- Same for the dec click
   - Expected: summary_i64("dispatch_dec_actions") equals `1`
   - Expected: summary_value("dispatch_dec_inline_onclick") equals `yes`
   - Expected: summary_value("dispatch_dec_default") equals `button-activate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has fresh component evidence produced against a real Chrome")
step("The summary must exist and be newer than the fixture and every extractor source")
expect(evidence_is_stale()).to_equal(false)  # oracle: missing/stale FAILS; run sh tools/component_diff/run_component_diff.shs
step("A real Chrome must have produced the chrome side")
expect(summary_value("chrome_version").contains("Chrome/")).to_equal(true)  # oracle: never a vacuous pass
step("All three interaction states must have been compared")
expect(summary_i64("states_compared")).to_equal(3)
step("A nonzero node-line count must have been compared")
expect(summary_i64("nodes_compared") > 0).to_equal(true)  # oracle: 0 divergences over 0 lines is not a pass

# @req REQ-SSPEC-SYSTEM
step("drives the click through the real Simple session event path")
step("The inc click dispatch must collect exactly the fixture's inline onclick action")
expect(summary_i64("dispatch_inc_actions")).to_equal(1)
expect(summary_value("dispatch_inc_inline_onclick")).to_equal("yes")
step("The button default action must be button-activate")
expect(summary_value("dispatch_inc_default")).to_equal("button-activate")
step("Same for the dec click")
expect(summary_i64("dispatch_dec_actions")).to_equal(1)
expect(summary_value("dispatch_dec_inline_onclick")).to_equal("yes")
expect(summary_value("dispatch_dec_default")).to_equal("button-activate")
```

</details>

#### updates the DOM text exactly as Chrome's real JS does at every state

- has fresh component evidence produced against a real Chrome
- The summary must exist and be newer than the fixture and every extractor source
   - Expected: evidence_is_stale() is false
- A real Chrome must have produced the chrome side
   - Expected: summary_value("chrome_version") contains `Chrome/`
- All three interaction states must have been compared
   - Expected: summary_i64("states_compared") equals `3`
- A nonzero node-line count must have been compared
   - Expected: summary_i64("nodes_compared") > 0 is true
- updates the DOM text exactly as Chrome's real JS does at every state
- Chrome (real JS) and Simple (session event path + counter model) must agree on display text
   - Expected: summary_value("display_s0_chrome") equals `count 0`
   - Expected: summary_value("display_s0_simple") equals `count 0`
   - Expected: summary_value("display_s1_chrome") equals `count 1 #`
   - Expected: summary_value("display_s1_simple") equals `count 1 #`
   - Expected: summary_value("display_s2_chrome") equals `count 0`
   - Expected: summary_value("display_s2_simple") equals `count 0`
- All three states must match, counted, not vacuously
   - Expected: summary_i64("display_match") equals `3`
   - Expected: summary_i64("display_total") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has fresh component evidence produced against a real Chrome")
step("The summary must exist and be newer than the fixture and every extractor source")
expect(evidence_is_stale()).to_equal(false)  # oracle: missing/stale FAILS; run sh tools/component_diff/run_component_diff.shs
step("A real Chrome must have produced the chrome side")
expect(summary_value("chrome_version").contains("Chrome/")).to_equal(true)  # oracle: never a vacuous pass
step("All three interaction states must have been compared")
expect(summary_i64("states_compared")).to_equal(3)
step("A nonzero node-line count must have been compared")
expect(summary_i64("nodes_compared") > 0).to_equal(true)  # oracle: 0 divergences over 0 lines is not a pass

# @req REQ-SSPEC-SYSTEM
step("updates the DOM text exactly as Chrome's real JS does at every state")
step("Chrome (real JS) and Simple (session event path + counter model) must agree on display text")
expect(summary_value("display_s0_chrome")).to_equal("count 0")
expect(summary_value("display_s0_simple")).to_equal("count 0")
expect(summary_value("display_s1_chrome")).to_equal("count 1 #")
expect(summary_value("display_s1_simple")).to_equal("count 1 #")
expect(summary_value("display_s2_chrome")).to_equal("count 0")
expect(summary_value("display_s2_simple")).to_equal("count 0")
step("All three states must match, counted, not vacuously")
expect(summary_i64("display_match")).to_equal(3)
expect(summary_i64("display_total")).to_equal(3)
```

</details>

#### re-layouts after the click the way Chrome does

- has fresh component evidence produced against a real Chrome
- The summary must exist and be newer than the fixture and every extractor source
   - Expected: evidence_is_stale() is false
- A real Chrome must have produced the chrome side
   - Expected: summary_value("chrome_version") contains `Chrome/`
- All three interaction states must have been compared
   - Expected: summary_i64("states_compared") equals `3`
- A nonzero node-line count must have been compared
   - Expected: summary_i64("nodes_compared") > 0 is true
- re-layouts after the click the way Chrome does
- Clicking inc must CHANGE geometry in BOTH engines (the display text box grows)
   - Expected: summary_i64("geometry_changed_chrome") equals `1`
   - Expected: summary_i64("geometry_changed_simple") equals `1`
- Clicking dec must return geometry EXACTLY to the initial state in BOTH engines
   - Expected: summary_i64("roundtrip_chrome") equals `1`
   - Expected: summary_i64("roundtrip_simple") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has fresh component evidence produced against a real Chrome")
step("The summary must exist and be newer than the fixture and every extractor source")
expect(evidence_is_stale()).to_equal(false)  # oracle: missing/stale FAILS; run sh tools/component_diff/run_component_diff.shs
step("A real Chrome must have produced the chrome side")
expect(summary_value("chrome_version").contains("Chrome/")).to_equal(true)  # oracle: never a vacuous pass
step("All three interaction states must have been compared")
expect(summary_i64("states_compared")).to_equal(3)
step("A nonzero node-line count must have been compared")
expect(summary_i64("nodes_compared") > 0).to_equal(true)  # oracle: 0 divergences over 0 lines is not a pass

# @req REQ-SSPEC-SYSTEM
step("re-layouts after the click the way Chrome does")
step("Clicking inc must CHANGE geometry in BOTH engines (the display text box grows)")
expect(summary_i64("geometry_changed_chrome")).to_equal(1)
expect(summary_i64("geometry_changed_simple")).to_equal(1)
step("Clicking dec must return geometry EXACTLY to the initial state in BOTH engines")
expect(summary_i64("roundtrip_chrome")).to_equal(1)
expect(summary_i64("roundtrip_simple")).to_equal(1)
```

</details>

#### holds the geometry divergence at or below the recorded baseline

- has fresh component evidence produced against a real Chrome
- The summary must exist and be newer than the fixture and every extractor source
   - Expected: evidence_is_stale() is false
- A real Chrome must have produced the chrome side
   - Expected: summary_value("chrome_version") contains `Chrome/`
- All three interaction states must have been compared
   - Expected: summary_i64("states_compared") equals `3`
- A nonzero node-line count must have been compared
   - Expected: summary_i64("nodes_compared") > 0 is true
- holds the geometry divergence at or below the recorded baseline
- Absent evidence reads as -1 and must FAIL rather than satisfy the ratchet
   - Expected: summary_i64("divergent_total") >= 0 is true
- Measured baseline: 4 divergent node pairs = 8 diff lines per state (body box, button text centering, text line height); may shrink, must not grow
   - Expected: summary_i64("divergent_s0") <= 8 is true
   - Expected: summary_i64("divergent_s1") <= 8 is true
   - Expected: summary_i64("divergent_s2") <= 8 is true
   - Expected: summary_i64("divergent_total") <= 24 is true
- The five exact pairs (counter, display, inc, dec, html) imply at most 4 divergent pairs over 9 lines; nodes_compared must stay 9 so the pin cannot be gamed by dropping nodes
   - Expected: summary_i64("nodes_compared") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has fresh component evidence produced against a real Chrome")
step("The summary must exist and be newer than the fixture and every extractor source")
expect(evidence_is_stale()).to_equal(false)  # oracle: missing/stale FAILS; run sh tools/component_diff/run_component_diff.shs
step("A real Chrome must have produced the chrome side")
expect(summary_value("chrome_version").contains("Chrome/")).to_equal(true)  # oracle: never a vacuous pass
step("All three interaction states must have been compared")
expect(summary_i64("states_compared")).to_equal(3)
step("A nonzero node-line count must have been compared")
expect(summary_i64("nodes_compared") > 0).to_equal(true)  # oracle: 0 divergences over 0 lines is not a pass

# @req REQ-SSPEC-SYSTEM
step("holds the geometry divergence at or below the recorded baseline")
step("Absent evidence reads as -1 and must FAIL rather than satisfy the ratchet")
expect(summary_i64("divergent_total") >= 0).to_equal(true)  # oracle: missing summary is not a pass
step("Measured baseline: 4 divergent node pairs = 8 diff lines per state (body box, button text centering, text line height); may shrink, must not grow")
expect(summary_i64("divergent_s0") <= 8).to_equal(true)  # oracle: ratchet, see tools/component_diff/CONTRACT.md
expect(summary_i64("divergent_s1") <= 8).to_equal(true)
expect(summary_i64("divergent_s2") <= 8).to_equal(true)
expect(summary_i64("divergent_total") <= 24).to_equal(true)
step("The five exact pairs (counter, display, inc, dec, html) imply at most 4 divergent pairs over 9 lines; nodes_compared must stay 9 so the pin cannot be gamed by dropping nodes")
expect(summary_i64("nodes_compared")).to_equal(9)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3d2bba1a8024e3f8df62a4899fa03b89d690ffd50fb3caf77c6e61a795f203db`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3d2bba1a8024e3f8df62a4899fa03b89d690ffd50fb3caf77c6e61a795f203db`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3d2bba1a8024e3f8df62a4899fa03b89d690ffd50fb3caf77c6e61a795f203db`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/browser_engine/chrome_counter_component_spec.spl
mirror: doc/06_spec/03_system/browser_engine/chrome_counter_component_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/browser_engine/chrome_counter_component_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/03_system/browser_engine/chrome_counter_component_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/browser_engine/chrome_counter_component_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has fresh component evidence produced against a real Chrome' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/browser_engine/chrome_counter_component_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drives the click through the real Simple session event path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/browser_engine/chrome_counter_component_spec.spl:169:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'updates the DOM text exactly as Chrome's real JS does at every state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
