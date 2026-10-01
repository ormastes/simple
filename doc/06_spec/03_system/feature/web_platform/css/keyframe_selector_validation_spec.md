# CSS Keyframe Selector Validation

> Proves that each comma-separated keyframe selector list is validated

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Keyframe Selector Validation

Proves that each comma-separated keyframe selector list is validated

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/keyframe_selector_validation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves that each comma-separated keyframe selector list is validated
atomically before any declarations are inserted. Invalid and empty members
discard their whole block without changing valid duplicate-offset cascade or
implicit-endpoint animation behavior.

## Scenarios

### CSS keyframe selector validation

#### should discard an invalid selector list before inserting its block

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should discard an invalid selector list before inserting its block
- Validate normalized and malformed selector tables atomically
   - Expected: registry.entries.len() equals `1`
   - Expected: normalized_registry.entries[0].frames[0].offset equals `0.0`
   - Expected: normalized_registry.entries[0].frames[1].offset equals `1.0`
   - Expected: endpoint_registry.entries[0].frames[0].offset equals `0.0`
   - Expected: endpoint_registry.entries[0].frames[1].offset equals `1.0`
   - Expected: numeric_registry.entries[0].frames[0].offset equals `0.005`
   - Expected: numeric_registry.entries[0].frames[1].offset equals `1.0`
   - Expected: exactly_bounded.entries[0].frames.len() equals `1`
   - Expected: exactly_bounded.entries[0].frames[0].offset equals `0.0`
   - Expected: over_bounded.entries[0].frames.len() equals `0`
   - Expected: remaining_rejected.entries[0].frames.len() equals `1`
   - Expected: remaining_rejected.entries[0].frames[0].offset equals `0.0`
   - Expected: remaining_control.entries[0].frames.len() equals `2`
   - Expected: remaining_control.entries[0].frames[1].offset equals `1.0`
- Reconcile the retained paused animation scheduler state
   - Expected: mixed_instances.len() equals `1`
   - Expected: mixed_instances[0].paused_elapsed_ms equals `0`
   - Expected: mixed_instances[0].duration_ms equals `1000`
   - Expected: trailing_instances.len() equals `1`
- Lower atomic rejection and valid controls through canonical Draw IR
   - Expected: _draw_color(_mixed_invalid_html()) equals `RED`
   - Expected: _draw_color(_trailing_comma_html()) equals `RED`
   - Expected: _draw_color(_removed_invalid_html()) equals `RED`
   - Expected: _draw_color(_duplicate_zero_html()) equals `BLUE`
   - Expected: _draw_color(_implicit_endpoint_html()) equals `RED`
   - Expected: _draw_color(_quota_html(256)) equals `BLUE`
   - Expected: _draw_color(_quota_html(257)) equals `RED`
   - Expected: _draw_color(_remaining_budget_html("from,to")) equals `RED`
   - Expected: _draw_color(_remaining_budget_html("to")) equals `RED`
- Render exact Engine2D pixels for rejection and control frames
   - Expected: mixed_pixels equals `removed_pixels`
   - Expected: trailing_pixels equals `removed_pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 111 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should discard an invalid selector list before inserting its block")
step("Validate normalized and malformed selector tables atomically")
val selectors: [text] = [
    "  FrOm , TO  ",
    "0%,100%",
    ".5%,1e2%",
    "bogus",
    "1..0%",
    "1e%",
    "50 %",
    "NaN%",
    "Infinity%",
    "1e309%",
    "-1%",
    "100.1%",
    "",
    ",from",
    "from,",
    "from,,to",
    "from,bogus"
]
val expected_frame_counts: [i32] = [
    2, 2, 2,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
]
var selector_index = 0
while selector_index < selectors.len():
    val registry = extract_keyframes(
        "@keyframes probe{" + selectors[selector_index] +
        "{{opacity:1}}}"
    )
    expect(registry.entries.len()).to_equal(1)
    expect(registry.entries[0].frames.len()).to_equal(
        expected_frame_counts[selector_index]
    )
    selector_index = selector_index + 1
val normalized_registry = extract_keyframes(
    "@keyframes probe{  FrOm , TO  {opacity:1}}"
)
expect(normalized_registry.entries[0].frames[0].offset).to_equal(0.0)
expect(normalized_registry.entries[0].frames[1].offset).to_equal(1.0)
val endpoint_registry = extract_keyframes(
    "@keyframes probe{0%,100%{opacity:1}}"
)
expect(endpoint_registry.entries[0].frames[0].offset).to_equal(0.0)
expect(endpoint_registry.entries[0].frames[1].offset).to_equal(1.0)
val numeric_registry = extract_keyframes(
    "@keyframes probe{.5%,1e2%{opacity:1}}"
)
expect(numeric_registry.entries[0].frames[0].offset).to_equal(0.005)
expect(numeric_registry.entries[0].frames[1].offset).to_equal(1.0)

val exactly_bounded = extract_keyframes(
    "@keyframes quota{" +
    _repeated_selector_list("from", 256) + "{{opacity:1}}}"
)
val over_bounded = extract_keyframes(
    "@keyframes quota{" +
    _repeated_selector_list("from", 257) + "{{opacity:1}}}"
)
val remaining_rejected = extract_keyframes(
    "@keyframes quota{" +
    _repeated_selector_list("from", 255) +
    "{{opacity:0}}from,to{{opacity:1}}}"
)
val remaining_control = extract_keyframes(
    "@keyframes quota{" +
    _repeated_selector_list("from", 255) +
    "{{opacity:0}}to{{opacity:1}}}"
)
expect(exactly_bounded.entries[0].frames.len()).to_equal(1)
expect(exactly_bounded.entries[0].frames[0].offset).to_equal(0.0)
expect(over_bounded.entries[0].frames.len()).to_equal(0)
expect(remaining_rejected.entries[0].frames.len()).to_equal(1)
expect(remaining_rejected.entries[0].frames[0].offset).to_equal(0.0)
expect(remaining_control.entries[0].frames.len()).to_equal(2)
expect(remaining_control.entries[0].frames[1].offset).to_equal(1.0)

step("Reconcile the retained paused animation scheduler state")
val mixed_instances = _instances(_mixed_invalid_html())
val trailing_instances = _instances(_trailing_comma_html())
expect(mixed_instances.len()).to_equal(1)
expect(mixed_instances[0].paused).to_be(true)
expect(mixed_instances[0].paused_elapsed_ms).to_equal(0)
expect(mixed_instances[0].duration_ms).to_equal(1000)
expect(trailing_instances.len()).to_equal(1)

step("Lower atomic rejection and valid controls through canonical Draw IR")
expect(_draw_color(_mixed_invalid_html())).to_equal(RED)
expect(_draw_color(_trailing_comma_html())).to_equal(RED)
expect(_draw_color(_removed_invalid_html())).to_equal(RED)
expect(_draw_color(_duplicate_zero_html())).to_equal(BLUE)
expect(_draw_color(_implicit_endpoint_html())).to_equal(RED)
expect(_draw_color(_quota_html(256))).to_equal(BLUE)
expect(_draw_color(_quota_html(257))).to_equal(RED)
expect(_draw_color(_remaining_budget_html("from,to"))).to_equal(RED)
expect(_draw_color(_remaining_budget_html("to"))).to_equal(RED)

step("Render exact Engine2D pixels for rejection and control frames")
val removed_pixels = _pixels(_removed_invalid_html())
val mixed_pixels = _pixels(_mixed_invalid_html())
val trailing_pixels = _pixels(_trailing_comma_html())
val duplicate_pixels = _pixels(_duplicate_zero_html())
val implicit_pixels = _pixels(_implicit_endpoint_html())
expect(mixed_pixels).to_equal(removed_pixels)
expect(trailing_pixels).to_equal(removed_pixels)
expect(mixed_pixels).to_contain(RED)
expect(trailing_pixels).to_contain(RED)
expect(duplicate_pixels).to_contain(BLUE)
expect(implicit_pixels).to_contain(RED)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-003`
- `REQ-WEB-BROWSER-004`
- `REQ-WEB-BROWSER-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e3402d249202b610d4f7f75cd779563391c3c82e690d62f97ea9e146992bc061`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e3402d249202b610d4f7f75cd779563391c3c82e690d62f97ea9e146992bc061`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e3402d249202b610d4f7f75cd779563391c3c82e690d62f97ea9e146992bc061`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/feature/web_platform/css/keyframe_selector_validation_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/css/keyframe_selector_validation_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=95 oracle=70
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/feature/web_platform/css/keyframe_selector_validation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/css/keyframe_selector_validation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/css/keyframe_selector_validation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 18 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/web_platform/css/keyframe_selector_validation_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/feature/web_platform/css/keyframe_selector_validation_spec.spl:131:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should discard an invalid selector list before inserting its block' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/keyframe_selector_validation_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should discard an invalid selector list before inserting its block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
