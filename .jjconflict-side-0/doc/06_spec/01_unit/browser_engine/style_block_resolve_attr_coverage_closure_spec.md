# Style Block Resolver Attribute-Selector Helpers — Coverage Closure (U4.3, part 4)

> Wave 4 of the WM/GUI/web system-test coverage plan

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Style Block Resolver Attribute-Selector Helpers — Coverage Closure (U4.3, part 4)

Wave 4 of the WM/GUI/web system-test coverage plan

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/style_block_resolve_attr_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Wave 4 of the WM/GUI/web system-test coverage plan
(doc/03_plan/ui/testing/wm_gui_web_system_test_coverage_plan_2026-08-07.md,
unit U4.3). Line coverage IS measurable now; branch coverage remains
unavailable and no branch percentage is claimed here.

The pre-existing dedicated spec
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_block_resolve_selectors_spec.spl`
already gives `style_block_resolve.spl` real, artifact-backed 63% line
coverage (200/317 lines, `Results: 29 total, 29 passed, 0 failed`, measured
via a throwaway `# @cover` header run for this unit, never committed).
Diffing the coverage artifact's hit-line set against every module-level `fn`
body region found 7 fully-uncovered functions; this spec closes the 3 that
are pure text helpers with no `BeDomNode` dependency:

  sb_attr_has_i_flag        — `[attr="val" i]` case-insensitive flag detection
  sb_attr_has_s_flag        — `[attr="val" s]` case-sensitive flag detection
  sb_attr_token_contains    — the `~=` token-list attribute-selector operator

`has_descendant_selector_list_match`, `node_has_relative_has_option_matching`,
`node_has_direct_child_matching`, and `node_has_descendant_matching` all take
a `BeDomNode` and are left for a follow-up unit that builds a DOM fixture —
out of scope for this pure-helper pass.

## Scenarios

### sb_attr_has_i_flag (U4.3 closure)

#### detects a trailing ' i' or ' I' case-insensitivity flag

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects a trailing ' i' or ' I' case-insensitivity flag
   - Expected: sb_attr_has_i_flag("value i") is true
   - Expected: sb_attr_has_i_flag("value I") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects a trailing ' i' or ' I' case-insensitivity flag")
expect(sb_attr_has_i_flag("value i")).to_equal(true)
expect(sb_attr_has_i_flag("value I")).to_equal(true)
```

</details>

#### is false with no trailing flag (both-directions oracle)

- is false with no trailing flag (both-directions oracle)
   - Expected: sb_attr_has_i_flag("value") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is false with no trailing flag (both-directions oracle)")
expect(sb_attr_has_i_flag("value")).to_equal(false)
```

</details>

### sb_attr_has_s_flag (U4.3 closure)

#### detects a trailing ' s' or ' S' case-sensitivity flag

- detects a trailing ' s' or ' S' case-sensitivity flag
   - Expected: sb_attr_has_s_flag("value s") is true
   - Expected: sb_attr_has_s_flag("value S") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects a trailing ' s' or ' S' case-sensitivity flag")
expect(sb_attr_has_s_flag("value s")).to_equal(true)
expect(sb_attr_has_s_flag("value S")).to_equal(true)
```

</details>

#### is false with no trailing flag (both-directions oracle)

- is false with no trailing flag (both-directions oracle)
   - Expected: sb_attr_has_s_flag("value") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is false with no trailing flag (both-directions oracle)")
expect(sb_attr_has_s_flag("value")).to_equal(false)
```

</details>

### sb_attr_token_contains (U4.3 closure)

#### finds a whitespace-delimited token match among several tokens

- finds a whitespace-delimited token match among several tokens
   - Expected: sb_attr_token_contains("btn btn-primary active", "btn-primary") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a whitespace-delimited token match among several tokens")
expect(sb_attr_token_contains("btn btn-primary active", "btn-primary")).to_equal(true)
```

</details>

#### is false when the expected token is only a substring, not a whole token (both-directions oracle)

- is false when the expected token is only a substring, not a whole token (both-directions oracle)
   - Expected: sb_attr_token_contains("btn btn-primary", "btn") is true
   - Expected: sb_attr_token_contains("button", "btn") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is false when the expected token is only a substring, not a whole token (both-directions oracle)")
expect(sb_attr_token_contains("btn btn-primary", "btn")).to_equal(true)
expect(sb_attr_token_contains("button", "btn")).to_equal(false)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `46d2536c6050738270c3cc9714b48547d9e51950c17c8e247d2b3fc99e8885b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `46d2536c6050738270c3cc9714b48547d9e51950c17c8e247d2b3fc99e8885b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `46d2536c6050738270c3cc9714b48547d9e51950c17c8e247d2b3fc99e8885b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/browser_engine/style_block_resolve_attr_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/style_block_resolve_attr_coverage_closure_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/style_block_resolve_attr_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/style_block_resolve_attr_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/style_block_resolve_attr_coverage_closure_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects a trailing ' i' or ' I' case-insensitivity flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/style_block_resolve_attr_coverage_closure_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is false with no trailing flag (both-directions oracle)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/style_block_resolve_attr_coverage_closure_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects a trailing ' s' or ' S' case-sensitivity flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
