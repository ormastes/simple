# Claude Full CustomSelect useSelectNavigation

> Checks real navigation parity for wrapping, disabled options, home/end, empty lists, and source helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CustomSelect useSelectNavigation

Checks real navigation parity for wrapping, disabled options, home/end, empty lists, and source helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/custom_select_navigation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks real navigation parity for wrapping, disabled options, home/end, empty lists, and source helpers.

## Scenarios

### Claude full CustomSelect useSelectNavigation

#### wraps next and previous while skipping disabled options

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- wraps next and previous while skipping disabled options
- Navigate over the sample list
   - Expected: nextSelectNavigationIndex(options, 0) equals `2`
   - Expected: nextSelectNavigationIndex(options, 2) equals `4`
   - Expected: nextSelectNavigationIndex(options, 4) equals `0`
   - Expected: previousSelectNavigationIndex(options, 0) equals `4`
   - Expected: previousSelectNavigationIndex(options, 4) equals `2`
   - Expected: previousSelectNavigationIndex(options, 2) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wraps next and previous while skipping disabled options")
step("Navigate over the sample list")
val options = sampleSelectNavigationOptions()
expect(nextSelectNavigationIndex(options, 0)).to_equal(2)
expect(nextSelectNavigationIndex(options, 2)).to_equal(4)
expect(nextSelectNavigationIndex(options, 4)).to_equal(0)
expect(previousSelectNavigationIndex(options, 0)).to_equal(4)
expect(previousSelectNavigationIndex(options, 4)).to_equal(2)
expect(previousSelectNavigationIndex(options, 2)).to_equal(0)
```

</details>

#### uses home and end for first and last enabled options

- uses home and end for first and last enabled options
- Resolve boundary navigation
   - Expected: homeSelectNavigationIndex(options) equals `0`
   - Expected: endSelectNavigationIndex(options) equals `4`
   - Expected: firstEnabledSelectNavigationIndex(options) equals `0`
   - Expected: lastEnabledSelectNavigationIndex(options) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses home and end for first and last enabled options")
step("Resolve boundary navigation")
val options = sampleSelectNavigationOptions()
expect(homeSelectNavigationIndex(options)).to_equal(0)
expect(endSelectNavigationIndex(options)).to_equal(4)
expect(firstEnabledSelectNavigationIndex(options)).to_equal(0)
expect(lastEnabledSelectNavigationIndex(options)).to_equal(4)
```

</details>

#### handles empty and all-disabled option lists

- handles empty and all-disabled option lists
- Return no active index for empty data
   - Expected: nextSelectNavigationIndex(empty, 0) equals `-1`
   - Expected: previousSelectNavigationIndex(empty, 0) equals `-1`
   - Expected: homeSelectNavigationIndex(empty) equals `-1`
   - Expected: endSelectNavigationIndex(empty) equals `-1`
   - Expected: selectNavigationValueAt(empty, 0) equals ``
- Return no active index when every option is disabled
   - Expected: nextSelectNavigationIndex(disabled, 0) equals `-1`
   - Expected: previousSelectNavigationIndex(disabled, 1) equals `-1`
   - Expected: createSelectNavigationState(disabled, "a").isEmpty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty and all-disabled option lists")
step("Return no active index for empty data")
val empty: [SelectNavigationOption] = []
expect(nextSelectNavigationIndex(empty, 0)).to_equal(-1)
expect(previousSelectNavigationIndex(empty, 0)).to_equal(-1)
expect(homeSelectNavigationIndex(empty)).to_equal(-1)
expect(endSelectNavigationIndex(empty)).to_equal(-1)
expect(selectNavigationValueAt(empty, 0)).to_equal("")

step("Return no active index when every option is disabled")
val disabled = [SelectNavigationOption.unavailable("a", "A"), SelectNavigationOption.unavailable("b", "B")]
expect(nextSelectNavigationIndex(disabled, 0)).to_equal(-1)
expect(previousSelectNavigationIndex(disabled, 1)).to_equal(-1)
expect(createSelectNavigationState(disabled, "a").isEmpty()).to_equal(true)
```

</details>

#### creates state from values and normalizes disabled selections

- creates state from values and normalizes disabled selections
- Keep enabled values and fall back from disabled ones
   - Expected: selected.activeIndex equals `2`
   - Expected: selected.activeValue() equals `gamma`
   - Expected: selected.next().activeValue() equals `epsilon`
   - Expected: selected.previous().activeValue() equals `alpha`
   - Expected: createSelectNavigationState(options, "beta").activeIndex equals `0`
   - Expected: selectNavigationIndexByValue(options, "missing") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates state from values and normalizes disabled selections")
step("Keep enabled values and fall back from disabled ones")
val options = sampleSelectNavigationOptions()
val selected = createSelectNavigationState(options, "gamma")
expect(selected.activeIndex).to_equal(2)
expect(selected.activeValue()).to_equal("gamma")
expect(selected.next().activeValue()).to_equal("epsilon")
expect(selected.previous().activeValue()).to_equal("alpha")
expect(createSelectNavigationState(options, "beta").activeIndex).to_equal(0)
expect(selectNavigationIndexByValue(options, "missing")).to_equal(0)
```

</details>

#### exports source helper parity

- exports source helper parity
- Pin upstream source helpers
   - Expected: useSelectNavigationModeledSourceFile() equals `src/components/CustomSelect/use-select-navigation.ts`
   - Expected: useSelectNavigationModeledHookName() equals `useSelectNavigation`
   - Expected: useSelectNavigationModeledSourceHelper() equals `getNextSelectableOption`
   - Expected: useSelectNavigationSourceLinesModeled() equals `653`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source helper parity")
step("Pin upstream source helpers")
expect(useSelectNavigationModeledSourceFile()).to_equal("src/components/CustomSelect/use-select-navigation.ts")
expect(useSelectNavigationModeledHookName()).to_equal("useSelectNavigation")
expect(useSelectNavigationModeledSourceHelper()).to_equal("getNextSelectableOption")
expect(useSelectNavigationSourceLinesModeled()).to_equal(653)
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

- Canonical SPipe generation for source `5b98a7be2bfc1406f414785904003ea6222bb5b15ff7a1700c637c6fa85771f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5b98a7be2bfc1406f414785904003ea6222bb5b15ff7a1700c637c6fa85771f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5b98a7be2bfc1406f414785904003ea6222bb5b15ff7a1700c637c6fa85771f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/components/custom_select_navigation_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/custom_select_navigation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/custom_select_navigation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/custom_select_navigation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/custom_select_navigation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/custom_select_navigation_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps next and previous while skipping disabled options' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/custom_select_navigation_spec.spl:161:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses home and end for first and last enabled options' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/custom_select_navigation_spec.spl:171:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles empty and all-disabled option lists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
