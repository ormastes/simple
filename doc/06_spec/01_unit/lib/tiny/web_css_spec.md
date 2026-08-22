# web_css_spec

> Verifies the web css behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# web_css_spec

Verifies the web css behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/web_css_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the web css behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### bounded tiny CSS declarations

#### parses tag class and ID selectors with admitted properties

- Verify: parses tag class and ID selectors with admitted properties
   - Expected: parsed.declarations.len() equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: parsed.declarations[0].selector_kind equals `TINY_CSS_SELECTOR_TAG`
   - Expected: parsed.declarations[2].selector_kind equals `TINY_CSS_SELECTOR_CLASS`
   - Expected: parsed.declarations[3].selector_kind equals `TINY_CSS_SELECTOR_ID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_CSS-001
step("Verify: parses tag class and ID selectors with admitted properties")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val parsed = tiny_css_parse("p { color: red; margin: 2px } .note { padding: 4px } #main { display: block }", 4, 8)
expect(parsed.status.is_ok()).to_be(true)
expect(parsed.declarations.len()).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(parsed.declarations[0].selector_kind).to_equal(TINY_CSS_SELECTOR_TAG)
expect(parsed.declarations[2].selector_kind).to_equal(TINY_CSS_SELECTOR_CLASS)
expect(parsed.declarations[3].selector_kind).to_equal(TINY_CSS_SELECTOR_ID)
```

</details>

#### reports unsupported selectors and properties explicitly

- Verify: reports unsupported selectors and properties explicitly
   - Expected: parsed.unsupported_count equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: parsed.declarations.len() equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_CSS-001
step("Verify: reports unsupported selectors and properties explicitly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val parsed = tiny_css_parse("div > p { color: red } p { transform: rotate(1deg); width: 10px }", 4, 8)
expect(parsed.status.is_ok()).to_be(false)
expect(parsed.unsupported_count).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(parsed.declarations.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### enforces rule and declaration bounds and malformed syntax

- Verify: enforces rule and declaration bounds and malformed syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-TINY_WEB_CSS-001
step("Verify: enforces rule and declaration bounds and malformed syntax")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(tiny_css_parse("p { color: red } div { color: blue }", 1, 8).status.is_ok()).to_be(false)
expect(tiny_css_parse("p { color: red; width: 1px }", 2, 1).status.is_ok()).to_be(false)
expect(tiny_css_parse("p color: red", 2, 2).status.is_ok()).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `62db77cd39fdbe0a9d3d5255fc76b876bf87507c24e0d38857b55ac9d260bcc2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `62db77cd39fdbe0a9d3d5255fc76b876bf87507c24e0d38857b55ac9d260bcc2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `62db77cd39fdbe0a9d3d5255fc76b876bf87507c24e0d38857b55ac9d260bcc2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/tiny/web_css_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/web_css_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/web_css_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/tiny/web_css_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/web_css_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
