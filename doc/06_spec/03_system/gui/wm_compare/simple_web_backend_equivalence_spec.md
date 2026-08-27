# Simple Web Backend Equivalence

> Exercises the production Simple Web facade with exact pixel comparison.  The

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Backend Equivalence

Exercises the production Simple Web facade with exact pixel comparison.  The

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_compare/simple_web_backend_equivalence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the production Simple Web facade with exact pixel comparison.  The
widget inventory is independently derived by the canonical coverage gate.

## Scenarios

### Simple Web detailed backend equivalence

#### validates fifty production layouts with exact pixels

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- validates fifty production layouts with exact pixels
   - Protocol capture: after_step
- Render the first fifty deterministic production layouts
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: first_production_layouts_match(50, 40, 30) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates fifty production layouts with exact pixels")
step("Render the first fifty deterministic production layouts")
expect(first_production_layouts_match(50, 40, 30)).to_equal(true)
```

</details>

#### renders all one hundred thirty-two offline site fixtures

- renders all one hundred thirty-two offline site fixtures
   - HTML capture: after_step
- Run every deterministic site through the production facade
   - HTML capture: after_step
   - Evidence: HTML text verified by 1 expected check
   - Expected: all_offline_site_fixtures_match(40, 30) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders all one hundred thirty-two offline site fixtures")
step("Run every deterministic site through the production facade")
expect(all_offline_site_fixtures_match(40, 30)).to_equal(true)
```

</details>

#### covers the forty-three widget fixture witnesses

- covers the forty-three widget fixture witnesses
   - HTML capture: after_step
- Derive and verify the complete widget inventory
   - HTML capture: after_step
   - Evidence: HTML text verified by 1 expected check
   - Expected: widget_coverage_gate_passes() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("covers the forty-three widget fixture witnesses")
step("Derive and verify the complete widget inventory")
expect(widget_coverage_gate_passes()).to_equal(true)
```

</details>

#### keeps text-bearing software and cpu layout pixels exact

- keeps text-bearing software and cpu layout pixels exact
- Compare production layout output without a tolerance
   - Expected: comparison.different_pixels equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps text-bearing software and cpu layout pixels exact")
step("Compare production layout output without a tolerance")
val sample = build_famous_site_sample_corpus()[0]
val software = simple_web_layout_render_html_pixels(sample.html, 160, 120, "software")
val cpu = simple_web_layout_render_html_pixels(sample.html, 160, 120, "cpu")
val comparison = compare_exact(software, cpu, 160, 120)
expect(comparison.different_pixels).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-012`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `102a8d065414de134904500d8a8b90387a10a78ff7bbc3bfed7d582f96f20b7f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `102a8d065414de134904500d8a8b90387a10a78ff7bbc3bfed7d582f96f20b7f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `102a8d065414de134904500d8a8b90387a10a78ff7bbc3bfed7d582f96f20b7f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/wm_compare/simple_web_backend_equivalence_spec.spl
mirror: doc/06_spec/03_system/gui/wm_compare/simple_web_backend_equivalence_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/gui/wm_compare/simple_web_backend_equivalence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_compare/simple_web_backend_equivalence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_compare/simple_web_backend_equivalence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/wm_compare/simple_web_backend_equivalence_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/wm_compare/simple_web_backend_equivalence_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates fifty production layouts with exact pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/simple_web_backend_equivalence_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders all one hundred thirty-two offline site fixtures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_compare/simple_web_backend_equivalence_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers the forty-three widget fixture witnesses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
