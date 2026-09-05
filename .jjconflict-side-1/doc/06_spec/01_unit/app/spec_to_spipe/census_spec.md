# Census Specification

> Tests covering spec-to-SPipe census classification, spec-to-SPipe census inventory ordering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Census Specification

## Scenarios

### spec-to-SPipe census classification

#### classifies production observations as behavioral

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies production observations as behavioral
   - Expected: classify_spec_text(source) equals `behavioral`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("classifies production observations as behavioral")
val source = "use app.widget.{run_widget}\n" +
    "describe \"widget\":\n    it \"runs\":\n" +
    "        expect(run_widget()).to_equal(7)"
expect(classify_spec_text(source)).to_equal("behavioral")
```

</details>

#### classifies stable model inspection as structural

- classifies stable model inspection as structural
   - Expected: classify_spec_text(source) equals `structural`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("classifies stable model inspection as structural")
val source = "describe \"schema\":\n    it \"keeps layout\":\n        expect(schema_layout()).to_equal(\"v1\")"
expect(classify_spec_text(source)).to_equal("structural")
```

</details>

#### distinguishes real compile-fail and compile-pass execution

- distinguishes real compile-fail and compile-pass execution
   - Expected: classify_spec_text(rejected) equals `compile_fail`
   - Expected: classify_spec_text(accepted) equals `compile_pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("distinguishes real compile-fail and compile-pass execution")
val rejected = "describe \"compiler\":\n    it \"rejects bad syntax\":\n" +
    "        val result = compile_source(\"bad\")\n" +
    "        expect(result.diagnostic).to_contain(\"unexpected\")"
val accepted = "describe \"compiler\":\n    it \"accepts syntax\":\n" +
    "        val result = compile_source(\"val x = 1\")\n" +
    "        expect(result.exit_code).to_equal(0)"
expect(classify_spec_text(rejected)).to_equal("compile_fail")
expect(classify_spec_text(accepted)).to_equal("compile_pass")
```

</details>

#### classifies retained external results as evidence-only

- classifies retained external results as evidence-only
   - Expected: classify_spec_text(source) equals `evidence_only`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("classifies retained external results as evidence-only")
val source = "# @evidence external result artifact\n" +
    "describe \"receipt\":\n    it \"retains it\":\n" +
    "        expect(receipt_hash).to_equal(expected_hash)"
expect(classify_spec_text(source)).to_equal("evidence_only")
```

</details>

#### keeps source-text checks separate from behavioral evidence

- keeps source-text checks separate from behavioral evidence
   - Expected: classify_spec_text(source) equals `source_grep`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps source-text checks separate from behavioral evidence")
val source = "describe \"implementation text\":\n    it \"has a helper\":\n" +
    "        val source = file_read(\"src/x.spl\")\n" +
    "        expect(source.find(\"fn helper\")).to_be_greater_than(-1)"
expect(classify_spec_text(source)).to_equal("source_grep")
```

</details>

#### reports tautologies and assertion-free examples as vacuous

- reports tautologies and assertion-free examples as vacuous
   - Expected: classify_spec_text(tautology) equals `vacuous`
   - Expected: classify_spec_text(no_assertion) equals `vacuous`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports tautologies and assertion-free examples as vacuous")
val tautology = "describe \"weak\":\n    it \"passes\":\n        " + "expect(true)" + ".to_equal(true)"
val no_assertion = "describe \"weak\":\n    it \"prints\":\n        print \"ok\""
expect(classify_spec_text(tautology)).to_equal("vacuous")
expect(classify_spec_text(no_assertion)).to_equal("vacuous")
```

</details>

#### does not promote local arithmetic through the SSpec import

- does not promote local arithmetic through the SSpec import
   - Expected: classify_spec_text(local_only) equals `vacuous`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not promote local arithmetic through the SSpec import")
val local_only = "use std.spec.*\ndescribe \"weak\":\n" +
    "    it \"adds constants\":\n        expect(1 + 1).to_equal(2)"
expect(classify_spec_text(local_only)).to_equal("vacuous")
```

</details>

#### reports unfinished and old compile helpers as placeholders

- reports unfinished and old compile helpers as placeholders
   - Expected: classify_spec_text(unfinished) equals `placeholder`
   - Expected: classify_spec_text(old_helper) equals `placeholder`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports unfinished and old compile helpers as placeholders")
val unfinished = "describe \"future\":\n    it \"exists\":\n        pass_" + "todo(\"implement\", \"REQ-1\")"
val old_helper = "describe \"compile\":\n    it \"accepts\":\n        assert_compiles()"
expect(classify_spec_text(unfinished)).to_equal("placeholder")
expect(classify_spec_text(old_helper)).to_equal("placeholder")
```

</details>

### spec-to-SPipe census inventory ordering

#### sorts by executable path and deterministic tie-break fields

- sorts by executable path and deterministic tie-break fields
   - Expected: ordered.len() equals `3`
   - Expected: ordered[0].canonical_source equals `doc/a.md`
   - Expected: ordered[1].canonical_source equals `doc/b.md`
   - Expected: ordered[2].executable_spec_path equals `test/z_spec.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("sorts by executable path and deterministic tie-break fields")
val z = spec_census_entry(
    "test/z_spec.spl", "doc/z.md", "doc/06_spec/z_spec.md",
    "z-owner", "unit", "behavioral", "planned"
)
val a2 = spec_census_entry(
    "test/a_spec.spl", "doc/b.md", "doc/06_spec/a_spec.md",
    "owner", "system", "structural", "mapped"
)
val a1 = spec_census_entry(
    "test/a_spec.spl", "doc/a.md", "doc/06_spec/a_spec.md",
    "owner", "system", "behavioral", "mapped"
)
val ordered = sort_spec_census_entries([z, a2, a1])
expect(ordered.len()).to_equal(3)
expect(ordered[0].canonical_source).to_equal("doc/a.md")
expect(ordered[1].canonical_source).to_equal("doc/b.md")
expect(ordered[2].executable_spec_path).to_equal("test/z_spec.spl")
```

</details>

#### retains the complete migration inventory contract

- retains the complete migration inventory contract
   - Expected: entry.canonical_source equals `doc/02_requirements/feature/widget.md`
   - Expected: entry.generated_documentation_path equals `doc/06_spec/03_system/app/widget_spec.md`
   - Expected: entry.owner equals `widget-team`
   - Expected: entry.test_tier equals `system`
   - Expected: entry.quality_classification equals `behavioral`
   - Expected: entry.migration_state equals `differential-gate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("retains the complete migration inventory contract")
val entry: SpecCensusEntry = spec_census_entry(
    "test/03_system/app/widget_spec.spl",
    "doc/02_requirements/feature/widget.md",
    "doc/06_spec/03_system/app/widget_spec.md",
    "widget-team",
    "system",
    "behavioral",
    "differential-gate"
)
expect(entry.canonical_source).to_equal("doc/02_requirements/feature/widget.md")
expect(entry.generated_documentation_path).to_equal("doc/06_spec/03_system/app/widget_spec.md")
expect(entry.owner).to_equal("widget-team")
expect(entry.test_tier).to_equal("system")
expect(entry.quality_classification).to_equal("behavioral")
expect(entry.migration_state).to_equal("differential-gate")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spec_to_spipe/census_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering spec-to-SPipe census classification, spec-to-SPipe census inventory ordering.
- spec-to-SPipe census classification
- spec-to-SPipe census inventory ordering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-S2SP-CENSUS-001`
- `REQ-S2SP-CENSUS-002`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dc01ef9d5aade56633c1dffa4c564dd12b5f744718e352f6f67f0d2f62f20034`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc01ef9d5aade56633c1dffa4c564dd12b5f744718e352f6f67f0d2f62f20034`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc01ef9d5aade56633c1dffa4c564dd12b5f744718e352f6f67f0d2f62f20034`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/spec_to_spipe/census_spec.spl
mirror: doc/06_spec/01_unit/app/spec_to_spipe/census_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/app/spec_to_spipe/census_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/spec_to_spipe/census_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/spec_to_spipe/census_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/spec_to_spipe/census_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/spec_to_spipe/census_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies production observations as behavioral' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spec_to_spipe/census_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies stable model inspection as structural' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spec_to_spipe/census_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'distinguishes real compile-fail and compile-pass execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
