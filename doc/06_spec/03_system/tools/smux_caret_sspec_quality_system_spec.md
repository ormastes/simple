# smux_caret_sspec_quality_system_spec

> smux and LLM Caret SSpec quality acceptance flow.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smux_caret_sspec_quality_system_spec

smux and LLM Caret SSpec quality acceptance flow.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/smux_caret_sspec_quality_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

smux and LLM Caret SSpec quality acceptance flow.

Every legacy `fn test_*` + `print("PASS: ...")` spec in this lane executes zero
examples, so the fail-closed zero-examples gate holds it permanently RED while
its own prints claim success. A `FAIL` print never fails the process, so those
checks were never oracles.

This scenario reads the lane's committed spec sources and asserts they are
Modern SSpec: `describe`/`it` blocks carrying `expect(...)` oracles, with no
`fn test_*`, no `main()`-driven prints, and byte-identical mirror trees.

Fail-closed by construction. A spec file that is missing, unreadable, or empty
classifies as NOT modern and fails the example — it is never skipped and never
counted as a pass. The classifier itself is proven to discriminate (see
SSQ-CLS-001/002) so a green run cannot come from a vacuous oracle.

## Scenarios

### smux and LLM Caret SSpec quality

### SSQ-CLS: the quality classifier discriminates

#### should classify a legacy print-based spec as legacy, not modern

- should classify a legacy print-based spec as legacy, not modern
- Classify a synthetic legacy main()-driven source
   - Expected: q.legacy_fn_test_count equals `1`
   - Expected: q.print_pass_count equals `2`
   - Expected: q.it_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should classify a legacy print-based spec as legacy, not modern")
step("Classify a synthetic legacy main()-driven source")
val legacy_src = "fn test_thing():\n    if true:\n        print(\"PASS: test_thing\")\n    else:\n        print(\"FAIL: test_thing\")\n\nfn main():\n    test_thing()\n"
val q = classify_spec_source("<synthetic-legacy>", true, legacy_src)
expect(q.legacy_fn_test_count).to_equal(1)
expect(q.print_pass_count).to_equal(2)
expect(q.it_count).to_equal(0)
expect(q.is_legacy()).to_be(true)
expect(q.is_modern()).to_be(false)
```

</details>

#### should classify a synthetic modern spec as modern

- should classify a synthetic modern spec as modern
- Classify a synthetic describe/it source carrying oracles
   - Expected: q.describe_count equals `1`
   - Expected: q.it_count equals `1`
   - Expected: q.expect_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should classify a synthetic modern spec as modern")
step("Classify a synthetic describe/it source carrying oracles")
val modern_src = "describe \"a thing\":\n    it \"works\":\n        expect(1).to_equal(1)\n"
val q = classify_spec_source("<synthetic-modern>", true, modern_src)
expect(q.describe_count).to_equal(1)
expect(q.it_count).to_equal(1)
expect(q.expect_count).to_equal(1)
expect(q.is_modern()).to_be(true)
expect(q.is_legacy()).to_be(false)
```

</details>

#### should refuse an empty source rather than passing vacuously

- should refuse an empty source rather than passing vacuously
- Classify an empty source
   - Expected: q.it_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should refuse an empty source rather than passing vacuously")
step("Classify an empty source")
val q = classify_spec_source("<synthetic-empty>", true, "")
expect(q.it_count).to_equal(0)
expect(q.is_modern()).to_be(false)
```

</details>

#### should refuse examples that declare no oracle

- should refuse examples that declare no oracle
- Classify a describe/it source with no expect(...) call
   - Expected: q.it_count equals `1`
   - Expected: q.expect_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should refuse examples that declare no oracle")
step("Classify a describe/it source with no expect(...) call")
val no_oracle = "describe \"a thing\":\n    it \"asserts nothing\":\n        val x = 1\n"
val q = classify_spec_source("<synthetic-no-oracle>", true, no_oracle)
expect(q.it_count).to_equal(1)
expect(q.expect_count).to_equal(0)
expect(q.is_modern()).to_be(false)
```

</details>

#### should treat a missing file as a failure, never as a skip

- should treat a missing file as a failure, never as a skip
- Classify a path that does not exist


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should treat a missing file as a failure, never as a skip")
step("Classify a path that does not exist")
# Assembled by concatenation on purpose. A single literal here would
# look like a real repo-relative path to
# scripts/check/check-spec-missing-path-vacuity.shs, which flags
# specs referencing product paths that do not exist. This one is a
# deliberate negative control, not a stale reference.
val missing = "test/01_unit/os/" + "absent_" + "fixture_spec.spl"
val q = classify_spec_file(missing)
expect(q.present).to_be(false)
expect(q.is_modern()).to_be(false)
```

</details>

### SSQ-SMUX: the smux unit specs are Modern SSpec

#### should carry describe/it oracles and no legacy constructs in smux_spec

- should carry describe/it oracles and no legacy constructs in smux_spec
- Read the committed smux unit spec
- Assert it is Modern SSpec with no surviving legacy construct
   - Expected: q.legacy_fn_test_count equals `0`
   - Expected: q.print_pass_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should carry describe/it oracles and no legacy constructs in smux_spec")
step("Read the committed smux unit spec")
val q = classify_spec_file(SMUX_UNIT)
expect(q.present).to_be(true)
step("Assert it is Modern SSpec with no surviving legacy construct")
expect(q.legacy_fn_test_count).to_equal(0)
expect(q.print_pass_count).to_equal(0)
expect(q.has_main).to_be(false)
expect(q.is_modern()).to_be(true)
```

</details>

#### should declare at least the twenty converted smux examples

- should declare at least the twenty converted smux examples
- Read the committed smux unit spec
   - Expected: q.it_count equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should declare at least the twenty converted smux examples")
step("Read the committed smux unit spec")
val q = classify_spec_file(SMUX_UNIT)
expect(q.it_count).to_equal(20)
```

</details>

#### should carry describe/it oracles and no legacy constructs in the dashboard spec

- should carry describe/it oracles and no legacy constructs in the dashboard spec
- Read the committed smux dashboard unit spec
- Assert it is Modern SSpec with no surviving legacy construct
   - Expected: q.legacy_fn_test_count equals `0`
   - Expected: q.print_pass_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should carry describe/it oracles and no legacy constructs in the dashboard spec")
step("Read the committed smux dashboard unit spec")
val q = classify_spec_file(DASH_UNIT)
expect(q.present).to_be(true)
step("Assert it is Modern SSpec with no surviving legacy construct")
expect(q.legacy_fn_test_count).to_equal(0)
expect(q.print_pass_count).to_equal(0)
expect(q.has_main).to_be(false)
expect(q.is_modern()).to_be(true)
```

</details>

#### should declare at least the twenty-one converted dashboard examples

- should declare at least the twenty-one converted dashboard examples
- Read the committed smux dashboard unit spec
   - Expected: q.it_count equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should declare at least the twenty-one converted dashboard examples")
step("Read the committed smux dashboard unit spec")
val q = classify_spec_file(DASH_UNIT)
expect(q.it_count).to_equal(21)
```

</details>

#### should carry describe/it oracles and no legacy constructs in the smux system spec

- should carry describe/it oracles and no legacy constructs in the smux system spec
- Read the committed smux system spec
- Assert it is Modern SSpec with no surviving legacy construct
   - Expected: q.legacy_fn_test_count equals `0`
   - Expected: q.print_pass_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should carry describe/it oracles and no legacy constructs in the smux system spec")
step("Read the committed smux system spec")
val q = classify_spec_file(SMUX_SYSTEM)
expect(q.present).to_be(true)
step("Assert it is Modern SSpec with no surviving legacy construct")
expect(q.legacy_fn_test_count).to_equal(0)
expect(q.print_pass_count).to_equal(0)
expect(q.has_main).to_be(false)
expect(q.is_modern()).to_be(true)
```

</details>

#### should declare at least the fifty-six converted system examples

- should declare at least the fifty-six converted system examples
- Read the committed smux system spec
   - Expected: q.it_count equals `56`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should declare at least the fifty-six converted system examples")
step("Read the committed smux system spec")
val q = classify_spec_file(SMUX_SYSTEM)
expect(q.it_count).to_equal(56)
```

</details>

### SSQ-MIRROR: duplicate test trees stay identical

#### should keep the smux mirror byte-identical to its 01_unit original

- should keep the smux mirror byte-identical to its 01_unit original
- Read both copies of the smux unit spec
- Compare the two sources byte for byte
   - Expected: file_read(SMUX_MIRROR) equals `file_read(SMUX_UNIT)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep the smux mirror byte-identical to its 01_unit original")
step("Read both copies of the smux unit spec")
expect(file_exists(SMUX_UNIT)).to_be(true)
expect(file_exists(SMUX_MIRROR)).to_be(true)
step("Compare the two sources byte for byte")
expect(file_read(SMUX_MIRROR)).to_equal(file_read(SMUX_UNIT))
```

</details>

#### should keep the dashboard mirror byte-identical to its 01_unit original

- should keep the dashboard mirror byte-identical to its 01_unit original
- Read both copies of the smux dashboard unit spec
- Compare the two sources byte for byte
   - Expected: file_read(DASH_MIRROR) equals `file_read(DASH_UNIT)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep the dashboard mirror byte-identical to its 01_unit original")
step("Read both copies of the smux dashboard unit spec")
expect(file_exists(DASH_UNIT)).to_be(true)
expect(file_exists(DASH_MIRROR)).to_be(true)
step("Compare the two sources byte for byte")
expect(file_read(DASH_MIRROR)).to_equal(file_read(DASH_UNIT))
```

</details>

#### should keep the mirror modern too, so neither tree regresses alone

- should keep the mirror modern too, so neither tree regresses alone
- Classify the mirrored smux spec independently
   - Expected: q.it_count equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep the mirror modern too, so neither tree regresses alone")
step("Classify the mirrored smux spec independently")
val q = classify_spec_file(SMUX_MIRROR)
expect(q.is_modern()).to_be(true)
expect(q.it_count).to_equal(20)
```

</details>

### SSQ-CARET: the LLM Caret lane specs are Modern SSpec

#### should find no legacy print-based construct in the caret unit spec

- should find no legacy print-based construct in the caret unit spec
- Read a committed LLM Caret unit spec
- Assert the caret lane carries oracles, not prints
   - Expected: q.legacy_fn_test_count equals `0`
   - Expected: q.print_pass_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should find no legacy print-based construct in the caret unit spec")
step("Read a committed LLM Caret unit spec")
val q = classify_spec_file(CARET_UNIT)
expect(q.present).to_be(true)
step("Assert the caret lane carries oracles, not prints")
expect(q.legacy_fn_test_count).to_equal(0)
expect(q.print_pass_count).to_equal(0)
expect(q.is_modern()).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `dbc5c9d6c1c162aa408a883f9f8d4ef452c1afd0d00fad52f048e8201cea0476`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dbc5c9d6c1c162aa408a883f9f8d4ef452c1afd0d00fad52f048e8201cea0476`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dbc5c9d6c1c162aa408a883f9f8d4ef452c1afd0d00fad52f048e8201cea0476`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/tools/smux_caret_sspec_quality_system_spec.spl
mirror: doc/06_spec/03_system/tools/smux_caret_sspec_quality_system_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/smux_caret_sspec_quality_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/smux_caret_sspec_quality_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/smux_caret_sspec_quality_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/smux_caret_sspec_quality_system_spec.spl:129:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify a legacy print-based spec as legacy, not modern' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/smux_caret_sspec_quality_system_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should classify a legacy print-based spec as legacy, not modern' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/smux_caret_sspec_quality_system_spec.spl:142:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify a synthetic modern spec as modern' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/smux_caret_sspec_quality_system_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should classify a synthetic modern spec as modern' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/smux_caret_sspec_quality_system_spec.spl:155:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should refuse an empty source rather than passing vacuously' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/smux_caret_sspec_quality_system_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should refuse an empty source rather than passing vacuously' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/smux_caret_sspec_quality_system_spec.spl:164:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should refuse examples that declare no oracle' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/smux_caret_sspec_quality_system_spec.spl:175:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should treat a missing file as a failure, never as a skip' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/smux_caret_sspec_quality_system_spec.spl:191:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should carry describe/it oracles and no legacy constructs in smux_spec' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
