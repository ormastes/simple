# parse001_spec_files_spec

> The lint parser must accept the `describe`/`it` block-call DSL (both the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# parse001_spec_files_spec

The lint parser must accept the `describe`/`it` block-call DSL (both the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/parse001_spec_files_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## PARSE001 false positive on spec-DSL files

    The lint parser must accept the `describe`/`it` block-call DSL (both the
    paren and no-paren-with-trailing-colon-block forms) that the real
    compiler and test runner already execute green, while still rejecting
    genuinely malformed sources.

## Scenarios

### PARSE001 on describe/it spec-DSL sources

#### minimal describe/it fixtures

#### accepts the no-paren `describe \

- accepts the no-paren `describe \


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the no-paren `describe \")
val source = "use std.spec.*\n\ndescribe \"d\":\n    it \"passes\":\n        expect(1).to_equal(1)\n"
expect(parses_clean(source)).to_be_true()
```

</details>

#### accepts the paren `describe(\

- accepts the paren `describe(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the paren `describe(\")
val source = "use std.spec.*\n\ndescribe(\"d\"):\n    it(\"passes\"):\n        expect(1).to_equal(1)\n"
expect(parses_clean(source)).to_be_true()
```

</details>

#### accepts a bare module-level call-with-block unrelated to spec (general grammar, not a special case)

- accepts a bare module-level call-with-block unrelated to spec (general grammar, not a special case)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a bare module-level call-with-block unrelated to spec (general grammar, not a special case)")
val source = "fn my_block(name: text, body: fn() -> void):\n    body()\n\nmy_block(\"d\"):\n    print(1)\n"
expect(parses_clean(source)).to_be_true()
```

</details>

#### accepts nested context blocks with step()/assert_* calls (bug doc's original repro shape)

- accepts nested context blocks with step()/assert_* calls (bug doc's original repro shape)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts nested context blocks with step()/assert_* calls (bug doc's original repro shape)")
val source = "use std.spec.*\n\ndescribe \"Stage-4 memory gate sampler\":\n    it \"records rows\":\n        step(\"Prepare\")\n        val rc = 0\n        assert_equal(rc, 0)\n"
expect(parses_clean(source)).to_be_true()
```

</details>

#### genuinely broken sources (the rule must not be neutered)

#### still reports PARSE001 on an unclosed call (missing paren)

- still reports PARSE001 on an unclosed call (missing paren)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still reports PARSE001 on an unclosed call (missing paren)")
val source = "use std.spec.*\n\ndescribe \"d\":\n    it \"broken\":\n        expect(1.to_equal(1)\n"
expect(parses_clean(source)).to_be_false()
```

</details>

#### still reports PARSE001 on a dangling colon with no block at all

- still reports PARSE001 on a dangling colon with no block at all


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still reports PARSE001 on a dangling colon with no block at all")
val source = "use std.spec.*\n\ndescribe(\"d\"):"
expect(parses_clean(source)).to_be_false()
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

- Canonical SPipe generation for source `9731759baf20d99cdfc4cf06163c6092ccb5bc54323071871654d41ba568228f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9731759baf20d99cdfc4cf06163c6092ccb5bc54323071871654d41ba568228f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9731759baf20d99cdfc4cf06163c6092ccb5bc54323071871654d41ba568228f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/lint/parse001_spec_files_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/parse001_spec_files_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lint/parse001_spec_files_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint/parse001_spec_files_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint/parse001_spec_files_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the no-paren `describe \' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/parse001_spec_files_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the paren `describe(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/parse001_spec_files_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a bare module-level call-with-block unrelated to spec (general grammar, not a special case)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
