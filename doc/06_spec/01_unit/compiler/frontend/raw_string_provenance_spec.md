# Raw String Provenance Regression

> Keeps raw, single-quoted, and triple-quoted source strings out of the ordinary

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Raw String Provenance Regression

Keeps raw, single-quoted, and triple-quoted source strings out of the ordinary

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/raw_string_provenance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Keeps raw, single-quoted, and triple-quoted source strings out of the ordinary
string interpolation expansion path, including block-DSL examples in docs.

## Scenarios

### Raw String Provenance

#### preserves raw triple block examples as literal documentation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves raw triple block examples as literal documentation


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves raw triple block examples as literal documentation")
val quotes = "\"\"\""
val content = "loss{{ mse(pred, target) }}"
expect_non_interpolating("r" + quotes + content + quotes, content)
```

</details>

#### preserves bare triple strings as non-interpolating literals

- preserves bare triple strings as non-interpolating literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves bare triple strings as non-interpolating literals")
val quotes = "\"\"\""
val content = "m{{ x^2 + y^2 }}"
expect_non_interpolating(quotes + content + quotes, content)
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-UNIT<br>
> step("preserves bare triple strings as non-interpolating literals")<br>
> val quotes = "\"\"\""<br>
> val content = "$? x^{2} + y^{2}$"<br>
> expect_non_interpolating(quotes + content + quotes, content)

</details>

</details>

#### preserves single-quoted strings as non-interpolating literals

- preserves single-quoted strings as non-interpolating literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves single-quoted strings as non-interpolating literals")
expect_non_interpolating("'literal {{name}}'", "literal {{name}}")
```

</details>

#### decodes doubled braces in canonical block examples

- decodes doubled braces in canonical block examples
   - Expected: math_block_def_new().examples()[0].code equals `m{{ x^2 + y^2 }}`
   - Expected: loss_block_def_new().examples()[0].code equals `loss{{ mse(pred, target) }}`
   - Expected: nograd_block_def_new().examples()[0].code equals `nograd{{ model(test_data) }}`
   - Expected: shell_block_def_new().examples()[0].code equals `sh{{ ls -la }}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes doubled braces in canonical block examples")
expect(math_block_def_new().examples()[0].code).to_equal("m{{ x^2 + y^2 }}")
expect(loss_block_def_new().examples()[0].code).to_equal("loss{{ mse(pred, target) }}")
expect(nograd_block_def_new().examples()[0].code).to_equal("nograd{{ model(test_data) }}")
expect(shell_block_def_new().examples()[0].code).to_equal("sh{{ ls -la }}")
```

<details>
<summary>Rendered scenario source</summary>

> # @req REQ-SSPEC-UNIT<br>
> step("decodes doubled braces in canonical block examples")<br>
> expect(math_block_def_new().examples()[0].code).to_equal("$? x^{2} + y^{2}$")<br>
> expect(loss_block_def_new().examples()[0].code).to_equal("loss{{ mse(pred, target) }}")<br>
> expect(nograd_block_def_new().examples()[0].code).to_equal("nograd{{ model(test_data) }}")<br>
> expect(shell_block_def_new().examples()[0].code).to_equal("sh{{ ls -la }}")

</details>

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6710bed66f009aa6d7f056e282a5cb3605a0353fe69793685de5f14c0e03fe1b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6710bed66f009aa6d7f056e282a5cb3605a0353fe69793685de5f14c0e03fe1b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6710bed66f009aa6d7f056e282a5cb3605a0353fe69793685de5f14c0e03fe1b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/frontend/raw_string_provenance_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/raw_string_provenance_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/raw_string_provenance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/raw_string_provenance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/raw_string_provenance_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves raw triple block examples as literal documentation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/raw_string_provenance_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves bare triple strings as non-interpolating literals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/raw_string_provenance_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves single-quoted strings as non-interpolating literals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
