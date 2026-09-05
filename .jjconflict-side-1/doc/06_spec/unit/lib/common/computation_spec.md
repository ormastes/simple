# Computation Specification

> Tests covering Computation Expression protocol, CE builder name constants, ce_builder_known, ce_bind_fn_name, ce_return_fn_name, ce_zero_fn_name, naming convention consistency.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Computation Specification

## Scenarios

### Computation Expression protocol

### CE builder name constants

#### CE_BUILDER_RESULT is result_ce

- CE_BUILDER_RESULT is result_ce
   - Expected: CE_BUILDER_RESULT equals `result_ce`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CE_BUILDER_RESULT is result_ce")
expect(CE_BUILDER_RESULT).to_equal("result_ce")
```

</details>

#### CE_BUILDER_OPTION is option_ce

- CE_BUILDER_OPTION is option_ce
   - Expected: CE_BUILDER_OPTION equals `option_ce`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CE_BUILDER_OPTION is option_ce")
expect(CE_BUILDER_OPTION).to_equal("option_ce")
```

</details>

#### CE_BUILDER_SEQ is seq_ce

- CE_BUILDER_SEQ is seq_ce
   - Expected: CE_BUILDER_SEQ equals `seq_ce`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CE_BUILDER_SEQ is seq_ce")
expect(CE_BUILDER_SEQ).to_equal("seq_ce")
```

</details>

### ce_builder_known

#### recognizes result_ce builder

- recognizes result_ce builder
   - Expected: ce_builder_known("result_ce") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes result_ce builder")
expect(ce_builder_known("result_ce")).to_equal(true)
```

</details>

#### recognizes option_ce builder

- recognizes option_ce builder
   - Expected: ce_builder_known("option_ce") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes option_ce builder")
expect(ce_builder_known("option_ce")).to_equal(true)
```

</details>

#### recognizes seq_ce builder

- recognizes seq_ce builder
   - Expected: ce_builder_known("seq_ce") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes seq_ce builder")
expect(ce_builder_known("seq_ce")).to_equal(true)
```

</details>

#### does not recognize unknown builder name

- does not recognize unknown builder name
   - Expected: ce_builder_known("unknown_ce") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not recognize unknown builder name")
expect(ce_builder_known("unknown_ce")).to_equal(false)
```

</details>

#### does not recognize empty string

- does not recognize empty string
   - Expected: ce_builder_known("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not recognize empty string")
expect(ce_builder_known("")).to_equal(false)
```

</details>

#### recognizes CE_BUILDER_RESULT constant

- recognizes CE_BUILDER_RESULT constant
   - Expected: ce_builder_known(CE_BUILDER_RESULT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes CE_BUILDER_RESULT constant")
expect(ce_builder_known(CE_BUILDER_RESULT)).to_equal(true)
```

</details>

#### recognizes CE_BUILDER_OPTION constant

- recognizes CE_BUILDER_OPTION constant
   - Expected: ce_builder_known(CE_BUILDER_OPTION) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes CE_BUILDER_OPTION constant")
expect(ce_builder_known(CE_BUILDER_OPTION)).to_equal(true)
```

</details>

#### recognizes CE_BUILDER_SEQ constant

- recognizes CE_BUILDER_SEQ constant
   - Expected: ce_builder_known(CE_BUILDER_SEQ) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes CE_BUILDER_SEQ constant")
expect(ce_builder_known(CE_BUILDER_SEQ)).to_equal(true)
```

</details>

#### does not recognize partial name

- does not recognize partial name
   - Expected: ce_builder_known("result") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not recognize partial name")
expect(ce_builder_known("result")).to_equal(false)
```

</details>

#### is case sensitive for unknown names

- is case sensitive for unknown names
   - Expected: ce_builder_known("Result_ce") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is case sensitive for unknown names")
expect(ce_builder_known("Result_ce")).to_equal(false)
```

</details>

### ce_bind_fn_name

#### returns bind name for result_ce

- returns bind name for result_ce
   - Expected: ce_bind_fn_name("result_ce") equals `result_ce_bind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns bind name for result_ce")
expect(ce_bind_fn_name("result_ce")).to_equal("result_ce_bind")
```

</details>

#### returns bind name for option_ce

- returns bind name for option_ce
   - Expected: ce_bind_fn_name("option_ce") equals `option_ce_bind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns bind name for option_ce")
expect(ce_bind_fn_name("option_ce")).to_equal("option_ce_bind")
```

</details>

#### returns bind name for seq_ce

- returns bind name for seq_ce
   - Expected: ce_bind_fn_name("seq_ce") equals `seq_ce_bind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns bind name for seq_ce")
expect(ce_bind_fn_name("seq_ce")).to_equal("seq_ce_bind")
```

</details>

#### returns bind name for arbitrary builder

- returns bind name for arbitrary builder
   - Expected: ce_bind_fn_name("my_ce") equals `my_ce_bind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns bind name for arbitrary builder")
expect(ce_bind_fn_name("my_ce")).to_equal("my_ce_bind")
```

</details>

#### bind name uses builder_bind pattern

- bind name uses builder_bind pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bind name uses builder_bind pattern")
val name = ce_bind_fn_name("foo_ce")
expect(name).to_end_with("_bind")
```

</details>

#### bind name starts with builder name

- bind name starts with builder name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bind name starts with builder name")
val name = ce_bind_fn_name("foo_ce")
expect(name).to_start_with("foo_ce")
```

</details>

### ce_return_fn_name

#### returns return name for result_ce

- returns return name for result_ce
   - Expected: ce_return_fn_name("result_ce") equals `result_ce_return`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns return name for result_ce")
expect(ce_return_fn_name("result_ce")).to_equal("result_ce_return")
```

</details>

#### returns return name for option_ce

- returns return name for option_ce
   - Expected: ce_return_fn_name("option_ce") equals `option_ce_return`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns return name for option_ce")
expect(ce_return_fn_name("option_ce")).to_equal("option_ce_return")
```

</details>

#### returns return name for seq_ce

- returns return name for seq_ce
   - Expected: ce_return_fn_name("seq_ce") equals `seq_ce_return`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns return name for seq_ce")
expect(ce_return_fn_name("seq_ce")).to_equal("seq_ce_return")
```

</details>

#### returns return name for arbitrary builder

- returns return name for arbitrary builder
   - Expected: ce_return_fn_name("my_ce") equals `my_ce_return`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns return name for arbitrary builder")
expect(ce_return_fn_name("my_ce")).to_equal("my_ce_return")
```

</details>

#### return name ends with _return

- return name ends with _return


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("return name ends with _return")
val name = ce_return_fn_name("foo_ce")
expect(name).to_end_with("_return")
```

</details>

#### return name starts with builder name

- return name starts with builder name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("return name starts with builder name")
val name = ce_return_fn_name("foo_ce")
expect(name).to_start_with("foo_ce")
```

</details>

### ce_zero_fn_name

#### returns zero name for result_ce

- returns zero name for result_ce
   - Expected: ce_zero_fn_name("result_ce") equals `result_ce_zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns zero name for result_ce")
expect(ce_zero_fn_name("result_ce")).to_equal("result_ce_zero")
```

</details>

#### returns zero name for option_ce

- returns zero name for option_ce
   - Expected: ce_zero_fn_name("option_ce") equals `option_ce_zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns zero name for option_ce")
expect(ce_zero_fn_name("option_ce")).to_equal("option_ce_zero")
```

</details>

#### returns zero name for seq_ce

- returns zero name for seq_ce
   - Expected: ce_zero_fn_name("seq_ce") equals `seq_ce_zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns zero name for seq_ce")
expect(ce_zero_fn_name("seq_ce")).to_equal("seq_ce_zero")
```

</details>

#### returns zero name for arbitrary builder

- returns zero name for arbitrary builder
   - Expected: ce_zero_fn_name("my_ce") equals `my_ce_zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns zero name for arbitrary builder")
expect(ce_zero_fn_name("my_ce")).to_equal("my_ce_zero")
```

</details>

#### zero name ends with _zero

- zero name ends with _zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero name ends with _zero")
val name = ce_zero_fn_name("foo_ce")
expect(name).to_end_with("_zero")
```

</details>

#### zero name starts with builder name

- zero name starts with builder name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero name starts with builder name")
val name = ce_zero_fn_name("foo_ce")
expect(name).to_start_with("foo_ce")
```

</details>

### naming convention consistency

#### all three names use the same prefix

- all three names use the same prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all three names use the same prefix")
val builder = "test_ce"
val bind_name = ce_bind_fn_name(builder)
val return_name = ce_return_fn_name(builder)
val zero_name = ce_zero_fn_name(builder)
expect(bind_name).to_start_with("test_ce")
```

</details>

#### bind and return names share builder prefix

- bind and return names share builder prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bind and return names share builder prefix")
val builder = "state_ce"
val bind_name = ce_bind_fn_name(builder)
val return_name = ce_return_fn_name(builder)
expect(bind_name).to_start_with("state_ce")
```

</details>

#### bind and zero names share builder prefix

- bind and zero names share builder prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bind and zero names share builder prefix")
val builder = "async_ce"
val bind_name = ce_bind_fn_name(builder)
val zero_name = ce_zero_fn_name(builder)
expect(zero_name).to_start_with("async_ce")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/computation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Computation Expression protocol, CE builder name constants, ce_builder_known, ce_bind_fn_name, ce_return_fn_name, ce_zero_fn_name, naming convention consistency.
- Computation Expression protocol
- CE builder name constants
- ce_builder_known
- ce_bind_fn_name
- ce_return_fn_name
- ce_zero_fn_name
- naming convention consistency

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
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

- Canonical SPipe generation for source `98e2bdce5a95aed12b1f8cd0228b1ae3244cac23df3e3a1fe91cfbeb727af21b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `98e2bdce5a95aed12b1f8cd0228b1ae3244cac23df3e3a1fe91cfbeb727af21b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `98e2bdce5a95aed12b1f8cd0228b1ae3244cac23df3e3a1fe91cfbeb727af21b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/computation_spec.spl
mirror: doc/06_spec/unit/lib/common/computation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/computation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/computation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/computation_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CE_BUILDER_RESULT is result_ce' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/computation_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CE_BUILDER_OPTION is option_ce' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/computation_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CE_BUILDER_SEQ is seq_ce' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
