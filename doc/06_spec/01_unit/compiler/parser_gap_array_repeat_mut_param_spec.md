# Parser Gap: Array-Repeat Expression + `mut` Parameters

> Closes two grammar-surface gaps the self-hosted `parse_full_frontend` rejected but the interpreter accepts:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Gap: Array-Repeat Expression + `mut` Parameters

Closes two grammar-surface gaps the self-hosted `parse_full_frontend` rejected but the interpreter accepts:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-GAP-A1, #PARSER-GAP-A2 |
| Category | Syntax / Self-hosted frontend parity |
| Status | In Progress |
| Plan | doc/03_plan/compiler/self_hosted_frontend/full_cli_redeploy_and_browser_startup_plan.md (Track A) |
| Design | doc/05_design/compiler/parsing/frontend_parser_gaps_and_lazy_closure_design.md |
| Source | `test/01_unit/compiler/parser_gap_array_repeat_mut_param_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Closes two grammar-surface gaps the self-hosted `parse_full_frontend` rejected
but the interpreter accepts:

- **A1 — array-repeat expression `[value; count]`** (count may be non-literal).
- **A2 — `mut` parameters** (`fn f(mut buf: [u8], ...)`).

If the module-level declarations below parse, the self-hosted parser accepts the
grammar (parse errors = file won't load at all). The `it` blocks assert the
constructs also *evaluate* identically under the interpreter (behavior parity).

## Syntax

```simple
var buf: [i32] = [0; 12]          # literal count
var b2: [i32]  = [7; n]           # runtime count
use std.spec.step

fn pack(mut buf: [i32], v: i32) -> i32:
    buf[0] = v
    buf[0]
```

## Scenarios

### parser gap A1: array-repeat expression

#### evaluation parity under the interpreter

#### builds a literal-count array of the right length

- builds a literal-count array of the right length


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a literal-count array of the right length")
assert_equal(ar_literal_u8(), 12)
```

</details>

#### builds a runtime-count array of the right length

- builds a runtime-count array of the right length


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a runtime-count array of the right length")
assert_equal(ar_runtime_count(5), 5)
```

</details>

#### fills every slot with the repeated value

- fills every slot with the repeated value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fills every slot with the repeated value")
assert_equal(ar_value_readback(), 18)
```

</details>

#### accepts a compound count expression

- accepts a compound count expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a compound count expression")
assert_equal(ar_expr_count(3), 5)
```

</details>

### parser gap A2: mut parameters

#### evaluation parity under the interpreter

#### accepts and mutates a leading mut param

- accepts and mutates a leading mut param


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts and mutates a leading mut param")
var buf: [i32] = [0; 3]
assert_equal(mp_pack_first(buf, 42), 42)
```

</details>

#### accepts a mut param after a plain param

- accepts a mut param after a plain param


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a mut param after a plain param")
var buf: [i32] = [0; 4]
assert_equal(mp_pack_middle(2, buf, 8), 8)
```

</details>

#### accepts multiple mut params

- accepts multiple mut params


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts multiple mut params")
var a: [i32] = [0; 2]
var b: [i32] = [0; 2]
assert_equal(mp_two_mut(a, b), 7)
```

</details>

#### accepts and preserves mut params on impl methods

- accepts and preserves mut params on impl methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts and preserves mut params on impl methods")
val probe = MutMethodProbe(marker: 2)
var buf: [i32] = [0; 3]
assert_equal(probe.write(1, buf, 11), 13)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/compiler/self_hosted_frontend/full_cli_redeploy_and_browser_startup_plan.md (Track A)`
- **Design:** `doc/05_design/compiler/parsing/frontend_parser_gaps_and_lazy_closure_design.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fd5e4b07e0b3c156f55c4d61719bf2fd1a051c426a46b00fd38ac3f26eed3156`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd5e4b07e0b3c156f55c4d61719bf2fd1a051c426a46b00fd38ac3f26eed3156`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd5e4b07e0b3c156f55c4d61719bf2fd1a051c426a46b00fd38ac3f26eed3156`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser_gap_array_repeat_mut_param_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser_gap_array_repeat_mut_param_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser_gap_array_repeat_mut_param_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser_gap_array_repeat_mut_param_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser_gap_array_repeat_mut_param_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a literal-count array of the right length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_gap_array_repeat_mut_param_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a runtime-count array of the right length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser_gap_array_repeat_mut_param_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fills every slot with the repeated value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
