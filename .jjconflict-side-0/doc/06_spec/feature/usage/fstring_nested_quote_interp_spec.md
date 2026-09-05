# F-String Nested Quote Interpolation Regression Specification

> A seed-lexer regression made a nested string literal inside f-string interpolation terminate the OUTER string: `"j={xs.join("-")}"` silently miscompiled (printed garbage like `-35948`) or parse-failed (`expected Comma, found FString(...)` / `expected Colon, found RBrace`) depending on surrounding tokens. The fix restores quote toggling inside `{...}` and contains runaway unmatched braces via a newline guard instead.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# F-String Nested Quote Interpolation Regression Specification

A seed-lexer regression made a nested string literal inside f-string interpolation terminate the OUTER string: `"j={xs.join("-")}"` silently miscompiled (printed garbage like `-35948`) or parse-failed (`expected Comma, found FString(...)` / `expected Colon, found RBrace`) depending on surrounding tokens. The fix restores quote toggling inside `{...}` and contains runaway unmatched braces via a newline guard instead.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | Fixed (310bcdf1131, parser/src/lexer/strings.rs) |
| Source | `test/feature/usage/fstring_nested_quote_interp_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

A seed-lexer regression made a nested string literal inside f-string
interpolation terminate the OUTER string: `"j={xs.join("-")}"` silently
miscompiled (printed garbage like `-35948`) or parse-failed
(`expected Comma, found FString(...)` / `expected Colon, found RBrace`)
depending on surrounding tokens. The fix restores quote toggling inside
`{...}` and contains runaway unmatched braces via a newline guard instead.

## Scenarios

### F-String Nested Quote Interpolation

#### joins list with a quoted separator inside interpolation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- joins list with a quoted separator inside interpolation
   - Expected: result equals `j=a-b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins list with a quoted separator inside interpolation")
val xs = ["a", "b"]
val result = "j={xs.join("-")}"
expect(result).to_equal("j=a-b")
```

</details>

#### joins with an underscore separator inside interpolation

- joins with an underscore separator inside interpolation
   - Expected: result equals `items=x_y_z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("joins with an underscore separator inside interpolation")
val items = ["x", "y", "z"]
val result = "items={items.join("_")}"
expect(result).to_equal("items=x_y_z")
```

</details>

#### handles a nested template literal with inner interpolation

- handles a nested template literal with inner interpolation
   - Expected: result equals `s_a_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles a nested template literal with inner interpolation")
# Shape that parse-broke spirv_builder.spl:234
val xs = ["a", "b"]
val result = "s_{xs.map("{_}").join("_")}"
expect(result).to_equal("s_a_b")
```

</details>

#### keeps surrounding literal text intact around the nested call

- keeps surrounding literal text intact around the nested call
   - Expected: result equals `prefix_hello-world_suffix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("keeps surrounding literal text intact around the nested call")
val data = ["hello", "world"]
val result = "prefix_{data.join("-")}_suffix"
expect(result).to_equal("prefix_hello-world_suffix")
```

</details>

#### does not silently corrupt output (was numeric garbage pre-fix)

- does not silently corrupt output (was numeric garbage pre-fix)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does not silently corrupt output (was numeric garbage pre-fix)")
val list = ["m", "n"]
val output = "m={list.join("-")}"
assert_true(output == "m=m-n")
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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `36fa508fb127e570fe97a130a988c14e8511548a4d0765a541eb2aa4c59e93eb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `36fa508fb127e570fe97a130a988c14e8511548a4d0765a541eb2aa4c59e93eb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `36fa508fb127e570fe97a130a988c14e8511548a4d0765a541eb2aa4c59e93eb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/fstring_nested_quote_interp_spec.spl
mirror: doc/06_spec/feature/usage/fstring_nested_quote_interp_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/fstring_nested_quote_interp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/fstring_nested_quote_interp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/fstring_nested_quote_interp_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'joins list with a quoted separator inside interpolation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/fstring_nested_quote_interp_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'joins with an underscore separator inside interpolation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/fstring_nested_quote_interp_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles a nested template literal with inner interpolation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
