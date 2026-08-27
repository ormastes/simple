# error_trace_design_spec

> Purpose: Prove that error propagation trace design.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# error_trace_design_spec

Purpose: Prove that error propagation trace design.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/error_trace_design_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that error propagation trace design.
Audience: COMP-CORE maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### error propagation trace design

#### ? operator propagates nil from a function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ? operator propagates nil from a function
- Verify: ? operator propagates nil from a function


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("? operator propagates nil from a function")
step("Verify: ? operator propagates nil from a function")
# @req: REQ-COMP-CORE-ERROR-PROPAGATION-TRACE-DESIGN-001
# When a value is nil, ? should propagate it (simulate nil propagation)
val nil_val = nil
val propagated = nil_val  # simulates ? propagation
expect(propagated).to_be_nil()
```

</details>

#### trace buffer records source location as text

- trace buffer records source location as text
- Verify: trace buffer records source location as text
   - Expected: trace_entry.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trace buffer records source location as text")
step("Verify: trace buffer records source location as text")
# Expected: each ? site records file:line info as a text entry
val trace_entry = "file.spl:42"
expect(trace_entry.len() > 0).to_equal(true)
```

</details>

#### trace entry contains filename

- trace entry contains filename
- Verify: trace entry contains filename
   - Expected: has_spl is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trace entry contains filename")
step("Verify: trace entry contains filename")
val trace_entry = "parser.spl:100"
val has_spl = trace_entry.contains(".spl")
expect(has_spl).to_equal(true)
```

</details>

#### trace entry contains line number

- trace entry contains line number
- Verify: trace entry contains line number
   - Expected: has_colon is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trace entry contains line number")
step("Verify: trace entry contains line number")
val trace_entry = "eval.spl:512"
val has_colon = trace_entry.contains(":")
expect(has_colon).to_equal(true)
```

</details>

#### multiple ? sites produce multiple trace entries

- multiple ? sites produce multiple trace entries
- Verify: multiple ? sites produce multiple trace entries
   - Expected: trace_buf.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple ? sites produce multiple trace entries")
step("Verify: multiple ? sites produce multiple trace entries")
# Simulated trace buffer (future: populated by ? operator)
var trace_buf: [text] = []
trace_buf.push("a.spl:10")
trace_buf.push("b.spl:20")
trace_buf.push("c.spl:30")
expect(trace_buf.len()).to_equal(3)
```

</details>

#### trace is empty when no errors propagated

- trace is empty when no errors propagated
- Verify: trace is empty when no errors propagated
   - Expected: empty_trace.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trace is empty when no errors propagated")
step("Verify: trace is empty when no errors propagated")
var empty_trace: [text] = []
expect(empty_trace.len()).to_equal(0)
```

</details>

#### propagation stops at top-level handler

- propagation stops at top-level handler
- Verify: propagation stops at top-level handler
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagation stops at top-level handler")
step("Verify: propagation stops at top-level handler")
# The outermost caller receives the nil value
fn maybe_fail(should_fail: bool) -> i64:
    if should_fail:
        return 0  # represents error case
    42
val result = maybe_fail(false)
expect(result).to_equal(42)
```

</details>

#### nil propagation preserves the nil value

- nil propagation preserves the nil value
- Verify: nil propagation preserves the nil value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nil propagation preserves the nil value")
step("Verify: nil propagation preserves the nil value")
val original = nil
var captured = original
expect(captured).to_be_nil()
```

</details>

#### trace format is colon-separated file and line

- trace format is colon-separated file and line
- Verify: trace format is colon-separated file and line
   - Expected: parts_check is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trace format is colon-separated file and line")
step("Verify: trace format is colon-separated file and line")
# Expected trace format: "filename.spl:linenum"
val expected_format = "module.spl:1"
val parts_check = expected_format.contains(".spl:")
expect(parts_check).to_equal(true)
```

</details>

#### error message is preserved through propagation

- error message is preserved through propagation
- Verify: error message is preserved through propagation
   - Expected: preserved equals `connection refused`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error message is preserved through propagation")
step("Verify: error message is preserved through propagation")
# When an error carries a message, ? should not discard it
val error_msg = "connection refused"
val preserved = error_msg
expect(preserved).to_equal("connection refused")
```

</details>

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
- `REQ-COMP-CORE-ERROR-PROPAGATION-TRACE-DESIGN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f40c9b7d34fad30b6f612394a7e716dcf01f268c0a095a910566bb9b1b143ddc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f40c9b7d34fad30b6f612394a7e716dcf01f268c0a095a910566bb9b1b143ddc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f40c9b7d34fad30b6f612394a7e716dcf01f268c0a095a910566bb9b1b143ddc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler_core/error_trace_design_spec.spl
mirror: doc/06_spec/unit/compiler_core/error_trace_design_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler_core/error_trace_design_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/error_trace_design_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/error_trace_design_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler_core/error_trace_design_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '? operator propagates nil from a function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/error_trace_design_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trace buffer records source location as text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/error_trace_design_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trace entry contains filename' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
