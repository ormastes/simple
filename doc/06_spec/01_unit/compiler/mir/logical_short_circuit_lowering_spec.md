# logical_short_circuit_lowering_spec

> Purpose: Prove that MIR logical short-circuit lowering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# logical_short_circuit_lowering_spec

Purpose: Prove that MIR logical short-circuit lowering.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/logical_short_circuit_lowering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that MIR logical short-circuit lowering.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### MIR logical short-circuit lowering

#### branches to the RHS only when an and-left value is true

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- branches to the RHS only when an and-left value is true
- Verify: branches to the RHS only when an and-left value is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("branches to the RHS only when an and-left value is true")
step("Verify: branches to the RHS only when an and-left value is true")
# @req: REQ-COMPILER-MIR-001
val mir = lower_logic_function("flag and rhs()")
expect_conditional_rhs(mir)
expect(mir).to_contain("\"then\":1,\"else\":2")
```

</details>

#### branches to the RHS only when an or-left value is false

- branches to the RHS only when an or-left value is false
- Verify: branches to the RHS only when an or-left value is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("branches to the RHS only when an or-left value is false")
step("Verify: branches to the RHS only when an or-left value is false")
val mir = lower_logic_function("flag or rhs()")
expect_conditional_rhs(mir)
expect(mir).to_contain("\"then\":2,\"else\":1")
```

</details>

#### uses independent slots for nested short-circuit expressions

- uses independent slots for nested short-circuit expressions
- Verify: uses independent slots for nested short-circuit expressions
   - Expected: mir.split("\"Alloc\"").len() equals `3`
   - Expected: mir.split("\"Store\"").len() equals `5`
   - Expected: mir.split("\"Load\"").len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses independent slots for nested short-circuit expressions")
step("Verify: uses independent slots for nested short-circuit expressions")
val mir = lower_logic_function("flag and (other or rhs())")
expect(mir.split("\"Alloc\"").len()).to_equal(3)
expect(mir.split("\"Store\"").len()).to_equal(5)
expect(mir.split("\"Load\"").len()).to_equal(3)
```

</details>

<details>
<summary>Advanced: hoists a loop-body logical merge slot to function entry</summary>

#### hoists a loop-body logical merge slot to function entry

- hoists a loop-body logical merge slot to function entry
- Verify: hoists a loop-body logical merge slot to function entry
   - Expected: mir.split("\"Alloc\"").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("hoists a loop-body logical merge slot to function entry")
step("Verify: hoists a loop-body logical merge slot to function entry")
val src = "fn rhs() -> bool:\n    true\n\nfn check(flag: bool) -> bool:\n    var result = false\n    while flag:\n        result = flag and rhs()\n        break\n    result\n"
val mir = lower_source_function(src, "check")
val alloc_pos = mir.index_of("\"Alloc\"")
val cond_pos = mir.index_of("\"label\":\"while_cond\"")
val body_pos = mir.index_of("\"label\":\"while_body\"")
expect(alloc_pos).to_be_greater_than(-1)
expect(cond_pos).to_be_greater_than(alloc_pos)
expect(body_pos).to_be_greater_than(cond_pos)
expect(mir.split("\"Alloc\"").len()).to_equal(2)
```

</details>


</details>

### MIR block terminator lowering

#### lowers a bare return without an optional payload crash

- lowers a bare return without an optional payload crash
- Verify: lowers a bare return without an optional payload crash


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers a bare return without an optional payload crash")
step("Verify: lowers a bare return without an optional payload crash")
val mir = lower_source_function("fn stop():\n    return\n", "stop")

expect(mir).to_contain("\"terminator\":{\"Return\":null}")
```

</details>

#### does not lower a Dict traversal after return

- does not lower a Dict traversal after return
- Verify: does not lower a Dict traversal after return
   - Expected: mir does not contain `rt_dict_values`
   - Expected: mir does not contain `Map.values`
   - Expected: mir does not contain `Dict.values`
   - Expected: mir does not contain `MethodCallStatic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not lower a Dict traversal after return")
step("Verify: does not lower a Dict traversal after return")
val source = "fn check(values: Dict<text, i64>) -> i64:\n    return 7\n    values.values()\n"
val mir = lower_source_function(source, "check")

expect(mir).to_contain("\"terminator\":{\"Return\":{\"Copy\"")
expect(mir).to_contain("\"value\":7")
expect(mir.contains("rt_dict_values")).to_equal(false)
expect(mir.contains("Map.values")).to_equal(false)
expect(mir.contains("Dict.values")).to_equal(false)
expect(mir.contains("MethodCallStatic")).to_equal(false)
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

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-MIR-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `40dec4562f886fac833fca59e416776c7d741256072190c4cca1e81edb720a68`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `40dec4562f886fac833fca59e416776c7d741256072190c4cca1e81edb720a68`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `40dec4562f886fac833fca59e416776c7d741256072190c4cca1e81edb720a68`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/mir/logical_short_circuit_lowering_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/logical_short_circuit_lowering_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/logical_short_circuit_lowering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/logical_short_circuit_lowering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/logical_short_circuit_lowering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/logical_short_circuit_lowering_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'branches to the RHS only when an and-left value is true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/logical_short_circuit_lowering_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'branches to the RHS only when an or-left value is false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/logical_short_circuit_lowering_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses independent slots for nested short-circuit expressions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
