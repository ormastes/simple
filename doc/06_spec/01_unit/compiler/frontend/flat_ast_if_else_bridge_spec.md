# flat_ast_if_else_bridge_spec

> Purpose: Prove that Flat AST bridge if/else fidelity (M12 item 6).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# flat_ast_if_else_bridge_spec

Purpose: Prove that Flat AST bridge if/else fidelity (M12 item 6).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/flat_ast_if_else_bridge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Flat AST bridge if/else fidelity (M12 item 6).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Flat AST bridge if/else fidelity (M12 item 6)

#### attaches the else block for if/else

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- attaches the else block for if/else
- Verify: attaches the else block for if/else
   - Expected: if_else_else_count(src, "f") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("attaches the else block for if/else")
step("Verify: attaches the else block for if/else")
# @req: REQ-COMPILER-FRONTEND-001
val src = "fn f(n: i64) -> i64:\n    if n > 0:\n        return 1\n    else:\n        return 2\n"
expect(if_else_else_count(src, "f")).to_equal(1)
```

</details>

#### leaves else nil for a plain if (no spurious empty else block)

- leaves else nil for a plain if (no spurious empty else block)
- Verify: leaves else nil for a plain if (no spurious empty else block)
   - Expected: if_else_else_count(src, "g") equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves else nil for a plain if (no spurious empty else block)")
step("Verify: leaves else nil for a plain if (no spurious empty else block)")
val src = "fn g(n: i64) -> i64:\n    if n > 0:\n        return 1\n    return 0\n"
expect(if_else_else_count(src, "g")).to_equal(-2)
```

</details>

#### attaches the else chain for if/elif/else

- attaches the else chain for if/elif/else
- Verify: attaches the else chain for if/elif/else
   - Expected: if_else_else_count(src, "h") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("attaches the else chain for if/elif/else")
step("Verify: attaches the else chain for if/elif/else")
val src = "fn h(n: i64) -> i64:\n    if n > 90:\n        return 1\n    elif n > 50:\n        return 2\n    else:\n        return 3\n"
expect(if_else_else_count(src, "h")).to_equal(1)
```

</details>

#### preserves every link in a long elif chain and its terminal else

- preserves every link in a long elif chain and its terminal else
- Verify: preserves every link in a long elif chain and its terminal else
   - Expected: parsed_if_chain_depth(src, "long_chain") equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves every link in a long elif chain and its terminal else")
step("Verify: preserves every link in a long elif chain and its terminal else")
val src = long_elif_source(128)
expect(parsed_if_chain_depth(src, "long_chain")).to_equal(128)
```

</details>

#### preserves every value-position arm in a long elif chain

- preserves every value-position arm in a long elif chain
- Verify: preserves every value-position arm in a long elif chain
   - Expected: parsed_value_if_chain_depth(src, "long_value_chain") equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves every value-position arm in a long elif chain")
step("Verify: preserves every value-position arm in a long elif chain")
val src = long_value_elif_source(128)
expect(parsed_value_if_chain_depth(src, "long_value_chain")).to_equal(128)
```

</details>

#### executes selected arms in order and short-circuits later conditions

- executes selected arms in order and short-circuits later conditions
- Verify: executes selected arms in order and short-circuits later conditions
   - Expected: executable_if_chain(1) equals `20`
   - Expected: if_chain_probe_calls equals `2`
   - Expected: executable_if_chain(9) equals `30`
   - Expected: if_chain_probe_calls equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("executes selected arms in order and short-circuits later conditions")
step("Verify: executes selected arms in order and short-circuits later conditions")
if_chain_probe_calls = 0
expect(executable_if_chain(1)).to_equal(20)  # oracle: 20 — named expected value from the requirement
expect(if_chain_probe_calls).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(executable_if_chain(9)).to_equal(30)  # oracle: 30 — named expected value from the requirement
expect(if_chain_probe_calls).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### preserves no-else and terminal-else results

- preserves no-else and terminal-else results
- Verify: preserves no-else and terminal-else results
   - Expected: executable_if_chain_no_else(0) equals `10`
   - Expected: executable_if_chain_no_else(9) equals `7`
   - Expected: executable_if_chain(9) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves no-else and terminal-else results")
step("Verify: preserves no-else and terminal-else results")
expect(executable_if_chain_no_else(0)).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(executable_if_chain_no_else(9)).to_equal(7)  # oracle: 7 — named expected value from the requirement
expect(executable_if_chain(9)).to_equal(30)  # oracle: 30 — named expected value from the requirement
```

</details>

#### preserves if-val narrowing across elif arms

- preserves if-val narrowing across elif arms
- Verify: preserves if-val narrowing across elif arms
   - Expected: executable_if_val_chain(nil, 42) equals `42`
   - Expected: executable_if_val_chain(7, 42) equals `7`
   - Expected: executable_if_val_chain(nil, nil) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves if-val narrowing across elif arms")
step("Verify: preserves if-val narrowing across elif arms")
expect(executable_if_val_chain(nil, 42)).to_equal(42)  # oracle: 42 — named expected value from the requirement
expect(executable_if_val_chain(7, 42)).to_equal(7)  # oracle: 7 — named expected value from the requirement
expect(executable_if_val_chain(nil, nil)).to_equal(-1)  # oracle: -1 — named expected value from the requirement
```

</details>

#### preserves mixed constructor and identifier if-val arms

- preserves mixed constructor and identifier if-val arms
- Verify: preserves mixed constructor and identifier if-val arms
   - Expected: executable_mixed_if_val_chain(7, 42) equals `7`
   - Expected: executable_mixed_if_val_chain(nil, 42) equals `42`
   - Expected: executable_mixed_if_val_chain(nil, nil) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves mixed constructor and identifier if-val arms")
step("Verify: preserves mixed constructor and identifier if-val arms")
expect(executable_mixed_if_val_chain(7, 42)).to_equal(7)  # oracle: 7 — named expected value from the requirement
expect(executable_mixed_if_val_chain(nil, 42)).to_equal(42)  # oracle: 42 — named expected value from the requirement
expect(executable_mixed_if_val_chain(nil, nil)).to_equal(-1)  # oracle: -1 — named expected value from the requirement
```

</details>

#### preserves else-if spelling

- preserves else-if spelling
- Verify: preserves else-if spelling
   - Expected: executable_else_if_chain(0) equals `10`
   - Expected: executable_else_if_chain(1) equals `20`
   - Expected: executable_else_if_chain(9) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves else-if spelling")
step("Verify: preserves else-if spelling")
expect(executable_else_if_chain(0)).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(executable_else_if_chain(1)).to_equal(20)  # oracle: 20 — named expected value from the requirement
expect(executable_else_if_chain(9)).to_equal(30)  # oracle: 30 — named expected value from the requirement
```

</details>

#### merges value-position expression arms

- merges value-position expression arms
- Verify: merges value-position expression arms
   - Expected: value_position_if_chain(0) equals `10`
   - Expected: value_position_if_chain(1) equals `20`
   - Expected: value_position_if_chain(9) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("merges value-position expression arms")
step("Verify: merges value-position expression arms")
expect(value_position_if_chain(0)).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(value_position_if_chain(1)).to_equal(20)  # oracle: 20 — named expected value from the requirement
expect(value_position_if_chain(9)).to_equal(30)  # oracle: 30 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-FRONTEND-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `083850a18f584c050bef792d3869b6417850d6fe64880f1ad99f586b411eb0af`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `083850a18f584c050bef792d3869b6417850d6fe64880f1ad99f586b411eb0af`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `083850a18f584c050bef792d3869b6417850d6fe64880f1ad99f586b411eb0af`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/frontend/flat_ast_if_else_bridge_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/flat_ast_if_else_bridge_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/flat_ast_if_else_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/flat_ast_if_else_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/flat_ast_if_else_bridge_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/flat_ast_if_else_bridge_spec.spl:167:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'attaches the else block for if/else' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/flat_ast_if_else_bridge_spec.spl:175:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves else nil for a plain if (no spurious empty else block)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/flat_ast_if_else_bridge_spec.spl:182:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'attaches the else chain for if/elif/else' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
