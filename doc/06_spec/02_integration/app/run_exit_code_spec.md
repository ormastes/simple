# `simple run` main() exit-code propagation (task #90)

> Purpose: This spec proves simple run propagates main() return value as process exit code.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `simple run` main() exit-code propagation (task #90)

Purpose: This spec proves simple run propagates main() return value as process exit code.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/run_exit_code_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves simple run propagates main() return value as process exit code.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### simple run propagates main() return value as process exit code

#### trailing expression: fn main() -> i32 returning 1 exits 1

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- trailing expression: fn main() -> i32 returning 1 exits 1
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RUNEXITCODE-001
step("trailing expression: fn main() -> i32 returning 1 exits 1")
val (out, err, code) = _run_script("fn main() -> i32:\\n    print(\\\"x\\\")\\n    1\\n")
expect(code).to_equal(1)
expect(out).to_contain("x")
```

</details>

#### explicit return: fn main() -> i32 with return 1 exits 1

- explicit return: fn main() -> i32 with return 1 exits 1
- explicit return: fn main() -> i32 with return 1 exits 1
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("explicit return: fn main() -> i32 with return 1 exits 1")
step("explicit return: fn main() -> i32 with return 1 exits 1")
val (out, err, code) = _run_script("fn main() -> i32:\\n    print(\\\"x\\\")\\n    return 1\\n")
expect(code).to_equal(1)
expect(out).to_contain("x")
```

</details>

#### fn main() -> int with return 1 exits 1

- fn main() -> int with return 1 exits 1
- fn main() -> int with return 1 exits 1
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fn main() -> int with return 1 exits 1")
step("fn main() -> int with return 1 exits 1")
val (out, err, code) = _run_script("fn main() -> int:\\n    print(\\\"x\\\")\\n    return 1\\n")
expect(code).to_equal(1)
expect(out).to_contain("x")
```

</details>

#### fn main() -> i32 returning 0 exits 0

- fn main() -> i32 returning 0 exits 0
- fn main() -> i32 returning 0 exits 0
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fn main() -> i32 returning 0 exits 0")
step("fn main() -> i32 returning 0 exits 0")
val (out, err, code) = _run_script("fn main() -> i32:\\n    print(\\\"ok\\\")\\n    0\\n")
expect(code).to_equal(0)
expect(out).to_contain("ok")
```

</details>

#### fn main() -> i32 returning a non-trivial value (42) exits 42

- fn main() -> i32 returning a non-trivial value (42) exits 42
- fn main() -> i32 returning a non-trivial value (42) exits 42
   - Expected: code equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fn main() -> i32 returning a non-trivial value (42) exits 42")
step("fn main() -> i32 returning a non-trivial value (42) exits 42")
val (out, err, code) = _run_script("fn main() -> i32:\\n    print(\\\"forty-two\\\")\\n    42\\n")
expect(code).to_equal(42)
```

</details>

#### unit-returning fn main() keeps the success exit code (0)

- unit-returning fn main() keeps the success exit code (0)
- unit-returning fn main() keeps the success exit code (0)
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("unit-returning fn main() keeps the success exit code (0)")
step("unit-returning fn main() keeps the success exit code (0)")
val (out, err, code) = _run_script("fn main():\\n    print(\\\"unit-main\\\")\\n")
expect(code).to_equal(0)
expect(out).to_contain("unit-main")
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

- `REQ-SSPEC-INTEGRATION`
- `REQ-RUNEXITCODE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8ea1d9955253dbcc049b04e65c8834d2d54d0b4d92ec9e0168205796834f1ea8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8ea1d9955253dbcc049b04e65c8834d2d54d0b4d92ec9e0168205796834f1ea8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8ea1d9955253dbcc049b04e65c8834d2d54d0b4d92ec9e0168205796834f1ea8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/app/run_exit_code_spec.spl
mirror: doc/06_spec/02_integration/app/run_exit_code_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/run_exit_code_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/run_exit_code_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/run_exit_code_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/run_exit_code_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trailing expression: fn main() -> i32 returning 1 exits 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/run_exit_code_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'explicit return: fn main() -> i32 with return 1 exits 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/run_exit_code_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fn main() -> int with return 1 exits 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
