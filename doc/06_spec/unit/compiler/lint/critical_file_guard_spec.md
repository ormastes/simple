# critical_file_guard_spec

> Purpose and audience: owning engineering team verifying Critical file guard lint.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# critical_file_guard_spec

Purpose and audience: owning engineering team verifying Critical file guard lint.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/lint/critical_file_guard_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose and audience: owning engineering team verifying Critical file guard lint.

## Scenarios

### Critical file guard lint

#### config/critical_files.sdn exists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- config/critical_files.sdn exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("config/critical_files.sdn exists")
assert_equal(expect(file_exists("config/critical_files.sdn")), true)
```

</details>

#### config has entries section

- config has entries section


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("config has entries section")
val content = read_file("config/critical_files.sdn")
assert_contains(content, "entries:")
```

</details>

#### config protects star_import.spl

- config protects star_import.spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("config protects star_import.spl")
val content = read_file("config/critical_files.sdn")
assert_contains(content, "src/compiler/35.semantics/lint/star_import.spl")
```

</details>

#### config protects error.spl

- config protects error.spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("config protects error.spl")
val content = read_file("config/critical_files.sdn")
assert_contains(content, "src/compiler/00.common/error.spl")
```

</details>

#### config protects itself

- config protects itself


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("config protects itself")
val content = read_file("config/critical_files.sdn")
assert_contains(content, "config/critical_files.sdn")
```

</details>

#### guard module has CFG001 deletion check

- guard module has CFG001 deletion check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guard module has CFG001 deletion check")
val source = read_file("src/compiler/35.semantics/lint/critical_file_guard.spl")
assert_contains(source, "\"CFG001\"")
assert_contains(source, "critical file deleted")
```

</details>

#### guard module has CFG002 shrinkage check

- guard module has CFG002 shrinkage check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guard module has CFG002 shrinkage check")
val source = read_file("src/compiler/35.semantics/lint/critical_file_guard.spl")
assert_contains(source, "\"CFG002\"")
assert_contains(source, "shrunk below")
```

</details>

#### guard is registered in __init__.spl

- guard is registered in __init__.spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guard is registered in __init__.spl")
val source = read_file("src/compiler/35.semantics/lint/__init__.spl")
assert_contains(source, "export critical_file_guard.*")
```

</details>

#### guard is integrated in query_lint.spl

- guard is integrated in query_lint.spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("guard is integrated in query_lint.spl")
val source = read_file("src/app/cli/query_lint.spl")
assert_contains(source, "check_all_critical_files")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `c7d0e15202b5c20096d73db51aa008b328619f2b7029bcb0d1710155f1c36dc6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c7d0e15202b5c20096d73db51aa008b328619f2b7029bcb0d1710155f1c36dc6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c7d0e15202b5c20096d73db51aa008b328619f2b7029bcb0d1710155f1c36dc6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/lint/critical_file_guard_spec.spl
mirror: doc/06_spec/unit/compiler/lint/critical_file_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/lint/critical_file_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/lint/critical_file_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/lint/critical_file_guard_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'config/critical_files.sdn exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/lint/critical_file_guard_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'config has entries section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/lint/critical_file_guard_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'config protects star_import.spl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
