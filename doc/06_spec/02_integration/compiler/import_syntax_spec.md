# import_syntax_spec

> Verifies the import syntax behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# import_syntax_spec

Verifies the import syntax behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/import_syntax_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the import syntax behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Import Syntax for mod.spl Files

#### Curly braces syntax: use app.io.{...}

#### imports env_get with curly braces

- Verify: imports env_get with curly braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_IMPORT_SYNTAX-001
step("Verify: imports env_get with curly braces")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = env_get("PATH")
expect result.len() > 0
```

</details>

#### imports env_set with curly braces

- Verify: imports env_set with curly braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_IMPORT_SYNTAX-001
step("Verify: imports env_set with curly braces")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = env_set("TEST_VAR_CURLY", "test")
expect result == true
```

</details>

#### imports shell with curly braces

- Verify: imports shell with curly braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_IMPORT_SYNTAX-001
step("Verify: imports shell with curly braces")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = shell("echo test")
expect result.exit_code == 0
```

</details>

#### Parentheses syntax: use app.io.mod (...)

#### imports file_exists with parentheses

- Verify: imports file_exists with parentheses


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_IMPORT_SYNTAX-001
step("Verify: imports file_exists with parentheses")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = file_exists("test/02_integration/compiler/import_syntax_spec.spl")
expect result == true
```

</details>

#### imports cwd with parentheses

- Verify: imports cwd with parentheses


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COMPILER-COMPILER_IMPORT_SYNTAX-001
step("Verify: imports cwd with parentheses")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val result = cwd()
expect result.len() > 0
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `78642271f1ee47a22678a1076c36b8ba993853f4acf9d3eb98df569e51ab54f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `78642271f1ee47a22678a1076c36b8ba993853f4acf9d3eb98df569e51ab54f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `78642271f1ee47a22678a1076c36b8ba993853f4acf9d3eb98df569e51ab54f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/compiler/import_syntax_spec.spl
mirror: doc/06_spec/02_integration/compiler/import_syntax_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/compiler/import_syntax_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/compiler/import_syntax_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/compiler/import_syntax_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
