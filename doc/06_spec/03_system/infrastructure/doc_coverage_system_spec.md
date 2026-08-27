# Doc Coverage System Specification

> Tests covering doc-coverage CLI - terminal mode, doc-coverage CLI - JSON mode, doc-coverage CLI - Markdown mode, doc-coverage CLI - missing flag, doc-coverage CLI - path scoping, stats command coverage integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Doc Coverage System Specification

## Scenarios

### doc-coverage CLI - terminal mode

<details>
<summary>Advanced: doc-coverage exits with 0</summary>

#### doc-coverage exits with 0 _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- doc-coverage exits with 0
   - Expected: exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage exits with 0")
val result = run_simple(["doc-coverage"])
val exit_code = result.2
expect(exit_code).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage shows coverage report header</summary>

#### doc-coverage shows coverage report header _(slow)_

- doc-coverage shows coverage report header
   - Expected: stdout contains `Coverage Report`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage shows coverage report header")
val result = run_simple(["doc-coverage"])
val stdout = result.0
expect(stdout.contains("Coverage Report")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage shows non-zero public function count</summary>

#### doc-coverage shows non-zero public function count _(slow)_

- doc-coverage shows non-zero public function count
   - Expected: stdout contains `Public Functions:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage shows non-zero public function count")
val result = run_simple(["doc-coverage"])
val stdout = result.0
expect(stdout.contains("Public Functions:")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage shows per-scope breakdown</summary>

#### doc-coverage shows per-scope breakdown _(slow)_

- doc-coverage shows per-scope breakdown
   - Expected: stdout contains `Per-Scope Breakdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage shows per-scope breakdown")
val result = run_simple(["doc-coverage"])
val stdout = result.0
expect(stdout.contains("Per-Scope Breakdown")).to_equal(true)
```

</details>


</details>

### doc-coverage CLI - JSON mode

<details>
<summary>Advanced: doc-coverage --format=json exits with 0</summary>

#### doc-coverage --format=json exits with 0 _(slow)_

- doc-coverage --format=json exits with 0
   - Expected: exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage --format=json exits with 0")
val result = run_simple(["doc-coverage", "--format=json"])
val exit_code = result.2
expect(exit_code).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage --format=json outputs JSON</summary>

#### doc-coverage --format=json outputs JSON _(slow)_

- doc-coverage --format=json outputs JSON
   - Expected: stdout.starts_with("{") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage --format=json outputs JSON")
val result = run_simple(["doc-coverage", "--format=json"])
val stdout = result.0
expect(stdout.starts_with("{")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage --format=json has total_public field</summary>

#### doc-coverage --format=json has total_public field _(slow)_

- doc-coverage --format=json has total_public field
   - Expected: stdout contains `"total_public"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage --format=json has total_public field")
val result = run_simple(["doc-coverage", "--format=json"])
val stdout = result.0
expect(stdout.contains("\"total_public\"")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage --format=json has per_scope field</summary>

#### doc-coverage --format=json has per_scope field _(slow)_

- doc-coverage --format=json has per_scope field
   - Expected: stdout contains `"per_scope"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage --format=json has per_scope field")
val result = run_simple(["doc-coverage", "--format=json"])
val stdout = result.0
expect(stdout.contains("\"per_scope\"")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage --format=json total_public is non-zero</summary>

#### doc-coverage --format=json total_public is non-zero _(slow)_

- doc-coverage --format=json total_public is non-zero
   - Expected: has_nonzero is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage --format=json total_public is non-zero")
val result = run_simple(["doc-coverage", "--format=json"])
val stdout = result.0
val has_nonzero = not stdout.contains("\"total_public\": 0")
expect(has_nonzero).to_equal(true)
```

</details>


</details>

### doc-coverage CLI - Markdown mode

<details>
<summary>Advanced: doc-coverage --format=md exits with 0</summary>

#### doc-coverage --format=md exits with 0 _(slow)_

- doc-coverage --format=md exits with 0
   - Expected: exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage --format=md exits with 0")
val result = run_simple(["doc-coverage", "--format=md"])
val exit_code = result.2
expect(exit_code).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage --format=md outputs markdown heading</summary>

#### doc-coverage --format=md outputs markdown heading _(slow)_

- doc-coverage --format=md outputs markdown heading
   - Expected: stdout contains `# Documentation Coverage Report`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage --format=md outputs markdown heading")
val result = run_simple(["doc-coverage", "--format=md"])
val stdout = result.0
expect(stdout.contains("# Documentation Coverage Report")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage --format=md contains table</summary>

#### doc-coverage --format=md contains table _(slow)_

- doc-coverage --format=md contains table
   - Expected: stdout contains `|`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage --format=md contains table")
val result = run_simple(["doc-coverage", "--format=md"])
val stdout = result.0
expect(stdout.contains("|")).to_equal(true)
```

</details>


</details>

### doc-coverage CLI - missing flag

<details>
<summary>Advanced: doc-coverage --missing exits with 0</summary>

#### doc-coverage --missing exits with 0 _(slow)_

- doc-coverage --missing exits with 0
   - Expected: exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage --missing exits with 0")
val result = run_simple(["doc-coverage", "--missing"])
val exit_code = result.2
expect(exit_code).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage --missing shows undocumented header</summary>

#### doc-coverage --missing shows undocumented header _(slow)_

- doc-coverage --missing shows undocumented header
   - Expected: stdout contains `Undocumented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage --missing shows undocumented header")
val result = run_simple(["doc-coverage", "--missing"])
val stdout = result.0
expect(stdout.contains("Undocumented")).to_equal(true)
```

</details>


</details>

### doc-coverage CLI - path scoping

<details>
<summary>Advanced: doc-coverage src/core scopes to core</summary>

#### doc-coverage src/core scopes to core _(slow)_

- doc-coverage src/core scopes to core
   - Expected: exit_code equals `0`
   - Expected: stdout contains `src/core`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage src/core scopes to core")
val result = run_simple(["doc-coverage", "src/core"])
val stdout = result.0
val exit_code = result.2
expect(exit_code).to_equal(0)
expect(stdout.contains("src/core")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: doc-coverage src/std scopes to std</summary>

#### doc-coverage src/std scopes to std _(slow)_

- doc-coverage src/std scopes to std
   - Expected: exit_code equals `0`
   - Expected: stdout contains `src/std`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc-coverage src/std scopes to std")
val result = run_simple(["doc-coverage", "src/std"])
val stdout = result.0
val exit_code = result.2
expect(exit_code).to_equal(0)
expect(stdout.contains("src/std")).to_equal(true)
```

</details>


</details>

### stats command coverage integration

<details>
<summary>Advanced: stats shows Coverage section with non-zero values</summary>

#### stats shows Coverage section with non-zero values _(slow)_

- stats shows Coverage section with non-zero values
   - Expected: exit_code equals `0`
   - Expected: stdout contains `Documentation Coverage Report`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stats shows Coverage section with non-zero values")
val result = run_simple(["doc-coverage"])
val stdout = result.0
val exit_code = result.2
expect(exit_code).to_equal(0)
expect(stdout.contains("Documentation Coverage Report")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: stats --json documentation total_public is non-zero</summary>

#### stats --json documentation total_public is non-zero _(slow)_

- stats --json documentation total_public is non-zero
   - Expected: has_nonzero is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stats --json documentation total_public is non-zero")
val result = run_simple(["doc-coverage", "--format=json"])
val stdout = result.0
val has_nonzero = not stdout.contains("\"total_public\": 0")
expect(has_nonzero).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infrastructure/doc_coverage_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering doc-coverage CLI - terminal mode, doc-coverage CLI - JSON mode, doc-coverage CLI - Markdown mode, doc-coverage CLI - missing flag, doc-coverage CLI - path scoping, stats command coverage integration.
- doc-coverage CLI - terminal mode
- doc-coverage CLI - JSON mode
- doc-coverage CLI - Markdown mode
- doc-coverage CLI - missing flag
- doc-coverage CLI - path scoping
- stats command coverage integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 18 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `427329772aba2395dff529a16d94ae30972a580d2646ee696e191d248ebfd85c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `427329772aba2395dff529a16d94ae30972a580d2646ee696e191d248ebfd85c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `427329772aba2395dff529a16d94ae30972a580d2646ee696e191d248ebfd85c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/infrastructure/doc_coverage_system_spec.spl
mirror: doc/06_spec/03_system/infrastructure/doc_coverage_system_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/infrastructure/doc_coverage_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/infrastructure/doc_coverage_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/infrastructure/doc_coverage_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/infrastructure/doc_coverage_system_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'doc-coverage exits with 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infrastructure/doc_coverage_system_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'doc-coverage shows coverage report header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infrastructure/doc_coverage_system_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'doc-coverage shows non-zero public function count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
