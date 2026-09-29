# Coverage Core Specification

> The coverage core module provides line, branch, and function coverage tracking during test execution. CoverageCollector records hit lines and function calls; CoverageStats computes ratios; data structs (SourceLoc, FunctionCoverage, ModuleCoverage, CoverageReport) carry the results.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coverage Core Specification

The coverage core module provides line, branch, and function coverage tracking during test execution. CoverageCollector records hit lines and function calls; CoverageStats computes ratios; data structs (SourceLoc, FunctionCoverage, ModuleCoverage, CoverageReport) carry the results.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COV-001 through #COV-025 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/coverage/coverage_core_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The coverage core module provides line, branch, and function coverage
tracking during test execution. CoverageCollector records hit lines
and function calls; CoverageStats computes ratios; data structs
(SourceLoc, FunctionCoverage, ModuleCoverage, CoverageReport) carry
the results.

## Key Concepts

| Concept           | Description                                      |
|-------------------|--------------------------------------------------|
| CoverageCollector | Mutable recorder of line hits and function calls  |
| CoverageStats     | Computed coverage ratios (line, branch, function) |
| CoverageReport    | Top-level report aggregating module coverages     |

## Behavior

- CoverageStats.empty() returns all-zero counters
- Coverage ratios return 0.0 when denominators are zero (no division by zero)
- CoverageCollector deduplicates line hits per file
- Function call counts increment on repeated calls
- clear() resets collector to empty state
- to_sdn() serialises collector state to SDN text

## Scenarios

### CoverageStats

#### empty()

#### returns all zeros

- returns all zeros
   - Expected: s.lines_hit equals `0`
   - Expected: s.lines_total equals `0`
   - Expected: s.branches_hit equals `0`
   - Expected: s.branches_total equals `0`
   - Expected: s.functions_hit equals `0`
   - Expected: s.functions_total equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns all zeros")
val s = CoverageStats.empty()
expect(s.lines_hit).to_equal(0)
expect(s.lines_total).to_equal(0)
expect(s.branches_hit).to_equal(0)
expect(s.branches_total).to_equal(0)
expect(s.functions_hit).to_equal(0)
expect(s.functions_total).to_equal(0)
```

</details>

#### line_coverage()

#### returns 0.0 when lines_total is 0

- returns 0.0 when lines_total is 0
   - Expected: s.line_coverage() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns 0.0 when lines_total is 0")
val s = CoverageStats.empty()
expect(s.line_coverage()).to_equal(0.0)
```

</details>

#### computes ratio when lines exist

- computes ratio when lines exist
   - Expected: s.line_coverage() equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes ratio when lines exist")
val s = CoverageStats(lines_hit: 5, lines_total: 10,
                       branches_hit: 0, branches_total: 0,
                       functions_hit: 0, functions_total: 0)
expect(s.line_coverage()).to_equal(0.5)
```

</details>

#### branch_coverage()

#### returns 0.0 when branches_total is 0

- returns 0.0 when branches_total is 0
   - Expected: s.branch_coverage() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns 0.0 when branches_total is 0")
val s = CoverageStats.empty()
expect(s.branch_coverage()).to_equal(0.0)
```

</details>

#### computes ratio with data

- computes ratio with data
   - Expected: s.branch_coverage() equals `0.75`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes ratio with data")
val s = CoverageStats(lines_hit: 0, lines_total: 0,
                       branches_hit: 3, branches_total: 4,
                       functions_hit: 0, functions_total: 0)
expect(s.branch_coverage()).to_equal(0.75)
```

</details>

#### function_coverage()

#### returns 0.0 when functions_total is 0

- returns 0.0 when functions_total is 0
   - Expected: s.function_coverage() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns 0.0 when functions_total is 0")
val s = CoverageStats.empty()
expect(s.function_coverage()).to_equal(0.0)
```

</details>

#### computes ratio with data

- computes ratio with data
   - Expected: s.function_coverage() equals `0.4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes ratio with data")
val s = CoverageStats(lines_hit: 0, lines_total: 0,
                       branches_hit: 0, branches_total: 0,
                       functions_hit: 2, functions_total: 5)
expect(s.function_coverage()).to_equal(0.4)
```

</details>

### CoverageCollector

#### create()

#### makes empty collector

- makes empty collector
   - Expected: files.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("makes empty collector")
val c = CoverageCollector.create()
val files = c.executed_files()
expect(files.len()).to_equal(0)
```

</details>

#### record_line

#### creates entry for new file

- creates entry for new file
   - Expected: files.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates entry for new file")
var c = CoverageCollector.create()
c.record_line("main.spl", 10)
val files = c.executed_files()
expect(files.len()).to_equal(1)
expect(files).to_contain("main.spl")
```

</details>

#### adds line to existing file

- adds line to existing file
   - Expected: s.lines_hit equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adds line to existing file")
var c = CoverageCollector.create()
c.record_line("main.spl", 10)
c.record_line("main.spl", 20)
val s = c.stats()
expect(s.lines_hit).to_equal(2)
```

</details>

#### ignores duplicate line numbers

- ignores duplicate line numbers
   - Expected: s.lines_hit equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ignores duplicate line numbers")
var c = CoverageCollector.create()
c.record_line("main.spl", 10)
c.record_line("main.spl", 10)
val s = c.stats()
expect(s.lines_hit).to_equal(1)
```

</details>

#### record_function_call

#### records first call with count 1

- records first call with count 1
   - Expected: c.was_function_called("foo") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records first call with count 1")
var c = CoverageCollector.create()
c.record_function_call("foo")
expect(c.was_function_called("foo")).to_equal(true)
```

</details>

#### increments on second call

- increments on second call
   - Expected: c.was_function_called("bar") is true
   - Expected: s.functions_total equals `1`
   - Expected: s.functions_hit equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("increments on second call")
var c = CoverageCollector.create()
c.record_function_call("bar")
c.record_function_call("bar")
# After two calls the function is still called
expect(c.was_function_called("bar")).to_equal(true)
# Stats should count exactly 1 distinct function
val s = c.stats()
expect(s.functions_total).to_equal(1)
expect(s.functions_hit).to_equal(1)
```

</details>

#### was_function_called

#### returns true for called function

- returns true for called function
   - Expected: c.was_function_called("do_thing") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns true for called function")
var c = CoverageCollector.create()
c.record_function_call("do_thing")
expect(c.was_function_called("do_thing")).to_equal(true)
```

</details>

#### returns false for uncalled function

- returns false for uncalled function
   - Expected: c.was_function_called("never_called") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns false for uncalled function")
val c = CoverageCollector.create()
expect(c.was_function_called("never_called")).to_equal(false)
```

</details>

#### executed_files

#### returns empty list for fresh collector

- returns empty list for fresh collector
   - Expected: c.executed_files().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty list for fresh collector")
val c = CoverageCollector.create()
expect(c.executed_files().len()).to_equal(0)
```

</details>

#### returns recorded file paths

- returns recorded file paths
   - Expected: files.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns recorded file paths")
var c = CoverageCollector.create()
c.record_line("a.spl", 1)
c.record_line("b.spl", 5)
val files = c.executed_files()
expect(files.len()).to_equal(2)
expect(files).to_contain("a.spl")
expect(files).to_contain("b.spl")
```

</details>

#### stats()

#### computes real statistics

- computes real statistics
   - Expected: s.lines_hit equals `3`
   - Expected: s.lines_total equals `3`
   - Expected: s.functions_hit equals `2`
   - Expected: s.functions_total equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes real statistics")
var c = CoverageCollector.create()
c.record_line("a.spl", 1)
c.record_line("a.spl", 2)
c.record_line("a.spl", 3)
c.record_function_call("foo")
c.record_function_call("bar")
val s = c.stats()
expect(s.lines_hit).to_equal(3)
expect(s.lines_total).to_equal(3)
expect(s.functions_hit).to_equal(2)
expect(s.functions_total).to_equal(2)
```

</details>

#### returns zeros on empty collector

- returns zeros on empty collector
   - Expected: s.lines_hit equals `0`
   - Expected: s.lines_total equals `0`
   - Expected: s.functions_hit equals `0`
   - Expected: s.functions_total equals `0`
   - Expected: s.branches_hit equals `0`
   - Expected: s.branches_total equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns zeros on empty collector")
val c = CoverageCollector.create()
val s = c.stats()
expect(s.lines_hit).to_equal(0)
expect(s.lines_total).to_equal(0)
expect(s.functions_hit).to_equal(0)
expect(s.functions_total).to_equal(0)
expect(s.branches_hit).to_equal(0)
expect(s.branches_total).to_equal(0)
```

</details>

#### clear()

#### resets all state

- resets all state
   - Expected: c.executed_files().len() equals `0`
   - Expected: c.was_function_called("foo") is false
   - Expected: s.lines_hit equals `0`
   - Expected: s.functions_total equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resets all state")
var c = CoverageCollector.create()
c.record_line("a.spl", 1)
c.record_function_call("foo")
c.clear()
expect(c.executed_files().len()).to_equal(0)
expect(c.was_function_called("foo")).to_equal(false)
val s = c.stats()
expect(s.lines_hit).to_equal(0)
expect(s.functions_total).to_equal(0)
```

</details>

#### to_sdn()

#### returns header on empty collector

- returns header on empty collector


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns header on empty collector")
val c = CoverageCollector.create()
val sdn = c.to_sdn()
expect(sdn).to_start_with("coverage:")
```

</details>

#### includes file info and function calls with data

- includes file info and function calls with data


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes file info and function calls with data")
var c = CoverageCollector.create()
c.record_line("main.spl", 5)
c.record_function_call("init")
val sdn = c.to_sdn()
expect(sdn).to_contain("main.spl")
expect(sdn).to_contain("init")
expect(sdn).to_contain("1 calls")
```

</details>

### Coverage data structs

#### SourceLoc

#### can be constructed with file, line, column

- can be constructed with file, line, column
   - Expected: loc.file equals `test.spl`
   - Expected: loc.line equals `42`
   - Expected: loc.column equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can be constructed with file, line, column")
val loc = SourceLoc(file: "test.spl", line: 42, column: 8)
expect(loc.file).to_equal("test.spl")
expect(loc.line).to_equal(42)
expect(loc.column).to_equal(8)
```

</details>

#### FunctionCoverage

#### can be constructed with coverage data

- can be constructed with coverage data
   - Expected: fc.name equals `my_func`
   - Expected: fc.lines_hit equals `10`
   - Expected: fc.lines_total equals `15`
   - Expected: fc.branches_hit equals `3`
   - Expected: fc.branches_total equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can be constructed with coverage data")
val fc = FunctionCoverage(name: "my_func",
                           lines_hit: 10, lines_total: 15,
                           branches_hit: 3, branches_total: 6)
expect(fc.name).to_equal("my_func")
expect(fc.lines_hit).to_equal(10)
expect(fc.lines_total).to_equal(15)
expect(fc.branches_hit).to_equal(3)
expect(fc.branches_total).to_equal(6)
```

</details>

#### ModuleCoverage

#### can be constructed with name and functions list

- can be constructed with name and functions list
   - Expected: mc.name equals `my_mod`
   - Expected: mc.functions.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can be constructed with name and functions list")
val fc = FunctionCoverage(name: "f", lines_hit: 1, lines_total: 2,
                           branches_hit: 0, branches_total: 0)
val mc = ModuleCoverage(name: "my_mod", functions: [fc])
expect(mc.name).to_equal("my_mod")
expect(mc.functions.len()).to_equal(1)
```

</details>

#### CoverageReport

#### can be constructed with modules and stats

- can be constructed with modules and stats
   - Expected: report.modules.len() equals `0`
   - Expected: report.stats.lines_hit equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can be constructed with modules and stats")
val stats = CoverageStats.empty()
val report = CoverageReport(modules: [], stats: stats)
expect(report.modules.len()).to_equal(0)
expect(report.stats.lines_hit).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-coverage-core`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f2fb0dc3d48fd0fd6ba8a891b77d79a71b5d2881e94641d98ffb853f525d5c79`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f2fb0dc3d48fd0fd6ba8a891b77d79a71b5d2881e94641d98ffb853f525d5c79`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f2fb0dc3d48fd0fd6ba8a891b77d79a71b5d2881e94641d98ffb853f525d5c79`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **77/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/coverage/coverage_core_spec.spl
mirror: doc/06_spec/03_system/coverage/coverage_core_spec.md (current)
findings: 11 blockers: 1
  narrative=100 structure=80 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=77; blocker cap makes effective=49
doc/06_spec/03_system/coverage/coverage_core_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/coverage/coverage_core_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/coverage/coverage_core_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 42 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/coverage/coverage_core_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/coverage/coverage_core_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns all zeros' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/coverage/coverage_core_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 0.0 when lines_total is 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/coverage/coverage_core_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes ratio when lines exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/coverage/coverage_core_spec.spl:286:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be constructed with file, line, column' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/coverage/coverage_core_spec.spl:295:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be constructed with coverage data' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/coverage/coverage_core_spec.spl:308:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be constructed with name and functions list' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/coverage/coverage_core_spec.spl:318:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be constructed with modules and stats' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
