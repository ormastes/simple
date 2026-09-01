# Dispatch Table App Path Resolves Specification

> Tests covering CLI dispatch table app_path integrity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dispatch Table App Path Resolves Specification

## Scenarios

### CLI dispatch table app_path integrity

#### resolves the two entries that were found stale

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves the two entries that were found stale
   - Expected: readable(entry.app_path) is true
   - Expected: entry.app_path equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("resolves the two entries that were found stale")
# Reproducer: these two names regressed. Named explicitly so the
# reproducer keeps failing if either is reverted.
for entry in get_command_table():
    if entry.name == "wrapper-gen":
        expect(readable(entry.app_path)).to_equal(true)
    if entry.name == "migrate":
        # `migrate` has no app directory; the entry must not claim one.
        expect(entry.app_path).to_equal("")
```

</details>

#### resolves every declared app_path to a readable source file

- resolves every declared app_path to a readable source file
   - Expected: broken.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("resolves every declared app_path to a readable source file")
# Detection spec: generalizes to the whole defect CLASS. Any future
# rename that leaves a table entry behind fails here, naming the entry.
var broken: [text] = []
var checked = 0
for entry in get_command_table():
    if entry.app_path.len() > 0:
        checked = checked + 1
        if not readable(entry.app_path):
            broken.push("{entry.name} -> {entry.app_path}")
# Non-vacuity: a run that checked nothing is a broken guard, not a pass.
expect(checked).to_be_greater_than(50)
expect(broken.len()).to_equal(0)
```

</details>

#### declares each command name exactly once

- declares each command name exactly once
   - Expected: dupes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("declares each command name exactly once")
# Same family: a duplicated name makes the second entry dead code,
# which is how a stale path survives unnoticed.
var dupes: [text] = []
val table = get_command_table()
var i = 0
while i < table.len():
    var j = i + 1
    while j < table.len():
        if table[i].name == table[j].name:
            dupes.push(table[i].name)
        j = j + 1
    i = i + 1
expect(dupes.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/dispatch_table_app_path_resolves_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CLI dispatch table app_path integrity.
- CLI dispatch table app_path integrity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e524aa5ecf65bea9588b31bbf7f73437fd6ad88c57fcd4ae38bf98d01e57a5dd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e524aa5ecf65bea9588b31bbf7f73437fd6ad88c57fcd4ae38bf98d01e57a5dd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e524aa5ecf65bea9588b31bbf7f73437fd6ad88c57fcd4ae38bf98d01e57a5dd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/cli/dispatch_table_app_path_resolves_spec.spl
mirror: doc/06_spec/01_unit/app/cli/dispatch_table_app_path_resolves_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli/dispatch_table_app_path_resolves_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/dispatch_table_app_path_resolves_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/dispatch_table_app_path_resolves_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/cli/dispatch_table_app_path_resolves_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves the two entries that were found stale' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/dispatch_table_app_path_resolves_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves every declared app_path to a readable source file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/dispatch_table_app_path_resolves_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares each command name exactly once' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
