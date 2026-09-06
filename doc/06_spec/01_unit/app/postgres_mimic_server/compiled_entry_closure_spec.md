# Compiled Entry Closure Specification

> Tests covering PostgreSQL mimic compiled entry closure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiled Entry Closure Specification

## Scenarios

### PostgreSQL mimic compiled entry closure

#### does not import the broad CLI or IO utility graph

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not import the broad CLI or IO utility graph
   - Expected: source does not contain `std.cli.cli_util`
   - Expected: source does not contain `use std.io`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not import the broad CLI or IO utility graph")
val source = rt_file_read_text("src/app/postgres_mimic_server/main.spl") ?? ""
expect(source).to_contain("extern fn sys_get_args() -> [text]")
expect(source).to_contain("fn pg_flag_value(args: [text], flag: text, fallback: text) -> text:")
expect(source.contains("std.cli.cli_util")).to_equal(false)
expect(source.contains("use std.io")).to_equal(false)
```

</details>

#### keeps the pure-Simple PostgreSQL mimic database capsule

- keeps the pure-Simple PostgreSQL mimic database capsule


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the pure-Simple PostgreSQL mimic database capsule")
val source = rt_file_read_text("src/app/postgres_mimic_server/main.spl") ?? ""
expect(source).to_contain("postgres_mimic_open(path)")
expect(source).to_contain("postgres_mimic_simple_query(server, session, sql)")
```

</details>

#### uses owner-module façades instead of imported class methods

- uses owner-module façades instead of imported class methods
   - Expected: source does not contain `PostgresMimicServer.open`
   - Expected: source does not contain `server.startup`
   - Expected: source does not contain `server.simple_query`
   - Expected: source does not contain `server.close`
   - Expected: source does not contain `.join(`
   - Expected: source does not contain `.map(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses owner-module façades instead of imported class methods")
val source = rt_file_read_text("src/app/postgres_mimic_server/main.spl") ?? ""
expect(source.contains("PostgresMimicServer.open")).to_equal(false)
expect(source.contains("server.startup")).to_equal(false)
expect(source.contains("server.simple_query")).to_equal(false)
expect(source.contains("server.close")).to_equal(false)
expect(source.contains(".join(")).to_equal(false)
expect(source.contains(".map(")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/postgres_mimic_server/compiled_entry_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PostgreSQL mimic compiled entry closure.
- PostgreSQL mimic compiled entry closure

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

- Canonical SPipe generation for source `93fdf9acebc0cde7db22f2582274297e6be259dd6f5bc917f08528c50090a8b0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `93fdf9acebc0cde7db22f2582274297e6be259dd6f5bc917f08528c50090a8b0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `93fdf9acebc0cde7db22f2582274297e6be259dd6f5bc917f08528c50090a8b0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/postgres_mimic_server/compiled_entry_closure_spec.spl
mirror: doc/06_spec/01_unit/app/postgres_mimic_server/compiled_entry_closure_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/app/postgres_mimic_server/compiled_entry_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/postgres_mimic_server/compiled_entry_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/postgres_mimic_server/compiled_entry_closure_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/postgres_mimic_server/compiled_entry_closure_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not import the broad CLI or IO utility graph' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/postgres_mimic_server/compiled_entry_closure_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the pure-Simple PostgreSQL mimic database capsule' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/postgres_mimic_server/compiled_entry_closure_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses owner-module façades instead of imported class methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
