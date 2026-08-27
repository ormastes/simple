# SPipe Knowledge Compiler primary workflow

> `bin/simple spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl --output doc/06_spec --no-index`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SPipe Knowledge Compiler primary workflow

`bin/simple spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl --output doc/06_spec --no-index`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Generation
`bin/simple spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl --output doc/06_spec --no-index`.

## Scenarios

### SPipe Knowledge Compiler primary operator workflow

#### index flow: identity, snapshots, and graph publication stay deterministic

- Run the Wave 2-3 acceptance suites
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-001 REQ-SPKC-005 REQ-SPKC-029
step("Run the Wave 2-3 acceptance suites")
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c",
    "cd examples/05_stdlib/spipe && node --test test/integration/knowledge_wave2_test.js test/integration/knowledge_wave3_test.js"])
expect(code).to_equal(0)  # oracle: 34/34 subtests green
expect(stdout).to_contain("# tests 34")  # oracle: full suites executed
expect(stdout).to_contain("# fail 0")  # oracle: typed snapshot/UID/graph results all hold
```

</details>

#### browse flow: bounded read-only graph projections hold without identity change

- Run the graph model and store suites
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-006 REQ-SPKC-009
step("Run the graph model and store suites")
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c",
    "cd examples/05_stdlib/spipe && node --test test/unit/graph_model_test.js test/unit/graph_store_test.js test/unit/graph_extraction_diagnostics_test.js"])
expect(code).to_equal(0)  # oracle: projection suites green
expect(stdout).to_contain("# fail 0")  # oracle: no projection regressed identity
expect(stdout).to_contain("# tests 2")  # oracle: non-vacuous run guard
```

</details>

#### search flow: provider parity lane explains ranked hits with locked evidence

- Run the Wave 4 JavaScript provider acceptance suite
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-017 REQ-SPKC-018
step("Run the Wave 4 JavaScript provider acceptance suite")
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c",
    "cd examples/05_stdlib/spipe && node --test test/integration/knowledge_wave4_search_test.js"])
expect(code).to_equal(0)  # oracle: 9/9 subtests green
expect(stdout).to_contain("# fail 0")  # oracle: roots/scores/order/explanations all locked
```

</details>

#### refactor flow: exact old or new state across snapshot boundaries

- Run the snapshot boundary and restart recovery suites
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-019 REQ-SPKC-020 REQ-SPKC-029
step("Run the snapshot boundary and restart recovery suites")
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c",
    "cd examples/05_stdlib/spipe && node --test test/unit/graph_snapshot_boundary_test.js test/unit/graph_snapshot_restart_test.js"])
expect(code).to_equal(0)  # oracle: recovery suites green
expect(stdout).to_contain("# fail 0")  # oracle: no mixed state survives
```

</details>

#### promotion flow: released CLI fails closed until compiler commands land

- Probe spipe --help for unreleased compiler commands
   - Expected: code equals `0`
   - Expected: leaked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-021 REQ-SPKC-029
step("Probe spipe --help for unreleased compiler commands")
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c",
    "cd examples/05_stdlib/spipe && node cli/spipe.js --help"])
expect(code).to_equal(0)  # oracle: released surface is healthy
val leaked = stdout.contains("knowledge-compile") or stdout.contains("index") or stdout.contains("promote")
expect(leaked).to_equal(false)  # oracle: no unproven compiler command is invocable
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SPKC-029`
- `REQ-SPKC-001`
- `REQ-SPKC-005`
- `REQ-SPKC-006`
- `REQ-SPKC-009`
- `REQ-SPKC-017`
- `REQ-SPKC-020`
- `REQ-SPKC-018`
- `REQ-SPKC-019`
- `REQ-SPKC-021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8cc668ee7aa1be98f90ee33b37071347411fd2c127e57fe639f2caf0b1b75f2c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8cc668ee7aa1be98f90ee33b37071347411fd2c127e57fe639f2caf0b1b75f2c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8cc668ee7aa1be98f90ee33b37071347411fd2c127e57fe639f2caf0b1b75f2c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl
mirror: doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'index flow: identity, snapshots, and graph publication stay deterministic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'browse flow: bounded read-only graph projections hold without identity change' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'search flow: provider parity lane explains ranked hits with locked evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
