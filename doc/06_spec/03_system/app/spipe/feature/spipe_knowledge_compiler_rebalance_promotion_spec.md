# SPipe rebalancing, promotion, and generated-skill safety

> `bin/simple spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl --output doc/06_spec --no-index`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SPipe rebalancing, promotion, and generated-skill safety

`bin/simple spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl --output doc/06_spec --no-index`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Requirement map
- Rebalancing substrate: REQ-SPKC-021, REQ-SPKC-022.
- Promotion boundary: REQ-SPKC-023, REQ-SPKC-024.
- Skill/phase/migration: REQ-SPKC-025.

## Generation
`bin/simple spipe-docgen test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl --output doc/06_spec --no-index`

## Scenarios

### SPipe organization and common-knowledge review

#### the graph substrate proposals are built on stays deterministic and green

- Run the Wave 2-3 identity, snapshot, and graph-publication suites
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-021 REQ-SPKC-022
step("Run the Wave 2-3 identity, snapshot, and graph-publication suites")
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c",
    "cd examples/05_stdlib/spipe && node --test test/integration/knowledge_wave2_test.js test/integration/knowledge_wave3_test.js"])
expect(code).to_equal(0)  # oracle: 34/34 wave2+3 subtests green
expect(stdout).to_contain("# tests 34")  # oracle: full suites executed
expect(stdout).to_contain("# fail 0")  # oracle: no subtest failed
```

</details>

<details>
<summary>Advanced: prior-tree preservation semantics hold at every snapshot boundary</summary>

#### prior-tree preservation semantics hold at every snapshot boundary

- Run the snapshot boundary and restart unit suites
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-021 REQ-SPKC-029
step("Run the snapshot boundary and restart unit suites")
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c",
    "cd examples/05_stdlib/spipe && node --test test/unit/graph_snapshot_boundary_test.js test/unit/graph_snapshot_restart_test.js"])
expect(code).to_equal(0)  # oracle: prior state recoverable at each durability boundary
expect(stdout).to_contain("# fail 0")  # oracle: zero failures across both suites
```

</details>


</details>

<details>
<summary>Advanced: released CLI fails closed: no rebalance or promotion command is exposed</summary>

#### released CLI fails closed: no rebalance or promotion command is exposed

- Probe spipe --help for the unreleased wave 5-11 commands
   - Expected: code equals `0`
   - Expected: leaked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-023 REQ-SPKC-024 REQ-SPKC-025 REQ-SPKC-028
step("Probe spipe --help for the unreleased wave 5-11 commands")
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c",
    "cd examples/05_stdlib/spipe && node cli/spipe.js --help"])
expect(code).to_equal(0)  # oracle: released surface itself is healthy
val leaked = stdout.contains("rebalance") or stdout.contains("promot")
expect(leaked).to_equal(false)  # oracle: unreleased commands cannot be invoked, so unsafe promotion is unreachable
```

</details>


</details>

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

- `REQ-SPKC-025`
- `REQ-SPKC-021`
- `REQ-SPKC-022`
- `REQ-SPKC-023`
- `REQ-SPKC-024`
- `REQ-SPKC-022.`
- `REQ-SPKC-024.`
- `REQ-SPKC-025.`
- `REQ-SPKC-029`
- `REQ-SPKC-028`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f4499f8bc625f915e5cfbb7b4e8175907b05c082b7b694d986cef1c7b5fdeb6b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f4499f8bc625f915e5cfbb7b4e8175907b05c082b7b694d986cef1c7b5fdeb6b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f4499f8bc625f915e5cfbb7b4e8175907b05c082b7b694d986cef1c7b5fdeb6b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl
mirror: doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prior-tree preservation semantics hold at every snapshot boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_rebalance_promotion_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'released CLI fails closed: no rebalance or promotion command is exposed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
