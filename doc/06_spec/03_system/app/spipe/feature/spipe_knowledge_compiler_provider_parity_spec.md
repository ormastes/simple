# SPipe knowledge-compiler provider parity

> This executable manual owns the Wave 4 provider-parity acceptance surface.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SPipe knowledge-compiler provider parity

This executable manual owns the Wave 4 provider-parity acceptance surface.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

This executable manual owns the Wave 4 provider-parity acceptance surface.
Every scenario EXECUTES the locked acceptance runner
(examples/05_stdlib/spipe/test/integration/knowledge_wave4_search_test.js)
instead of asserting a placeholder failure.

- The JavaScript provider lane runs for real: locked golden roots, scores,
  ordering, explanations, mixed incremental deltas, boundary and latency
  gates all execute against the live provider code.
- The Simple/DBFS lanes stay fail-closed: enabling SPIPE_RUN_SIMPLE_CONFORMANCE
  without an admitted self-hosted binary (SPIPE_SIMPLE_BIN /
  SPIPE_STAGE4_PROVENANCE absolute, canonical, provenance-verified) must make
  the runner fail. Source presence is never provider-parity evidence.

Fixture oracle:
`examples/05_stdlib/spipe/test/fixture/wave4_search/fixture_manifest.json`.

## Scenarios

### SPipe knowledge compiler provider parity

#### javascript provider lane meets every locked golden, boundary, and latency gate

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Run the wave4 acceptance runner with the production JavaScript provider
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-011 REQ-SPKC-012 REQ-SPKC-013
step("Run the wave4 acceptance runner with the production JavaScript provider")
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c",
    "cd examples/05_stdlib/spipe && node --test test/integration/knowledge_wave4_search_test.js"])
expect(code).to_equal(0)  # oracle: 9/9 subtests green, per runner summary
expect(stdout).to_contain("# tests 9")  # oracle: full suite ran, not a subset
expect(stdout).to_contain("# fail 0")  # oracle: no subtest failed
```

</details>

#### golden ordering, identity dominance, tie-breaks, filters, explanations and deltas execute green

- Run the same runner and pin the named parity subtests
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-011 REQ-SPKC-012 REQ-SPKC-014
step("Run the same runner and pin the named parity subtests")
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c",
    "cd examples/05_stdlib/spipe && node --test test/integration/knowledge_wave4_search_test.js 2>&1 | grep -c '^ok '"])
expect(code).to_equal(0)  # oracle: grep itself succeeded
expect(stdout.trim()).to_equal("9")  # oracle: all nine named parity subtests reported ok
```

</details>

#### enabling the Simple conformance lane without an admitted self-hosted binary fails closed

- Run with SPIPE_RUN_SIMPLE_CONFORMANCE=1 but no SPIPE_SIMPLE_BIN admission
   - Expected: code != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SPKC-011 REQ-SPKC-015
step("Run with SPIPE_RUN_SIMPLE_CONFORMANCE=1 but no SPIPE_SIMPLE_BIN admission")
val (stdout, _stderr, code) = process_run("/bin/sh", ["-c",
    "cd examples/05_stdlib/spipe && SPIPE_RUN_SIMPLE_CONFORMANCE=1 node --test test/integration/knowledge_wave4_search_test.js"])
expect(code != 0).to_equal(true)  # oracle: runner rejects the run as NOT-EVIDENCE
expect(stdout).to_contain("SPIPE_SIMPLE_BIN and SPIPE_STAGE4_PROVENANCE must be absolute paths")  # oracle: fail-closed reason is the admission gap
```

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

- `REQ-SPKC-011`
- `REQ-SPKC-012`
- `REQ-SPKC-013`
- `REQ-SPKC-014`
- `REQ-SPKC-015`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ed87f9417c0210b31bedfd11c44115499f671bbc4c87b6ead0273f68dc591093`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ed87f9417c0210b31bedfd11c44115499f671bbc4c87b6ead0273f68dc591093`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ed87f9417c0210b31bedfd11c44115499f671bbc4c87b6ead0273f68dc591093`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl
mirror: doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'javascript provider lane meets every locked golden, boundary, and latency gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'golden ordering, identity dominance, tie-breaks, filters, explanations and deltas execute green' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/spipe/feature/spipe_knowledge_compiler_provider_parity_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enabling the Simple conformance lane without an admitted self-hosted binary fails closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
