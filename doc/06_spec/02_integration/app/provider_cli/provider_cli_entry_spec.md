# Provider Cli Entry Specification

> Tests covering separately targetable provider CLI entry.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Cli Entry Specification

## Scenarios

### separately targetable provider CLI entry

#### REQ-003 exposes command metadata without provider activation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ-003 exposes command metadata without provider activation
   - Expected: result.exit_code equals `0`
   - Expected: result.output equals `fmt-leaf|SimpleCliCommandV1/1|provider=257|abi=771`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("REQ-003 exposes command metadata without provider activation")
val result = provider_cli_execute_v1(["metadata"])
expect(result.exit_code).to_equal(0)
expect(result.output).to_equal("fmt-leaf|SimpleCliCommandV1/1|provider=257|abi=771")
```

</details>

#### REQ-003 dispatches the in-process leaf through SimpleProviderQueryV1

- REQ-003 dispatches the in-process leaf through SimpleProviderQueryV1
   - Expected: result.exit_code equals `0`
   - Expected: result.output equals `formatted:alpha.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("REQ-003 dispatches the in-process leaf through SimpleProviderQueryV1")
val result = provider_cli_execute_v1(["run", "fmt-leaf", "alpha.spl"])
expect(result.exit_code).to_equal(0)
expect(result.output).to_equal("formatted:alpha.spl")
```

</details>

#### REQ-003 does not pretend native or SMF artifacts are callable

- REQ-003 does not pretend native or SMF artifacts are callable
   - Expected: native_result.exit_code equals `3`
   - Expected: native_result.diagnostic equals `provider-not-process-callable:native`
   - Expected: smf_result.exit_code equals `3`
   - Expected: smf_result.diagnostic equals `provider-not-process-callable:smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("REQ-003 does not pretend native or SMF artifacts are callable")
val native_result = provider_cli_execute_v1(["query", "native"])
val smf_result = provider_cli_execute_v1(["query", "smf"])
expect(native_result.exit_code).to_equal(3)
expect(native_result.diagnostic).to_equal("provider-not-process-callable:native")
expect(smf_result.exit_code).to_equal(3)
expect(smf_result.diagnostic).to_equal("provider-not-process-callable:smf")
```

</details>

#### REQ-003 rejects unknown leaf commands

- REQ-003 rejects unknown leaf commands
   - Expected: result.exit_code equals `3`
   - Expected: result.diagnostic equals `command-not-provided`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("REQ-003 rejects unknown leaf commands")
val result = provider_cli_execute_v1(["run", "unknown", "alpha.spl"])
expect(result.exit_code).to_equal(3)
expect(result.diagnostic).to_equal("command-not-provided")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/provider_cli/provider_cli_entry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering separately targetable provider CLI entry.
- separately targetable provider CLI entry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e2eb339755c61ca189c60b08ec83c0077a3eb7a41021a1e706af6dd463da2ea0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e2eb339755c61ca189c60b08ec83c0077a3eb7a41021a1e706af6dd463da2ea0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e2eb339755c61ca189c60b08ec83c0077a3eb7a41021a1e706af6dd463da2ea0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/app/provider_cli/provider_cli_entry_spec.spl
mirror: doc/06_spec/02_integration/app/provider_cli/provider_cli_entry_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/provider_cli/provider_cli_entry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/provider_cli/provider_cli_entry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/provider_cli/provider_cli_entry_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/provider_cli/provider_cli_entry_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-003 exposes command metadata without provider activation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/provider_cli/provider_cli_entry_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-003 dispatches the in-process leaf through SimpleProviderQueryV1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/provider_cli/provider_cli_entry_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-003 does not pretend native or SMF artifacts are callable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
