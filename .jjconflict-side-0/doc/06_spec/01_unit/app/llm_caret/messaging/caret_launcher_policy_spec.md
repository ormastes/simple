# Caret Launcher Policy Specification

> Tests covering Caret messaging launcher policy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Caret Launcher Policy Specification

## Scenarios

### Caret messaging launcher policy

#### allows only the thin messaging supervisor without a monolithic artifact

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allows only the thin messaging supervisor without a monolithic artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("allows only the thin messaging supervisor without a monolithic artifact")
val source = rt_file_read_text("bin/caret") ?? ""
expect(source).to_contain("messaging_supervisor=1")
expect(source).to_contain("Interpreting this control plane therefore never")
expect(source).to_contain("interprets the PureDatabase hot path")
expect(source).to_contain("src/app/llm_caret/messaging/main.spl")
```

</details>

#### keeps legacy Caret commands native-only by default

- keeps legacy Caret commands native-only by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps legacy Caret commands native-only by default")
val source = rt_file_read_text("bin/caret") ?? ""
expect(source).to_contain("SIMPLE_CARET_ALLOW_SOURCE_FALLBACK:-0")
expect(source).to_contain("cached native Caret artifact not found")
```

</details>

#### keeps the minimal entrypoint separate from legacy Caret UI providers

- keeps the minimal entrypoint separate from legacy Caret UI providers
   - Expected: source does not contain `chat_tui`
   - Expected: source does not contain `llm_caret.provider`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the minimal entrypoint separate from legacy Caret UI providers")
val source = rt_file_read_text("src/app/llm_caret/messaging/main.spl") ?? ""
expect(source).to_contain("run_messaging_cli(get_cli_args())")
expect(source.contains("chat_tui")).to_equal(false)
expect(source.contains("llm_caret.provider")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/caret_launcher_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Caret messaging launcher policy.
- Caret messaging launcher policy

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f50349712e554551716ca9c82d9fce47dd2bf6f92839eba7ee3a30ccf5c714f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f50349712e554551716ca9c82d9fce47dd2bf6f92839eba7ee3a30ccf5c714f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f50349712e554551716ca9c82d9fce47dd2bf6f92839eba7ee3a30ccf5c714f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/caret_launcher_policy_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/caret_launcher_policy_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/caret_launcher_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/caret_launcher_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/caret_launcher_policy_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/llm_caret/messaging/caret_launcher_policy_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/caret_launcher_policy_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows only the thin messaging supervisor without a monolithic artifact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/caret_launcher_policy_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps legacy Caret commands native-only by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/caret_launcher_policy_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the minimal entrypoint separate from legacy Caret UI providers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
