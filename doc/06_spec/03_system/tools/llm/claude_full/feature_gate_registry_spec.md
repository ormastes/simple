# Claude Full Feature-Gate Registry

> REQ-LLM-CARET-HIDDEN-008

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Feature-Gate Registry

REQ-LLM-CARET-HIDDEN-008

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

REQ-LLM-CARET-HIDDEN-008

Validates a bounded cross-map from Claude-full feature-gate owners to focused
or aggregate system-test evidence. It preserves the known distinction between
root command metadata and leaf conditional behavior.

This is parts-bin evidence. It does not prove shipped Caret admission, future
unimported gate discovery, or complete current-upstream Claude parity.

## Scenarios

### Claude full feature-gate registry

### REQ-LLM-CARET-HIDDEN-008: bounded gate-owner cross-map

#### should validate the bounded accepted Claude feature-gate registry
#### should preserve compact root metadata and conditional owner behavior

- should preserve compact root metadata and conditional owner behavior
- Reconcile root metadata with owner behavior
   - Expected: compact.root_command equals `/compact`
   - Expected: owner_default.condition equals `disableCompactEnvTruthy=false`
   - Expected: owner_disabled.condition equals `disableCompactEnvTruthy=true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve compact root metadata and conditional owner behavior")
step("Reconcile root metadata with owner behavior")
val records = setup_claude_feature_gate_fixture()
val compact = _feature_gate_record(records, "compact")
val root = findRootCommand("/compact")
val owner_default = _feature_gate_probe(compact, "default")
val owner_disabled = _feature_gate_probe(compact, "disabled-by-env")

expect(root.found).to_be(true)
expect(root.command.enabled).to_be(true)
expect(root.command.hidden).to_be(false)
expect(compact.root_command).to_equal("/compact")
expect(compact.root_enabled).to_be(true)
expect(compact.root_hidden).to_be(false)
expect(owner_default.condition).to_equal("disableCompactEnvTruthy=false")
expect(owner_default.enabled).to_be(true)
expect(owner_disabled.condition).to_equal("disableCompactEnvTruthy=true")
expect(owner_disabled.enabled).to_be(false)
```

</details>

#### should reject duplicate ownerless and incomplete gate records

- should reject duplicate ownerless and incomplete gate records
- Check feature-gate completeness and rejection
   - Expected: diagnostics equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject duplicate ownerless and incomplete gate records")
step("Check feature-gate completeness and rejection")
val diagnostics = check_claude_feature_gate_registry(_malformed_feature_gate_fixture())

expect(diagnostics).to_equal([
    "duplicate-source-id:duplicate",
    "duplicate-root-command:/dup",
    "ownerless-record:duplicate",
    "root-metadata-without-command:incomplete",
    "incomplete-record:incomplete",
    "empty-probe-condition:incomplete:default",
    "duplicate-probe-id:incomplete:default",
    "empty-probe-id:incomplete",
    "default-probe-mismatch:incomplete",
    "conditional-probes-incomplete:incomplete",
    "invalid-gate-kind:invalid",
    "invalid-state-shape:invalid",
    "unknown-default-labeled:invalid",
    "compact-drift-missing"
])
```

</details>

#### should reject import-frontier owners without registry coverage in either direction

- should reject import-frontier owners without registry coverage in either direction
- Compare the bounded import frontier with registry owner edges
   - Expected: diagnostics equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject import-frontier owners without registry coverage in either direction")
step("Compare the bounded import frontier with registry owner edges")
val records = setup_claude_feature_gate_fixture()
val diagnostics = check_feature_gate_source_completeness(
    records,
    _feature_gate_drifted_source_fixture()
)

expect(diagnostics).to_equal([
    "duplicate-discovered-source-owner:src/app/llm_caret/claude_full/commands/compact/index.spl|compactCommand",
    "unregistered-source-owner:src/app/llm_caret/claude_full/future/newGate.spl|newGateEnabled",
    "registry-owner-not-discovered:src/app/llm_caret/claude_full/bridge/bridgeEnabled.spl|isCcrMirrorEnabled"
])
```

</details>

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

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-HIDDEN-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6b999b627dee818dd5c4b4cede0e77154f71fbd9602a320f7e38f46ef0a73be6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6b999b627dee818dd5c4b4cede0e77154f71fbd9602a320f7e38f46ef0a73be6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6b999b627dee818dd5c4b4cede0e77154f71fbd9602a320f7e38f46ef0a73be6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/feature_gate_registry_spec.md (current)
findings: 11 blockers: 1
  narrative=100 structure=70 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/tools/llm/claude_full/feature_gate_registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/feature_gate_registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl:539:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should validate the bounded accepted Claude feature-gate registry' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl:539:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should validate the bounded accepted Claude feature-gate registry' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl:646:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve compact root metadata and conditional owner behavior' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl:646:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve compact root metadata and conditional owner behavior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl:667:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject duplicate ownerless and incomplete gate records' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl:667:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject duplicate ownerless and incomplete gate records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl:690:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject import-frontier owners without registry coverage in either direction' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/feature_gate_registry_spec.spl:690:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject import-frontier owners without registry coverage in either direction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
