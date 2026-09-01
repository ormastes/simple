# @req REQ-SSPEC-UNIT

> SimpleOS sandbox lowering installation tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @req REQ-SSPEC-UNIT

SimpleOS sandbox lowering installation tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/ipc/sandbox_lowering_install_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

SimpleOS sandbox lowering installation tests.

Validates that generated sandbox_lowering capability handles become pledged
kernel CapabilitySet records instead of observational metadata.

## Scenarios

### CapabilityManager sandbox lowering installer

#### maps lowered capability handles into a pledged kernel capability set

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps lowered capability handles into a pledged kernel capability set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps lowered capability handles into a pledged kernel capability set")
var mgr = CapabilityManager.new()
val task = TaskId(id: 123)
val lowering = """
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5fd0c7e9dd4ca5072032210f902b480d954807d105d4cfb6da1f1da6b83d84bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5fd0c7e9dd4ca5072032210f902b480d954807d105d4cfb6da1f1da6b83d84bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5fd0c7e9dd4ca5072032210f902b480d954807d105d4cfb6da1f1da6b83d84bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/ipc/sandbox_lowering_install_spec.spl
mirror: doc/06_spec/unit/os/kernel/ipc/sandbox_lowering_install_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/ipc/sandbox_lowering_install_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/ipc/sandbox_lowering_install_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/ipc/sandbox_lowering_install_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps lowered capability handles into a pledged kernel capability set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/ipc/sandbox_lowering_install_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces ambient task authority with lowered sandbox capabilities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/ipc/sandbox_lowering_install_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed for baremetal MPU lowering when static linker section is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
