# Claude Full Hidden Stub Registry

> REQ-LLM-CARET-HIDDEN-008

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Hidden Stub Registry

REQ-LLM-CARET-HIDDEN-008

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/hidden_stub_registry_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

REQ-LLM-CARET-HIDDEN-008

Projects every claude_full parts-bin hidden-disabled stub descriptor into one neutral
registry and independently compares it with normalized source discovery.
Hyphen/underscore twins count as one logical capsule. This is parts-bin
metadata evidence, not shipped Caret command admission or current upstream
Claude parity.

## Scenarios

### Claude full hidden stub registry

### REQ-LLM-CARET-HIDDEN-008: hidden disabled stub inventory

#### derives every hidden disabled stub from claude_full leaf descriptors and matches normalized source discovery

- every hidden disabled stub is derived from claude_full leaf descriptors and matches normalized source discovery
- Load the parts-bin hidden-stub registry
- Check every hidden stub is disabled
   - Expected: check_hidden_stub_registry_contract(records) equals `complete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-LLM-CARET-HIDDEN-008
step("every hidden disabled stub is derived from claude_full leaf descriptors and matches normalized source discovery")
step("Load the parts-bin hidden-stub registry")
val records = setup_hidden_stub_registry_fixture()

step("Check every hidden stub is disabled")
expect(check_hidden_stub_registry_contract(records)).to_equal("complete")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `ad254fcca366c657ac49fccb64d8809241651c99b855e2363acbf17364b5c9b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ad254fcca366c657ac49fccb64d8809241651c99b855e2363acbf17364b5c9b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ad254fcca366c657ac49fccb64d8809241651c99b855e2363acbf17364b5c9b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/03_system/tools/llm/claude_full/commands/hidden_stub_registry_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/hidden_stub_registry_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/hidden_stub_registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/hidden_stub_registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/hidden_stub_registry_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives every hidden disabled stub from claude_full leaf descriptors and matches normalized source discovery' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
