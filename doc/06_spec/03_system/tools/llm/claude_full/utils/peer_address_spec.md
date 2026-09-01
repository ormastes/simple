# Claude Full peer address

> Pure Simple coverage for peer address scheme parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full peer address

Pure Simple coverage for peer address scheme parsing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/peer_address_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for peer address scheme parsing.

## Scenarios

### Claude full peer address

#### parses uds-prefixed addresses

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses uds-prefixed addresses
- Check UDS prefix
   - Expected: parsed.scheme equals `uds`
   - Expected: parsed.target equals `/tmp/simple.sock`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses uds-prefixed addresses")
step("Check UDS prefix")
val parsed = parseAddress("uds:/tmp/simple.sock")
expect(parsed.scheme).to_equal("uds")
expect(parsed.target).to_equal("/tmp/simple.sock")
```

</details>

#### parses bridge-prefixed addresses

- parses bridge-prefixed addresses
- Check bridge prefix
   - Expected: parsed.scheme equals `bridge`
   - Expected: parsed.target equals `session-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses bridge-prefixed addresses")
step("Check bridge prefix")
val parsed = parseAddress("bridge:session-1")
expect(parsed.scheme).to_equal("bridge")
expect(parsed.target).to_equal("session-1")
```

</details>

#### routes bare absolute paths through uds

- routes bare absolute paths through uds
- Check legacy UDS path
   - Expected: parsed.scheme equals `uds`
   - Expected: parsed.target equals `/tmp/simple.sock`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes bare absolute paths through uds")
step("Check legacy UDS path")
val parsed = parseAddress("/tmp/simple.sock")
expect(parsed.scheme).to_equal("uds")
expect(parsed.target).to_equal("/tmp/simple.sock")
```

</details>

#### leaves other addresses untouched

- leaves other addresses untouched
- Check fallback route
   - Expected: parsed.scheme equals `other`
   - Expected: parsed.target equals `session_manager`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves other addresses untouched")
step("Check fallback route")
val parsed = parseAddress("session_manager")
expect(parsed.scheme).to_equal("other")
expect(parsed.target).to_equal("session_manager")
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `536be2354797c981e03c2b592832863a0d7acc5ae7749c594008556e777ee5ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `536be2354797c981e03c2b592832863a0d7acc5ae7749c594008556e777ee5ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `536be2354797c981e03c2b592832863a0d7acc5ae7749c594008556e777ee5ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/peer_address_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/peer_address_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/peer_address_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/peer_address_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/peer_address_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses uds-prefixed addresses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/peer_address_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses bridge-prefixed addresses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/peer_address_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes bare absolute paths through uds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
