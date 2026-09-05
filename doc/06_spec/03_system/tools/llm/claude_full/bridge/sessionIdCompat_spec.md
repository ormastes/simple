# Claude Full Bridge Session ID Compat

> Checks CCR v2 session tag translation without importing bridge-enabled gates.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge Session ID Compat

Checks CCR v2 session tag translation without importing bridge-enabled gates.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bridge/sessionIdCompat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks CCR v2 session tag translation without importing bridge-enabled gates.

## Scenarios

### Claude full bridge session id compat

#### retags cse ids to compat session ids when the shim is active

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- retags cse ids to compat session ids when the shim is active
- Default gate is active when no bridgeEnabled import registers it
   - Expected: toCompatSessionId("cse_abc") equals `session_abc`
   - Expected: toCompatSessionId("other_abc") equals `other_abc`
   - Expected: toCompatSessionIdWithGate("cse_abc", defaultCseShimGate()) equals `session_abc`
   - Expected: toCompatSessionIdWithGate("cse_abc", setCseShimGate(true)) equals `session_abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retags cse ids to compat session ids when the shim is active")
step("Default gate is active when no bridgeEnabled import registers it")
expect(toCompatSessionId("cse_abc")).to_equal("session_abc")
expect(toCompatSessionId("other_abc")).to_equal("other_abc")
expect(toCompatSessionIdWithGate("cse_abc", defaultCseShimGate())).to_equal("session_abc")
expect(toCompatSessionIdWithGate("cse_abc", setCseShimGate(true))).to_equal("session_abc")
```

</details>

#### leaves cse ids unchanged when the registered gate is off

- leaves cse ids unchanged when the registered gate is off
- Injected GrowthBook gate can disable the compat shim
   - Expected: cseShimGateRegistered(gate) is true
   - Expected: cseShimGateEnabled(gate) is false
   - Expected: toCompatSessionIdWithGate("cse_abc", gate) equals `cse_abc`
   - Expected: shouldRetagForCompat("cse_abc", gate) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves cse ids unchanged when the registered gate is off")
step("Injected GrowthBook gate can disable the compat shim")
val gate = setCseShimGate(false)
expect(cseShimGateRegistered(gate)).to_equal(true)
expect(cseShimGateEnabled(gate)).to_equal(false)
expect(toCompatSessionIdWithGate("cse_abc", gate)).to_equal("cse_abc")
expect(shouldRetagForCompat("cse_abc", gate)).to_equal(false)
```

</details>

#### retags compat session ids to infra cse ids

- retags compat session ids to infra cse ids
- Reconnect and worker calls need infrastructure tags
   - Expected: toInfraSessionId("session_abc") equals `cse_abc`
   - Expected: toInfraSessionId("cse_abc") equals `cse_abc`
   - Expected: toInfraSessionIdForReconnect("session_abc") equals `cse_abc`
   - Expected: shouldRetagForInfra("session_abc") is true
   - Expected: shouldRetagForInfra("cse_abc") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retags compat session ids to infra cse ids")
step("Reconnect and worker calls need infrastructure tags")
expect(toInfraSessionId("session_abc")).to_equal("cse_abc")
expect(toInfraSessionId("cse_abc")).to_equal("cse_abc")
expect(toInfraSessionIdForReconnect("session_abc")).to_equal("cse_abc")
expect(shouldRetagForInfra("session_abc")).to_equal(true)
expect(shouldRetagForInfra("cse_abc")).to_equal(false)
```

</details>

#### preserves the UUID portion across both tags

- preserves the UUID portion across both tags
- Same UUID, different compatibility costume
   - Expected: sameUuidDifferentTag("cse_abc") is true
   - Expected: sameUuidDifferentTag("session_abc") is false
   - Expected: roundTripSessionId("cse_abc") equals `cse_abc`
   - Expected: toCompatSessionIdForArchive("cse_abc") equals `session_abc`
   - Expected: toCompatSessionIdForEvents("cse_abc") equals `session_abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves the UUID portion across both tags")
step("Same UUID, different compatibility costume")
expect(sameUuidDifferentTag("cse_abc")).to_equal(true)
expect(sameUuidDifferentTag("session_abc")).to_equal(false)
expect(roundTripSessionId("cse_abc")).to_equal("cse_abc")
expect(toCompatSessionIdForArchive("cse_abc")).to_equal("session_abc")
expect(toCompatSessionIdForEvents("cse_abc")).to_equal("session_abc")
```

</details>

#### exports source-backed prefixes and endpoint roles

- exports source-backed prefixes and endpoint roles
- Document which API layer expects each tag
   - Expected: csePrefix() equals `cse_`
   - Expected: sessionPrefix() equals `session_`
   - Expected: compatEndpointFamily() equals `/v1/sessions/<id>`
   - Expected: workerEndpointFamily() equals `/v1/code/sessions/<id>/worker/*`
   - Expected: reconnectEndpointFamily() equals `/v1/environments/<id>/bridge/reconnect`
   - Expected: compatTagName() equals `TagSession`
   - Expected: infraTagName() equals `cse`
   - Expected: sdkBundleAvoidsBridgeEnabledImport() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed prefixes and endpoint roles")
step("Document which API layer expects each tag")
expect(csePrefix()).to_equal("cse_")
expect(sessionPrefix()).to_equal("session_")
expect(compatEndpointFamily()).to_equal("/v1/sessions/<id>")
expect(workerEndpointFamily()).to_equal("/v1/code/sessions/<id>/worker/*")
expect(reconnectEndpointFamily()).to_equal("/v1/environments/<id>/bridge/reconnect")
expect(compatTagName()).to_equal("TagSession")
expect(infraTagName()).to_equal("cse")
expect(shimDefaultActiveReason()).to_contain("defaults active")
expect(sdkBundleAvoidsBridgeEnabledImport()).to_equal(true)
expect(sessionIdCompatModulePurpose()).to_contain("CCR v2 compat")
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `42c6f4f0d5c935300f9ff6b7a596033acd9b1a3fa379bace35ada151d50070de`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `42c6f4f0d5c935300f9ff6b7a596033acd9b1a3fa379bace35ada151d50070de`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `42c6f4f0d5c935300f9ff6b7a596033acd9b1a3fa379bace35ada151d50070de`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/bridge/sessionIdCompat_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/bridge/sessionIdCompat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/bridge/sessionIdCompat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/bridge/sessionIdCompat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/bridge/sessionIdCompat_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retags cse ids to compat session ids when the shim is active' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/sessionIdCompat_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves cse ids unchanged when the registered gate is off' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/sessionIdCompat_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retags compat session ids to infra cse ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
