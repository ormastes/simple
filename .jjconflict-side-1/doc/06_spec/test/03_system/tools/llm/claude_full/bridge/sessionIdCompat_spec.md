# Claude Full Bridge Session ID Compat

> Checks CCR v2 session tag translation without importing bridge-enabled gates.

<!-- sdn-diagram:id=sessionIdCompat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sessionIdCompat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sessionIdCompat_spec -> std
sessionIdCompat_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sessionIdCompat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks CCR v2 session tag translation without importing bridge-enabled gates.

## Scenarios

### Claude full bridge session id compat

#### retags cse ids to compat session ids when the shim is active

- Default gate is active when no bridgeEnabled import registers it
   - Expected: toCompatSessionId("cse_abc") equals `session_abc`
   - Expected: toCompatSessionId("other_abc") equals `other_abc`
   - Expected: toCompatSessionIdWithGate("cse_abc", defaultCseShimGate()) equals `session_abc`
   - Expected: toCompatSessionIdWithGate("cse_abc", setCseShimGate(true)) equals `session_abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Default gate is active when no bridgeEnabled import registers it")
expect(toCompatSessionId("cse_abc")).to_equal("session_abc")
expect(toCompatSessionId("other_abc")).to_equal("other_abc")
expect(toCompatSessionIdWithGate("cse_abc", defaultCseShimGate())).to_equal("session_abc")
expect(toCompatSessionIdWithGate("cse_abc", setCseShimGate(true))).to_equal("session_abc")
```

</details>

#### leaves cse ids unchanged when the registered gate is off

- Injected GrowthBook gate can disable the compat shim
   - Expected: cseShimGateRegistered(gate) is true
   - Expected: cseShimGateEnabled(gate) is false
   - Expected: toCompatSessionIdWithGate("cse_abc", gate) equals `cse_abc`
   - Expected: shouldRetagForCompat("cse_abc", gate) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Injected GrowthBook gate can disable the compat shim")
val gate = setCseShimGate(false)
expect(cseShimGateRegistered(gate)).to_equal(true)
expect(cseShimGateEnabled(gate)).to_equal(false)
expect(toCompatSessionIdWithGate("cse_abc", gate)).to_equal("cse_abc")
expect(shouldRetagForCompat("cse_abc", gate)).to_equal(false)
```

</details>

#### retags compat session ids to infra cse ids

- Reconnect and worker calls need infrastructure tags
   - Expected: toInfraSessionId("session_abc") equals `cse_abc`
   - Expected: toInfraSessionId("cse_abc") equals `cse_abc`
   - Expected: toInfraSessionIdForReconnect("session_abc") equals `cse_abc`
   - Expected: shouldRetagForInfra("session_abc") is true
   - Expected: shouldRetagForInfra("cse_abc") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reconnect and worker calls need infrastructure tags")
expect(toInfraSessionId("session_abc")).to_equal("cse_abc")
expect(toInfraSessionId("cse_abc")).to_equal("cse_abc")
expect(toInfraSessionIdForReconnect("session_abc")).to_equal("cse_abc")
expect(shouldRetagForInfra("session_abc")).to_equal(true)
expect(shouldRetagForInfra("cse_abc")).to_equal(false)
```

</details>

#### preserves the UUID portion across both tags

- Same UUID, different compatibility costume
   - Expected: sameUuidDifferentTag("cse_abc") is true
   - Expected: sameUuidDifferentTag("session_abc") is false
   - Expected: roundTripSessionId("cse_abc") equals `cse_abc`
   - Expected: toCompatSessionIdForArchive("cse_abc") equals `session_abc`
   - Expected: toCompatSessionIdForEvents("cse_abc") equals `session_abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Same UUID, different compatibility costume")
expect(sameUuidDifferentTag("cse_abc")).to_equal(true)
expect(sameUuidDifferentTag("session_abc")).to_equal(false)
expect(roundTripSessionId("cse_abc")).to_equal("cse_abc")
expect(toCompatSessionIdForArchive("cse_abc")).to_equal("session_abc")
expect(toCompatSessionIdForEvents("cse_abc")).to_equal("session_abc")
```

</details>

#### exports source-backed prefixes and endpoint roles

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

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
