# Claude Full Bridge Trusted Device

> Mirrors trusted-device token gating, cache, clearing, enrollment, and request metadata.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge Trusted Device

Mirrors trusted-device token gating, cache, clearing, enrollment, and request metadata.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bridge/trustedDevice_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors trusted-device token gating, cache, clearing, enrollment, and request metadata.

## Scenarios

### Claude full bridge trusted device

#### returns no token when the gate is off and reads env token first when on

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns no token when the gate is off and reads env token first when on
- Gate token access and prefer env var
   - Expected: getTrustedDeviceToken(off) equals ``
   - Expected: env.getTrustedDeviceToken() equals `env-token`
   - Expected: env.storage.readToken() equals `stored`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns no token when the gate is off and reads env token first when on")
step("Gate token access and prefer env var")
val off = trustedDeviceContextNew(false, "", "stored")
expect(getTrustedDeviceToken(off)).to_equal("")
val env = trustedDeviceContextNew(true, "env-token", "stored")
expect(env.getTrustedDeviceToken()).to_equal("env-token")
expect(env.storage.readToken()).to_equal("stored")
```

</details>

#### memoizes storage reads and clears the cache

- memoizes storage reads and clears the cache
- Read secure storage once until cache clear
   - Expected: ctx.getTrustedDeviceToken() equals `stored-a`
   - Expected: ctx.getTrustedDeviceToken() equals `stored-a`
   - Expected: ctx.getTrustedDeviceToken() equals `stored-b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("memoizes storage reads and clears the cache")
step("Read secure storage once until cache clear")
val ctx = trustedDeviceContextNew(true, "", "stored-a")
expect(ctx.getTrustedDeviceToken()).to_equal("stored-a")
ctx.storage = TrustedDeviceStorage.new("stored-b")
expect(ctx.getTrustedDeviceToken()).to_equal("stored-a")
ctx.clearTrustedDeviceTokenCache()
expect(ctx.getTrustedDeviceToken()).to_equal("stored-b")
```

</details>

#### clears stored trusted device token only when gate is enabled

- clears stored trusted device token only when gate is enabled
- Clear storage and memo cache during login
   - Expected: off.storage.trustedDeviceToken equals `stored`
   - Expected: ctx.getTrustedDeviceToken() equals `stored`
   - Expected: ctx.storage.trustedDeviceToken equals ``
   - Expected: ctx.getTrustedDeviceToken() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clears stored trusted device token only when gate is enabled")
step("Clear storage and memo cache during login")
val off = trustedDeviceContextNew(false, "", "stored")
off.clearTrustedDeviceToken()
expect(off.storage.trustedDeviceToken).to_equal("stored")
val ctx = trustedDeviceContextNew(true, "", "stored")
expect(ctx.getTrustedDeviceToken()).to_equal("stored")
ctx.clearTrustedDeviceToken()
expect(ctx.storage.trustedDeviceToken).to_equal("")
expect(ctx.getTrustedDeviceToken()).to_equal("")
```

</details>

#### skips enrollment for gate, env, auth, privacy, and network preconditions

- skips enrollment for gate, env, auth, privacy, and network preconditions
- Return early without blocking login


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips enrollment for gate, env, auth, privacy, and network preconditions")
step("Return early without blocking login")
val gateOff = trustedDeviceContextNew(true, "", "")
gateOff.blockingGateEnabled = false
gateOff.enrollTrustedDevice(TrustedDeviceEnrollmentResponse.ok("tok", "dev"))
expect(gateOff.logs[0]).to_contain("Gate")
val env = trustedDeviceContextNew(true, "env-token", "")
env.enrollTrustedDevice(TrustedDeviceEnrollmentResponse.ok("tok", "dev"))
expect(env.logs[0]).to_contain("env var")
val auth = trustedDeviceContextNew(true, "", "")
auth.accessToken = ""
auth.enrollTrustedDevice(TrustedDeviceEnrollmentResponse.ok("tok", "dev"))
expect(auth.logs[0]).to_contain("No OAuth token")
val privacy = trustedDeviceContextNew(true, "", "")
privacy.essentialTrafficOnly = true
privacy.enrollTrustedDevice(TrustedDeviceEnrollmentResponse.ok("tok", "dev"))
expect(privacy.logs[0]).to_contain("Essential traffic only")
val network = trustedDeviceContextNew(true, "", "")
network.enrollTrustedDevice(TrustedDeviceEnrollmentResponse.network("down"))
expect(network.logs[0]).to_contain("request failed")
```

</details>

#### handles enrollment response and storage persistence

- handles enrollment response and storage persistence
- Persist successful token and report failures
   - Expected: ctx.storage.trustedDeviceToken equals `device-token`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles enrollment response and storage persistence")
step("Persist successful token and report failures")
val ctx = trustedDeviceContextNew(true, "", "")
ctx.enrollTrustedDevice(TrustedDeviceEnrollmentResponse.ok("device-token", "dev-1"))
expect(ctx.storage.trustedDeviceToken).to_equal("device-token")
expect(ctx.logs[0]).to_contain("dev-1")
val badStatus = trustedDeviceContextNew(true, "", "")
badStatus.enrollTrustedDevice(TrustedDeviceEnrollmentResponse.failed(403))
expect(badStatus.logs[0]).to_contain("Enrollment failed 403")
val missing = trustedDeviceContextNew(true, "", "")
missing.enrollTrustedDevice(TrustedDeviceEnrollmentResponse.ok("", "dev"))
expect(missing.logs[0]).to_contain("missing device_token")
val unreadable = trustedDeviceContextNew(true, "", "")
unreadable.storage = TrustedDeviceStorage.unreadable()
unreadable.enrollTrustedDevice(TrustedDeviceEnrollmentResponse.ok("tok", "dev"))
expect(unreadable.logs[0]).to_contain("Cannot read storage")
```

</details>

#### builds enrollment request metadata

- builds enrollment request metadata
- Expose constants and request values
   - Expected: ctx.lastRequest.url equals `https://api.anthropic.com/api/auth/trusted_devices`
   - Expected: ctx.lastRequest.display_name equals `trustedDeviceDisplayName("workstation", "linux")`
   - Expected: ctx.lastRequest.Authorization equals `trustedDeviceAuthHeader("oauth")`
   - Expected: ctx.lastRequest.Content_Type equals `trustedDeviceContentType()`
   - Expected: ctx.lastRequest.timeoutMs equals `trustedDeviceTimeoutMs()`
   - Expected: trustedDeviceGateName() equals `tengu_sessions_elevated_auth_enforcement`
   - Expected: trustedDeviceEnvVarName() equals `CLAUDE_TRUSTED_DEVICE_TOKEN`
   - Expected: trustedDevicePath() equals `/api/auth/trusted_devices`
   - Expected: trustedDeviceTtlDays() equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds enrollment request metadata")
step("Expose constants and request values")
val ctx = trustedDeviceContextNew(true, "", "")
ctx.host = "workstation"
ctx.platform = "linux"
ctx.enrollTrustedDevice(TrustedDeviceEnrollmentResponse.ok("tok", "dev"))
expect(ctx.lastRequest.url).to_equal("https://api.anthropic.com/api/auth/trusted_devices")
expect(ctx.lastRequest.display_name).to_equal(trustedDeviceDisplayName("workstation", "linux"))
expect(ctx.lastRequest.Authorization).to_equal(trustedDeviceAuthHeader("oauth"))
expect(ctx.lastRequest.Content_Type).to_equal(trustedDeviceContentType())
expect(ctx.lastRequest.timeoutMs).to_equal(trustedDeviceTimeoutMs())
expect(trustedDeviceGateName()).to_equal("tengu_sessions_elevated_auth_enforcement")
expect(trustedDeviceEnvVarName()).to_equal("CLAUDE_TRUSTED_DEVICE_TOKEN")
expect(trustedDevicePath()).to_equal("/api/auth/trusted_devices")
expect(trustedDeviceTtlDays()).to_equal(90)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `01ca96ee8efe9d5aaface97fe8a09828f9d02a3bb42aa2d28555f750d5b68f96`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `01ca96ee8efe9d5aaface97fe8a09828f9d02a3bb42aa2d28555f750d5b68f96`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `01ca96ee8efe9d5aaface97fe8a09828f9d02a3bb42aa2d28555f750d5b68f96`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/bridge/trustedDevice_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/bridge/trustedDevice_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/bridge/trustedDevice_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/bridge/trustedDevice_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/bridge/trustedDevice_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/bridge/trustedDevice_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns no token when the gate is off and reads env token first when on' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/trustedDevice_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'memoizes storage reads and clears the cache' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/trustedDevice_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clears stored trusted device token only when gate is enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
