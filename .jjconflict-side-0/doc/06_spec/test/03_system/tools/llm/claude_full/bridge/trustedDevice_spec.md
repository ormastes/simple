# Claude Full Bridge Trusted Device

> Mirrors trusted-device token gating, cache, clearing, enrollment, and request metadata.

<!-- sdn-diagram:id=trustedDevice_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=trustedDevice_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

trustedDevice_spec -> std
trustedDevice_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=trustedDevice_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors trusted-device token gating, cache, clearing, enrollment, and request metadata.

## Scenarios

### Claude full bridge trusted device

#### returns no token when the gate is off and reads env token first when on

- Gate token access and prefer env var
   - Expected: getTrustedDeviceToken(off) equals ``
   - Expected: env.getTrustedDeviceToken() equals `env-token`
   - Expected: env.storage.readToken() equals `stored`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Gate token access and prefer env var")
val off = trustedDeviceContextNew(false, "", "stored")
expect(getTrustedDeviceToken(off)).to_equal("")
val env = trustedDeviceContextNew(true, "env-token", "stored")
expect(env.getTrustedDeviceToken()).to_equal("env-token")
expect(env.storage.readToken()).to_equal("stored")
```

</details>

#### memoizes storage reads and clears the cache

- Read secure storage once until cache clear
   - Expected: ctx.getTrustedDeviceToken() equals `stored-a`
- ctx storage = TrustedDeviceStorage new
   - Expected: ctx.getTrustedDeviceToken() equals `stored-a`
- ctx clearTrustedDeviceTokenCache
   - Expected: ctx.getTrustedDeviceToken() equals `stored-b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Clear storage and memo cache during login
- off clearTrustedDeviceToken
   - Expected: off.storage.trustedDeviceToken equals `stored`
   - Expected: ctx.getTrustedDeviceToken() equals `stored`
- ctx clearTrustedDeviceToken
   - Expected: ctx.storage.trustedDeviceToken equals ``
   - Expected: ctx.getTrustedDeviceToken() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Return early without blocking login
- gateOff enrollTrustedDevice
- env enrollTrustedDevice
- auth enrollTrustedDevice
- privacy enrollTrustedDevice
- network enrollTrustedDevice


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Persist successful token and report failures
- ctx enrollTrustedDevice
   - Expected: ctx.storage.trustedDeviceToken equals `device-token`
- badStatus enrollTrustedDevice
- missing enrollTrustedDevice
- unreadable storage = TrustedDeviceStorage unreadable
- unreadable enrollTrustedDevice


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Expose constants and request values
- ctx enrollTrustedDevice
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

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
