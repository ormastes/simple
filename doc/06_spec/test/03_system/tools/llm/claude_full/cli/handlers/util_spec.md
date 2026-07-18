# Claude Full CLI Util Handlers

> Checks setup-token, doctor, and install subcommand behavior.

<!-- sdn-diagram:id=util_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=util_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

util_spec -> std
util_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=util_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CLI Util Handlers

Checks setup-token, doctor, and install subcommand behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/handlers/util_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks setup-token, doctor, and install subcommand behavior.

## Scenarios

### Claude full cli util handlers

#### renders setup token flow

- Setup token logs, renders OAuth flow, and warns when auth is already external
   - Expected: warned.screen equals `setupTokenModeName()`
   - Expected: warned.warningShown is true
   - Expected: warned.message equals `setupTokenStartingMessage()`
   - Expected: quiet.warningShown is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Setup token logs, renders OAuth flow, and warns when auth is already external")
val warned = setupTokenHandler(false)
expect(warned.screen).to_equal(setupTokenModeName())
expect(warned.events).to_contain(setupTokenEventName())
expect(warned.warningShown).to_equal(true)
expect(warned.message).to_equal(setupTokenStartingMessage())
val quiet = setupTokenHandler(true)
expect(quiet.warningShown).to_equal(false)
```

</details>

#### renders doctor with plugins and MCP manager

- Doctor logs and renders the plugin-aware wrapper
   - Expected: result.screen equals `doctor`
   - Expected: result.message equals `DoctorWithPlugins`
   - Expected: result.exitCode equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Doctor logs and renders the plugin-aware wrapper")
val result = doctorHandler()
expect(result.screen).to_equal("doctor")
expect(result.events).to_contain(doctorEventName())
expect(result.message).to_equal("DoctorWithPlugins")
expect(result.exitCode).to_equal(0)
```

</details>

#### builds install command arguments and exit code

- Target and force become args; failed output exits one
   - Expected: ok.setupCalled is true
   - Expected: ok.args equals `["stable", "--force"]`
   - Expected: ok.exitCode equals `0`
   - Expected: failed.args equals `[]`
   - Expected: failed.exitCode equals `1`
   - Expected: installArgs("nightly", false) equals `["nightly"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Target and force become args; failed output exits one")
val ok = installHandler("stable", true, "installed")
expect(ok.setupCalled).to_equal(true)
expect(ok.args).to_equal(["stable", "--force"])
expect(ok.exitCode).to_equal(0)
val failed = installHandler("", false, "failed to install")
expect(failed.args).to_equal([])
expect(failed.exitCode).to_equal(1)
expect(installArgs("nightly", false)).to_equal(["nightly"])
```

</details>

#### exports source-backed constants

- Pin helper flags from the TS handler
   - Expected: installSetupModeName() equals `default`
   - Expected: doctorUsesPluginManager() is true
   - Expected: doctorUsesSuspenseFallbackNull() is true
   - Expected: doctorUsesMcpConnectionManager() is true
   - Expected: doctorStrictMcpConfig() is false
   - Expected: setupTokenUsesAppStateOnChange() is true
   - Expected: setupTokenUsesKeybindingSetup() is true
   - Expected: setupTokenRendersWelcome() is true
   - Expected: installCallsSetupBeforeCommand() is true
   - Expected: installFailureExitCode() equals `1`
   - Expected: installSuccessExitCode() equals `0`
   - Expected: cliSubcommandsIntentionallyExit() is true
   - Expected: utilHandlerSourceLinesModeled() equals `109`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin helper flags from the TS handler")
expect(setupTokenWarningText()).to_contain("Warning:")
expect(installSetupModeName()).to_equal("default")
expect(doctorUsesPluginManager()).to_equal(true)
expect(doctorUsesSuspenseFallbackNull()).to_equal(true)
expect(doctorUsesMcpConnectionManager()).to_equal(true)
expect(doctorStrictMcpConfig()).to_equal(false)
expect(setupTokenUsesAppStateOnChange()).to_equal(true)
expect(setupTokenUsesKeybindingSetup()).to_equal(true)
expect(setupTokenRendersWelcome()).to_equal(true)
expect(installCallsSetupBeforeCommand()).to_equal(true)
expect(installFailureExitCode()).to_equal(1)
expect(installSuccessExitCode()).to_equal(0)
expect(cliSubcommandsIntentionallyExit()).to_equal(true)
expect(utilHandlerSourceLinesModeled()).to_equal(109)
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
