# LLM Caret Installed Claude CLI Compatibility

> Verifies the llm caret installed claude cli behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Installed Claude CLI Compatibility

Verifies the llm caret installed claude cli behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Plan | doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the llm caret installed claude cli behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### LLM Caret installed Claude CLI compatibility

### REQ-LLM-CARET-CLI-HARDEN-006: installed Claude CLI contract

#### should resolve the installed executable and recorded provenance

- Verify: should resolve the installed executable and recorded provenance
- Load the accepted Claude feature map
- Invoke the installed Claude CLI with no prompt or provider credentials
- Check the structured CLI response
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-CLI-HARDEN-006
step("Verify: should resolve the installed executable and recorded provenance")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the accepted Claude feature map")
check_feature_map()

step("Invoke the installed Claude CLI with no prompt or provider credentials")
val result = probe_current_claude_cli("prerequisites")

step("Check the structured CLI response")
expect(result.stdout).to_contain(
    "case=prerequisites status=PASS"
)
expect(result.stdout).to_contain("claude_path=")
expect(result.stdout).to_contain("claude_canonical_target=")
expect(result.stdout).to_contain("claude_sha256=")
expect(result.stdout).to_contain("prompt_submitted=false")
expect(result.stdout).to_contain(
    "provider_credentials_inherited=false"
)
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.stdout).to_contain(ARTIFACT_ROOT)
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
check_probe_artifacts("prerequisites")
```

</details>

#### should record the current version without pinning release drift

- Verify: should record the current version without pinning release drift
- Load the accepted Claude feature map
- Invoke the installed Claude CLI with no prompt or provider credentials
- Check the structured CLI response
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-CLI-HARDEN-006
step("Verify: should record the current version without pinning release drift")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the accepted Claude feature map")
check_feature_map()

step("Invoke the installed Claude CLI with no prompt or provider credentials")
val result = probe_current_claude_cli("version")

step("Check the structured CLI response")
expect(result.stdout).to_contain("case=version status=PASS")
expect(result.stdout).to_contain("claude_version=")
expect(result.stdout).to_contain("version_recorded=true")
expect(result.stdout).to_contain("raw_exit=0")
expect(result.stdout).to_contain("prompt_submitted=false")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
check_probe_artifacts("version")
```

</details>

#### should advertise every required current flag and variadic allowed tools

- Verify: should advertise every required current flag and variadic allowed tools
- Load the accepted Claude feature map
- Invoke the installed Claude CLI with no prompt or provider credentials
- Check the structured CLI response
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-CLI-HARDEN-006
step("Verify: should advertise every required current flag and variadic allowed tools")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the accepted Claude feature map")
check_feature_map()

step("Invoke the installed Claude CLI with no prompt or provider credentials")
val result = probe_current_claude_cli("help")

step("Check the structured CLI response")
expect(result.stdout).to_contain("case=help status=PASS")
expect(result.stdout).to_contain("required_flags=present")
expect(result.stdout).to_contain("allowed_tools_variadic=true")
expect(result.stdout).to_contain(
    "removed_max_tokens_absent=true"
)
expect(result.stdout).to_contain(
    "hidden_max_turns_absent=true"
)
expect(result.stdout).to_contain("prompt_submitted=false")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
check_probe_artifacts("help")
```

</details>

#### should reject missing print input without a prompt-bearing provider path

- Verify: should reject missing print input without a prompt-bearing provider path
- Load the accepted Claude feature map
- Invoke the installed Claude CLI with no prompt or provider credentials
- Check the structured CLI response
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-CLI-HARDEN-006
step("Verify: should reject missing print input without a prompt-bearing provider path")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the accepted Claude feature map")
check_feature_map()

step("Invoke the installed Claude CLI with no prompt or provider credentials")
val result = probe_current_claude_cli("missing-input")

step("Check the structured CLI response")
expect(result.stdout).to_contain(
    "case=missing-input status=PASS"
)
expect(result.stdout).to_contain("input_rejected=true")
expect(result.stdout).to_contain("prompt_submitted=false")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
check_probe_artifacts("missing-input")
```

</details>

#### should safely reject the removed maximum-token option

- Verify: should safely reject the removed maximum-token option
- Load the accepted Claude feature map
- Invoke the installed Claude CLI with no prompt or provider credentials
- Check the structured CLI response
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-CLI-HARDEN-006
step("Verify: should safely reject the removed maximum-token option")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the accepted Claude feature map")
check_feature_map()

step("Invoke the installed Claude CLI with no prompt or provider credentials")
val result = probe_current_claude_cli("removed-option")

step("Check the structured CLI response")
expect(result.stdout).to_contain(
    "case=removed-option status=PASS"
)
expect(result.stdout).to_contain(
    "removed_option_rejected=true"
)
expect(result.stdout).to_contain("prompt_submitted=false")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
check_probe_artifacts("removed-option")
```

</details>

#### should accept the hidden maximum-turn option without a prompt

- Verify: should accept the hidden maximum-turn option without a prompt
- Load the accepted Claude feature map
- Invoke the installed Claude CLI with no prompt or provider credentials
- Check the structured CLI response
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-CLI-HARDEN-006
step("Verify: should accept the hidden maximum-turn option without a prompt")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the accepted Claude feature map")
check_feature_map()

step("Invoke the installed Claude CLI with no prompt or provider credentials")
val result = probe_current_claude_cli("hidden-max-turns")

step("Check the structured CLI response")
expect(result.stdout).to_contain(
    "case=hidden-max-turns status=PASS"
)
expect(result.stdout).to_contain(
    "hidden_max_turns_accepted=true"
)
expect(result.stdout).to_contain("input_rejected=true")
expect(result.stdout).to_contain("prompt_submitted=false")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
check_probe_artifacts("hidden-max-turns")
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


## Related Documentation

- **Plan:** `doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9581191fbe5a3d6165c0711815a5df81d1b4ba5dbea1ab8a611f871508122580`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9581191fbe5a3d6165c0711815a5df81d1b4ba5dbea1ab8a611f871508122580`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9581191fbe5a3d6165c0711815a5df81d1b4ba5dbea1ab8a611f871508122580`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:89:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should resolve the installed executable and recorded provenance' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:115:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should record the current version without pinning release drift' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:134:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should advertise every required current flag and variadic allowed tools' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:158:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing print input without a prompt-bearing provider path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:177:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should safely reject the removed maximum-token option' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:198:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept the hidden maximum-turn option without a prompt' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
