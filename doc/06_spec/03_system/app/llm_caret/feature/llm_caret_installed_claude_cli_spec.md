# LLM Caret Installed Claude CLI Compatibility

> Probe the currently installed Claude CLI without sending a prompt or allowing

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Installed Claude CLI Compatibility

Probe the currently installed Claude CLI without sending a prompt or allowing

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Plan | doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scope

Probe the currently installed Claude CLI without sending a prompt or allowing
provider credentials into the child environment. The checker records the
resolved executable, canonical target, version, SHA-256, raw stdout, raw
stderr, and exit status under:

`build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli/`

The cases prove current help compatibility, variadic `--allowedTools`,
rejection of missing print input, acceptance of the help-hidden `--max-turns`
option, and safe rejection of the removed `--max-tokens` option. Version and
hash are recorded as drift evidence; this specification does not pin their
exact values.

No case contains a prompt-bearing success path, authenticates, resumes a
session, or accepts a provider response. A missing installed binary fails closed.
This is supplemental environmental compatibility evidence; it does not replace
the requirement's direct production-declaration scenarios.

## Scenarios

### LLM Caret installed Claude CLI compatibility

### REQ-LLM-CARET-CLI-HARDEN-006: installed Claude CLI contract

#### should resolve the installed executable and recorded provenance
#### should record the current version without pinning release drift

- should record the current version without pinning release drift
- Load the accepted Claude feature map
- Invoke the installed Claude CLI with no prompt or provider credentials
- Check the structured CLI response
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should record the current version without pinning release drift")
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
expect(result.exit_code).to_equal(0)
check_probe_artifacts("version")
```

</details>

#### should advertise every required current flag and variadic allowed tools

- should advertise every required current flag and variadic allowed tools
- Load the accepted Claude feature map
- Invoke the installed Claude CLI with no prompt or provider credentials
- Check the structured CLI response
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should advertise every required current flag and variadic allowed tools")
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
expect(result.exit_code).to_equal(0)
check_probe_artifacts("help")
```

</details>

#### should reject missing print input without a prompt-bearing provider path

- should reject missing print input without a prompt-bearing provider path
- Load the accepted Claude feature map
- Invoke the installed Claude CLI with no prompt or provider credentials
- Check the structured CLI response
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing print input without a prompt-bearing provider path")
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
expect(result.exit_code).to_equal(0)
check_probe_artifacts("missing-input")
```

</details>

#### should safely reject the removed maximum-token option

- should safely reject the removed maximum-token option
- Load the accepted Claude feature map
- Invoke the installed Claude CLI with no prompt or provider credentials
- Check the structured CLI response
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should safely reject the removed maximum-token option")
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
expect(result.exit_code).to_equal(0)
check_probe_artifacts("removed-option")
```

</details>

#### should accept the hidden maximum-turn option without a prompt

- should accept the hidden maximum-turn option without a prompt
- Load the accepted Claude feature map
- Invoke the installed Claude CLI with no prompt or provider credentials
- Check the structured CLI response
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept the hidden maximum-turn option without a prompt")
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
expect(result.exit_code).to_equal(0)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-CLI-HARDEN-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7c3061ec921c8f36465617970af31c5973275ba135e254226995d45bf017ca7d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7c3061ec921c8f36465617970af31c5973275ba135e254226995d45bf017ca7d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7c3061ec921c8f36465617970af31c5973275ba135e254226995d45bf017ca7d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **74/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.md (current)
findings: 14 blockers: 1
  narrative=100 structure=60 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=74; blocker cap makes effective=49
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:79:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should resolve the installed executable and recorded provenance' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:79:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should resolve the installed executable and recorded provenance' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:106:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should record the current version without pinning release drift' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should record the current version without pinning release drift' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:124:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should advertise every required current flag and variadic allowed tools' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should advertise every required current flag and variadic allowed tools' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:147:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing print input without a prompt-bearing provider path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject missing print input without a prompt-bearing provider path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:165:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should safely reject the removed maximum-token option' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl:185:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept the hidden maximum-turn option without a prompt' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
