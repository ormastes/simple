# Claude Full model providers

> Pure Simple coverage for provider selection and first-party base URL checks.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full model providers

Pure Simple coverage for provider selection and first-party base URL checks.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/model/providers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for provider selection and first-party base URL checks.

## Scenarios

### Claude full model providers

#### selects API providers by upstream precedence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects API providers by upstream precedence
- Check provider precedence
   - Expected: getAPIProvider(Some("yes"), Some("1"), Some("on")) equals `bedrock`
   - Expected: getAPIProvider(nil, Some("TRUE"), nil) equals `vertex`
   - Expected: getAPIProvider(nil, Some(""), Some("on")) equals `foundry`
   - Expected: getAPIProvider(nil, nil, nil) equals `firstParty`
   - Expected: getAPIProviderForStatsig(nil, Some("true"), nil) equals `vertex`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects API providers by upstream precedence")
step("Check provider precedence")
expect(getAPIProvider(Some("yes"), Some("1"), Some("on"))).to_equal("bedrock")
expect(getAPIProvider(nil, Some("TRUE"), nil)).to_equal("vertex")
expect(getAPIProvider(nil, Some(""), Some("on"))).to_equal("foundry")
expect(getAPIProvider(nil, nil, nil)).to_equal("firstParty")
expect(getAPIProviderForStatsig(nil, Some("true"), nil)).to_equal("vertex")
```

</details>

#### accepts unset first-party base URLs

- accepts unset first-party base URLs
- Check default first-party URL
   - Expected: isFirstPartyAnthropicBaseUrl(nil, nil) is true
   - Expected: isFirstPartyAnthropicBaseUrl(Some(""), nil) is true
   - Expected: isFirstPartyAnthropicBaseUrl(Some("   "), nil) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts unset first-party base URLs")
step("Check default first-party URL")
expect(isFirstPartyAnthropicBaseUrl(nil, nil)).to_equal(true)
expect(isFirstPartyAnthropicBaseUrl(Some(""), nil)).to_equal(true)
expect(isFirstPartyAnthropicBaseUrl(Some("   "), nil)).to_equal(false)
```

</details>

#### accepts Anthropic API hosts only

- accepts Anthropic API hosts only
- Check allowed hosts
   - Expected: isFirstPartyAnthropicBaseUrl(Some("https://API.ANTHROPIC.COM/v1/messages"), nil) is true
   - Expected: isFirstPartyAnthropicBaseUrl(Some("https://api.anthropic.com:443/v1/messages"), nil) is true
   - Expected: isFirstPartyAnthropicBaseUrl(Some("https://api.anthropic.com:/v1/messages"), nil) is true
   - Expected: isFirstPartyAnthropicBaseUrl(Some("https://api-staging.anthropic.com/v1/messages"), Some("ant")) is true
   - Expected: isFirstPartyAnthropicBaseUrl(Some("https://api-staging.anthropic.com/v1/messages"), nil) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts Anthropic API hosts only")
step("Check allowed hosts")
expect(isFirstPartyAnthropicBaseUrl(Some("https://API.ANTHROPIC.COM/v1/messages"), nil)).to_equal(true)
expect(isFirstPartyAnthropicBaseUrl(Some("https://api.anthropic.com:443/v1/messages"), nil)).to_equal(true)
expect(isFirstPartyAnthropicBaseUrl(Some("https://api.anthropic.com:/v1/messages"), nil)).to_equal(true)
expect(isFirstPartyAnthropicBaseUrl(Some("https://api-staging.anthropic.com/v1/messages"), Some("ant"))).to_equal(true)
expect(isFirstPartyAnthropicBaseUrl(Some("https://api-staging.anthropic.com/v1/messages"), nil)).to_equal(false)
```

</details>

#### rejects invalid or non-first-party base URLs

- rejects invalid or non-first-party base URLs
- Check rejected hosts
   - Expected: isFirstPartyAnthropicBaseUrl(Some("://bad"), nil) is false
   - Expected: isFirstPartyAnthropicBaseUrl(Some("api.anthropic.com"), nil) is false
   - Expected: isFirstPartyAnthropicBaseUrl(Some("https://api.anthropic.com:444"), nil) is false
   - Expected: isFirstPartyAnthropicBaseUrl(Some("https://example.com"), Some("ant")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects invalid or non-first-party base URLs")
step("Check rejected hosts")
expect(isFirstPartyAnthropicBaseUrl(Some("://bad"), nil)).to_equal(false)
expect(isFirstPartyAnthropicBaseUrl(Some("api.anthropic.com"), nil)).to_equal(false)
expect(isFirstPartyAnthropicBaseUrl(Some("https://api.anthropic.com:444"), nil)).to_equal(false)
expect(isFirstPartyAnthropicBaseUrl(Some("https://example.com"), Some("ant"))).to_equal(false)
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

- Canonical SPipe generation for source `a672ddd7efc09865bce67d68fcd4937e4cc712abe1dfddc64649820998226c09`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a672ddd7efc09865bce67d68fcd4937e4cc712abe1dfddc64649820998226c09`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a672ddd7efc09865bce67d68fcd4937e4cc712abe1dfddc64649820998226c09`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/model/providers_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/model/providers_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/model/providers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/model/providers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/model/providers_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects API providers by upstream precedence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/model/providers_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts unset first-party base URLs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/model/providers_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts Anthropic API hosts only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
