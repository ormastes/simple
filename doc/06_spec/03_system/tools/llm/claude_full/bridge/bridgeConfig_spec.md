# Claude Full Bridge Config

> This parity slice covers the tiny but security-sensitive bridge resolver used before bridge API calls are made. The source exposes two override getters and two fallback getters. Overrides are valid only when `USER_TYPE` is `ant`; otherwise token resolution falls back to OAuth tokens and base URL resolution falls back to the production OAuth config.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge Config

This parity slice covers the tiny but security-sensitive bridge resolver used before bridge API calls are made. The source exposes two override getters and two fallback getters. Overrides are valid only when `USER_TYPE` is `ant`; otherwise token resolution falls back to OAuth tokens and base URL resolution falls back to the production OAuth config.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A - parity matrix slice for Claude full bridgeConfig. |
| Plan | N/A - owned single-file parity slice. |
| Design | N/A - direct mirror of `tmp/claude/claude-code-main/src/bridge/bridgeConfig.ts`. |
| Research | N/A - source file supplied by parity matrix. |
| Source | `test/03_system/tools/llm/claude_full/bridge/bridgeConfig_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This parity slice covers the tiny but security-sensitive bridge resolver used
before bridge API calls are made. The source exposes two override getters and
two fallback getters. Overrides are valid only when `USER_TYPE` is `ant`;
otherwise token resolution falls back to OAuth tokens and base URL resolution
falls back to the production OAuth config.

## Requirements

**Requirements:** N/A - parity matrix slice for Claude full bridgeConfig.
**Plan:** N/A - owned single-file parity slice.
**Design:** N/A - direct mirror of `tmp/claude/claude-code-main/src/bridge/bridgeConfig.ts`.
**Research:** N/A - source file supplied by parity matrix.

## Examples

Ant development:

- `USER_TYPE=ant`
- `CLAUDE_BRIDGE_OAUTH_TOKEN=dev-token`
- `CLAUDE_BRIDGE_BASE_URL=http://localhost:8787`
- access token resolves to `dev-token`
- base URL resolves to `http://localhost:8787`

Normal user:

- `USER_TYPE=customer`
- bridge override-shaped values are ignored
- access token resolves to OAuth token
- base URL resolves to OAuth config `BASE_API_URL`

## Scenarios

### Claude full bridge config

#### should expose ant-only token and base URL overrides

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose ant-only token and base URL overrides
- Create an ant bridge context with both CLAUDE_BRIDGE overrides
- Resolve override getters before OAuth/config fallbacks
   - Expected: getBridgeTokenOverrideFrom(ctx) == nil is false
   - Expected: getBridgeTokenOverrideFrom(ctx).unwrap() equals `dev-token`
   - Expected: getBridgeBaseUrlOverrideFrom(ctx) == nil is false
   - Expected: getBridgeBaseUrlOverrideFrom(ctx).unwrap() equals `http://localhost:8787`
   - Expected: getBridgeAccessTokenFrom(ctx).unwrap() equals `dev-token`
   - Expected: getBridgeBaseUrlFrom(ctx) equals `http://localhost:8787`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose ant-only token and base URL overrides")
step("Create an ant bridge context with both CLAUDE_BRIDGE overrides")
val ctx = bridgeConfigContextNew(
    "ant",
    "dev-token",
    "http://localhost:8787",
    "oauth-token",
    "https://api.anthropic.com"
)

step("Resolve override getters before OAuth/config fallbacks")
expect(getBridgeTokenOverrideFrom(ctx) == nil).to_equal(false)
expect(getBridgeTokenOverrideFrom(ctx).unwrap()).to_equal("dev-token")
expect(getBridgeBaseUrlOverrideFrom(ctx) == nil).to_equal(false)
expect(getBridgeBaseUrlOverrideFrom(ctx).unwrap()).to_equal("http://localhost:8787")
expect(getBridgeAccessTokenFrom(ctx).unwrap()).to_equal("dev-token")
expect(getBridgeBaseUrlFrom(ctx)).to_equal("http://localhost:8787")
```

</details>

#### should ignore bridge overrides for non-ant users

- should ignore bridge overrides for non-ant users
- Create a normal user context that still has override-shaped values
- Fall through to OAuth tokens and production config
   - Expected: getBridgeTokenOverrideFrom(ctx) == nil is true
   - Expected: getBridgeBaseUrlOverrideFrom(ctx) == nil is true
   - Expected: getBridgeAccessTokenFrom(ctx).unwrap() equals `oauth-token`
   - Expected: getBridgeBaseUrlFrom(ctx) equals `https://api.anthropic.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should ignore bridge overrides for non-ant users")
step("Create a normal user context that still has override-shaped values")
val ctx = bridgeConfigContextNew(
    "customer",
    "dev-token",
    "http://localhost:8787",
    "oauth-token",
    "https://api.anthropic.com"
)

step("Fall through to OAuth tokens and production config")
expect(getBridgeTokenOverrideFrom(ctx) == nil).to_equal(true)
expect(getBridgeBaseUrlOverrideFrom(ctx) == nil).to_equal(true)
expect(getBridgeAccessTokenFrom(ctx).unwrap()).to_equal("oauth-token")
expect(getBridgeBaseUrlFrom(ctx)).to_equal("https://api.anthropic.com")
```

</details>

#### should model logged-out token absence while always returning a base URL

- should model logged-out token absence while always returning a base URL
- Create an ant context without override or OAuth tokens
- Report missing access token and preserve config base URL
   - Expected: getBridgeTokenOverrideFrom(ctx) == nil is true
   - Expected: getBridgeAccessTokenFrom(ctx) == nil is true
   - Expected: getBridgeBaseUrlFrom(ctx) equals `https://console.anthropic.com/api`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model logged-out token absence while always returning a base URL")
step("Create an ant context without override or OAuth tokens")
val ctx = bridgeConfigContextNew(
    "ant",
    "",
    "",
    "",
    "https://console.anthropic.com/api"
)

step("Report missing access token and preserve config base URL")
expect(getBridgeTokenOverrideFrom(ctx) == nil).to_equal(true)
expect(getBridgeAccessTokenFrom(ctx) == nil).to_equal(true)
expect(getBridgeBaseUrlFrom(ctx)).to_equal("https://console.anthropic.com/api")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `N/A - parity matrix slice for Claude full bridgeConfig.`
- **Plan:** `N/A - owned single-file parity slice.`
- **Design:** `N/A - direct mirror of `tmp/claude/claude-code-main/src/bridge/bridgeConfig.ts`.`
- **Research:** `N/A - source file supplied by parity matrix.`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `db52ad319ec50e986d0d37822d7abbd9c70115966a798fd5c791d1057774a85b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db52ad319ec50e986d0d37822d7abbd9c70115966a798fd5c791d1057774a85b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db52ad319ec50e986d0d37822d7abbd9c70115966a798fd5c791d1057774a85b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/bridge/bridgeConfig_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/bridge/bridgeConfig_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/bridge/bridgeConfig_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/bridge/bridgeConfig_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/bridge/bridgeConfig_spec.spl:51:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose ant-only token and base URL overrides' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/bridge/bridgeConfig_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose ant-only token and base URL overrides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/bridgeConfig_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should ignore bridge overrides for non-ant users' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/bridge/bridgeConfig_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should ignore bridge overrides for non-ant users' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/bridgeConfig_spec.spl:89:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model logged-out token absence while always returning a base URL' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/bridge/bridgeConfig_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model logged-out token absence while always returning a base URL' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
