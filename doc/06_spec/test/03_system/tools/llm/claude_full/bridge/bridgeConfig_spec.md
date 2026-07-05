# Claude Full Bridge Config

> This parity slice covers the tiny but security-sensitive bridge resolver used before bridge API calls are made. The source exposes two override getters and two fallback getters. Overrides are valid only when `USER_TYPE` is `ant`; otherwise token resolution falls back to OAuth tokens and base URL resolution falls back to the production OAuth config.

<!-- sdn-diagram:id=bridgeConfig_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bridgeConfig_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bridgeConfig_spec -> std
bridgeConfig_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bridgeConfig_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
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

- Create an ant bridge context with both CLAUDE_BRIDGE overrides
- Resolve override getters before OAuth/config fallbacks
   - Expected: getBridgeTokenOverrideFrom(ctx).? is true
   - Expected: getBridgeTokenOverrideFrom(ctx).unwrap() equals `dev-token`
   - Expected: getBridgeBaseUrlOverrideFrom(ctx).? is true
   - Expected: getBridgeBaseUrlOverrideFrom(ctx).unwrap() equals `http://localhost:8787`
   - Expected: getBridgeAccessTokenFrom(ctx).unwrap() equals `dev-token`
   - Expected: getBridgeBaseUrlFrom(ctx) equals `http://localhost:8787`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create an ant bridge context with both CLAUDE_BRIDGE overrides")
val ctx = bridgeConfigContextNew(
    "ant",
    "dev-token",
    "http://localhost:8787",
    "oauth-token",
    "https://api.anthropic.com"
)

step("Resolve override getters before OAuth/config fallbacks")
expect(getBridgeTokenOverrideFrom(ctx).?).to_equal(true)
expect(getBridgeTokenOverrideFrom(ctx).unwrap()).to_equal("dev-token")
expect(getBridgeBaseUrlOverrideFrom(ctx).?).to_equal(true)
expect(getBridgeBaseUrlOverrideFrom(ctx).unwrap()).to_equal("http://localhost:8787")
expect(getBridgeAccessTokenFrom(ctx).unwrap()).to_equal("dev-token")
expect(getBridgeBaseUrlFrom(ctx)).to_equal("http://localhost:8787")
```

</details>

#### should ignore bridge overrides for non-ant users

- Create a normal user context that still has override-shaped values
- Fall through to OAuth tokens and production config
   - Expected: getBridgeTokenOverrideFrom(ctx).? is false
   - Expected: getBridgeBaseUrlOverrideFrom(ctx).? is false
   - Expected: getBridgeAccessTokenFrom(ctx).unwrap() equals `oauth-token`
   - Expected: getBridgeBaseUrlFrom(ctx) equals `https://api.anthropic.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a normal user context that still has override-shaped values")
val ctx = bridgeConfigContextNew(
    "customer",
    "dev-token",
    "http://localhost:8787",
    "oauth-token",
    "https://api.anthropic.com"
)

step("Fall through to OAuth tokens and production config")
expect(getBridgeTokenOverrideFrom(ctx).?).to_equal(false)
expect(getBridgeBaseUrlOverrideFrom(ctx).?).to_equal(false)
expect(getBridgeAccessTokenFrom(ctx).unwrap()).to_equal("oauth-token")
expect(getBridgeBaseUrlFrom(ctx)).to_equal("https://api.anthropic.com")
```

</details>

#### should model logged-out token absence while always returning a base URL

- Create an ant context without override or OAuth tokens
- Report missing access token and preserve config base URL
   - Expected: getBridgeTokenOverrideFrom(ctx).? is false
   - Expected: getBridgeAccessTokenFrom(ctx).? is false
   - Expected: getBridgeBaseUrlFrom(ctx) equals `https://console.anthropic.com/api`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create an ant context without override or OAuth tokens")
val ctx = bridgeConfigContextNew(
    "ant",
    "",
    "",
    "",
    "https://console.anthropic.com/api"
)

step("Report missing access token and preserve config base URL")
expect(getBridgeTokenOverrideFrom(ctx).?).to_equal(false)
expect(getBridgeAccessTokenFrom(ctx).?).to_equal(false)
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

- **Requirements:** [N/A - parity matrix slice for Claude full bridgeConfig.](N/A - parity matrix slice for Claude full bridgeConfig.)
- **Plan:** [N/A - owned single-file parity slice.](N/A - owned single-file parity slice.)
- **Design:** [N/A - direct mirror of `tmp/claude/claude-code-main/src/bridge/bridgeConfig.ts`.](N/A - direct mirror of `tmp/claude/claude-code-main/src/bridge/bridgeConfig.ts`.)
- **Research:** [N/A - source file supplied by parity matrix.](N/A - source file supplied by parity matrix.)


</details>
