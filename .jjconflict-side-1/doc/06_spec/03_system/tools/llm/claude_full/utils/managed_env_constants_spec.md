# Claude Full Managed Environment Constants

> Verifies provider-managed, dangerous-shell, safe, and experimental
> hidden-feature environment-key classifications without reading the host
> environment.

| Tests | Active | Skipped | Pending | Executed |
|------:|-------:|--------:|--------:|---------:|
| 5 | 5 | 0 | 0 | 0 |

The executable source is
`test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl`.
This manual is synchronized from that source. The current self-hosted SSpec
runner is blocked before scenario execution, so the scenarios below are
designed evidence rather than a runtime PASS.

## Scenarios

### should detect provider-managed env vars case-insensitively

- Classify lowercase and uppercase provider keys.
- Reject an unrelated process key.

<details>
<summary>Executable SSpec</summary>

```simple
expect(isProviderManagedEnvVar("anthropic_model")).to_be(true)
expect(isProviderManagedEnvVar("CLAUDE_CODE_USE_VERTEX")).to_be(true)
expect(isProviderManagedEnvVar("PATH")).to_be(false)
```

</details>

### should detect Vertex region overrides by prefix

- Classify future model-region keys through the managed prefix.

<details>
<summary>Executable SSpec</summary>

```simple
expect(
    isProviderManagedEnvVar("vertex_region_claude_future_model")
).to_be(true)
```

</details>

### should keep dangerous shell settings available

- Preserve the API-key helper and status-line shell settings.

<details>
<summary>Executable SSpec</summary>

```simple
expect(dangerousShellSettings()).to_contain("apiKeyHelper")
expect(dangerousShellSettings()).to_contain("statusLine")
```

</details>

### should keep representative safe env vars available

- Preserve custom headers, MCP limits, and pinned Vertex-region keys.

<details>
<summary>Executable SSpec</summary>

```simple
expect(safeEnvVars()).to_contain("ANTHROPIC_CUSTOM_HEADERS")
expect(safeEnvVars()).to_contain("MAX_MCP_OUTPUT_TOKENS")
expect(safeEnvVars()).to_contain("VERTEX_REGION_CLAUDE_4_5_SONNET")
```

</details>

### should expose experimental hidden-feature gates only as safe env vars

- Preserve the experimental-beta disable and agent-team keys.
- Keep both out of provider-managed classification.

<details>
<summary>Executable SSpec</summary>

```simple
val safe = safeEnvVars()
expect(safe).to_contain("CLAUDE_CODE_DISABLE_EXPERIMENTAL_BETAS")
expect(safe).to_contain("CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS")
expect(isProviderManagedEnvVar(
    "CLAUDE_CODE_DISABLE_EXPERIMENTAL_BETAS"
)).to_be(false)
expect(isProviderManagedEnvVar(
    "CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS"
)).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
| Executed scenarios | 0 |

