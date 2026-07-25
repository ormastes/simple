# Claude Full Security Review Command

> Checks modern SSpec parity for the security-review command.

<!-- sdn-diagram:id=security_review_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=security_review_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

security_review_spec -> std
security_review_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=security_review_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Security Review Command

Checks modern SSpec parity for the security-review command.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/security_review_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the security-review command.

## Scenarios

### Claude full security-review command

#### should expose command metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = securityReviewSource()
expect(source).to_contain("name: \"security-review\"")
expect(source).to_contain("Review code for security vulnerabilities")
expect(source).to_contain("argumentHint: \"[path]\"")
expect(source).to_contain("supportsNonInteractive: true")
expect(source).to_contain("[\"Read\", \"Grep\", \"Glob\"]")
```

</details>

#### should default to the workspace target

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = securityReviewSource()
expect(source).to_contain("return \".\"")
expect(source).to_contain("Focus on injection, auth, secrets")
expect(source).to_contain("unsafe file/process access")
expect(source).to_contain("confirmed issues")
```

</details>

#### should review an explicit target and gate untrusted workspaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = securityReviewSource()
expect(source).to_contain("trimmed")
expect(source).to_contain("command.allowedTools")
expect(source).to_contain("queued security review")
expect(source).to_contain("not workspaceTrusted")
expect(source).to_contain("requires a trusted workspace")
```

</details>

#### should expose source size parity

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = securityReviewSource()
expect(source.split("\n").len()).to_be_greater_than(242)
expect(source).to_contain("fn securityReviewSourceLinesModeled() -> i64:")
expect(source).to_contain("243")
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
