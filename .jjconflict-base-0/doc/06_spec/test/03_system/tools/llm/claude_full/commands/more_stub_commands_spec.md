# Claude Full More Stub Commands

> Mirrors another batch of one-line Claude command index files that export hidden

<!-- sdn-diagram:id=more_stub_commands_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=more_stub_commands_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

more_stub_commands_spec -> std
more_stub_commands_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=more_stub_commands_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full More Stub Commands

Mirrors another batch of one-line Claude command index files that export hidden

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/more_stub_commands_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors another batch of one-line Claude command index files that export hidden
disabled stub commands.

## Scenarios

### Claude full additional stub command indexes

#### should expose hidden disabled cache, context, and good-claude commands

- Load the first additional stub command batch
- assert stub
- assert stub
- assert stub


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load the first additional stub command batch")
val break_cache = breakCacheCommand()
val ctx = ctxVizCommand()
val good = goodClaudeCommand()

assert_stub(break_cache.name, break_cache.isHidden, break_cache.isEnabled())
assert_stub(ctx.name, ctx.isHidden, ctx.isEnabled())
assert_stub(good.name, good.isHidden, good.isEnabled())
```

</details>

#### should expose hidden disabled limit, oauth, and perf commands

- Load the second additional stub command batch
- assert stub
- assert stub
- assert stub


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load the second additional stub command batch")
val mock_limits = mockLimitsCommand()
val oauth = oauthRefreshCommand()
val perf = perfIssueCommand()

assert_stub(mock_limits.name, mock_limits.isHidden, mock_limits.isEnabled())
assert_stub(oauth.name, oauth.isHidden, oauth.isEnabled())
assert_stub(perf.name, perf.isHidden, perf.isEnabled())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
