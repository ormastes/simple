# Claude Full Auth and Keybindings Commands

> Checks modern SSpec parity for keybindings, login, and logout.

<!-- sdn-diagram:id=auth_keybindings_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=auth_keybindings_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

auth_keybindings_spec -> std
auth_keybindings_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=auth_keybindings_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Auth and Keybindings Commands

Checks modern SSpec parity for keybindings, login, and logout.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/auth_keybindings_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for keybindings, login, and logout.

## Scenarios

### Claude full auth keybindings commands

#### should model keybindings lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(keybindingsIndexCommandName()).to_equal("keybindings")
expect(keybindingsFindAction("tab")).to_equal("complete")
expect(keybindingsFindAction("missing")).to_equal("")
```

</details>

#### should model login and logout decisions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(loginIndexCommandName()).to_equal("login")
expect(runLoginCommand("anthropic", false).shouldOpenBrowser).to_equal(true)
expect(runLoginCommand("anthropic", true).message).to_contain("Already")
expect(logoutIndexCommandName()).to_equal("logout")
expect(runLogoutCommand(true).clearedCredentials).to_equal(true)
expect(runLogoutCommand(false).message).to_contain("Not logged")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(keybindingsSourceLinesModeled()).to_equal(53)
expect(keybindingsIndexSourceLinesModeled()).to_equal(13)
expect(loginSourceLinesModeled()).to_equal(103)
expect(loginIndexSourceLinesModeled()).to_equal(14)
expect(logoutSourceLinesModeled()).to_equal(81)
expect(logoutIndexSourceLinesModeled()).to_equal(10)
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


</details>
