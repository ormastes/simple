# Claude Full agent swarms enabled

> Focused agent-swarms owner behavior for `REQ-LLM-CARET-HIDDEN-008`.

| Field | Value |
|---|---|
| Source | `test/03_system/tools/llm/claude_full/utils/agent_swarms_enabled_spec.spl` |
| Executable scenarios | 3 |
| Execution in this tranche | 0 scenarios executed |
| Result | Not executed; no PASS is claimed |
| Requirement | `REQ-LLM-CARET-HIDDEN-008` |

## Scope and Claim Boundary

This focused manual mirrors ANT override, external opt-in, and killswitch
behavior from `agentSwarmsEnabled.spl`. The aggregate feature-gate registry
owns the exhaustive input matrix. This manual does not claim shipped CLI/TUI
reachability, live process behavior, or runtime execution.

## Scenarios

### REQ-LLM-CARET-HIDDEN-008: focused agent-swarms owner behavior

#### should always enable ANT users

- Check ant override

<details>
<summary>Executable SSpec</summary>

```simple
it "should always enable ANT users":
    step("Check ant override")
    expect(isAgentSwarmsEnabled("ant", false, false, false)).to_equal(true)
    expect(isAgentSwarmsEnabled("ant", false, false, true)).to_equal(true)
    expect(isAgentSwarmsEnabled("ant", true, true, false)).to_equal(true)
```

</details>

#### should require external opt-in

- Check external opt-in

<details>
<summary>Executable SSpec</summary>

```simple
it "should require external opt-in":
    step("Check external opt-in")
    expect(isAgentSwarmsEnabled("user", false, false, true)).to_equal(false)
    expect(isAgentSwarmsEnabled("user", true, false, true)).to_equal(true)
    expect(isAgentSwarmsEnabled("user", false, true, true)).to_equal(true)
    expect(isAgentSwarmsEnabled("user", true, true, true)).to_equal(true)
```

</details>

#### should respect the external killswitch

- Check killswitch

<details>
<summary>Executable SSpec</summary>

```simple
it "should respect the external killswitch":
    step("Check killswitch")
    expect(isAgentSwarmsEnabled("user", true, false, false)).to_equal(false)
    expect(isAgentSwarmsEnabled("user", false, true, false)).to_equal(false)
    expect(isAgentSwarmsEnabled("user", true, true, false)).to_equal(false)
```

</details>

## Execution Status

The executable spec and this mirrored manual were updated statically. No
runtime was invoked, 0 scenarios were executed, and no PASS is claimed.
