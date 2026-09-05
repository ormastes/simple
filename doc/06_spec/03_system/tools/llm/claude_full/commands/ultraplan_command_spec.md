# Claude Full Ultraplan Command

> Checks modern SSpec parity for the ultraplan command model.

<!-- sdn-diagram:id=ultraplan_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ultraplan_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ultraplan_command_spec -> std
ultraplan_command_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ultraplan_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Ultraplan Command

Checks modern SSpec parity for the ultraplan command model.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/ultraplan_command_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the ultraplan command model.

## Scenarios

### Claude full ultraplan command

#### exposes command metadata and plan mode name

- Check command metadata
   - Expected: ultraplanCommandName() equals `ultraplan`
   - Expected: ultraplanPlanModeName() equals `ultraplan`
   - Expected: ultraplanArgumentHint() equals `[goal]`
   - Expected: ultraplanLoadPath() equals `./ultraplan.js`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check command metadata")
expect(ultraplanCommandName()).to_equal("ultraplan")
expect(ultraplanPlanModeName()).to_equal("ultraplan")
expect(ultraplanArgumentHint()).to_equal("[goal]")
expect(ultraplanLoadPath()).to_equal("./ultraplan.js")
expect(ultraplanCommandDescription()).to_contain("implementation plan")
```

</details>

#### creates a plan summary in ultraplan mode

- Create a plan from a concrete goal
   - Expected: result.ok is true
   - Expected: result.status equals `plan-created`
   - Expected: result.mode equals `ultraplan`
   - Expected: result.sessionId equals `session-1`
   - Expected: result.title equals `Plan: ship Claude full parity`
   - Expected: result.nextAction equals `Review the proposed plan, then accept or refine it.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a plan from a concrete goal")
val session = ultraplanDefaultSession(" session-1 ")
val result = ultraplanCreatePlan(session, " ship Claude full parity ")

expect(result.ok).to_equal(true)
expect(result.status).to_equal("plan-created")
expect(result.mode).to_equal("ultraplan")
expect(result.sessionId).to_equal("session-1")
expect(result.title).to_equal("Plan: ship Claude full parity")
expect(result.summary).to_contain("ship Claude full parity")
expect(result.summary).to_contain("0 prior accepted plan(s)")
expect(result.nextAction).to_equal("Review the proposed plan, then accept or refine it.")
```

</details>

#### models disabled and invalid input behavior

- Reject command use while disabled
   - Expected: blocked.ok is false
   - Expected: blocked.status equals `disabled`
- Reject blank goals
   - Expected: invalid.ok is false
   - Expected: invalid.status equals `invalid-input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject command use while disabled")
val disabled = ultraplanDisabledSession("session-2")
val blocked = ultraplanCreatePlan(disabled, "plan something")
expect(blocked.ok).to_equal(false)
expect(blocked.status).to_equal("disabled")
expect(blocked.nextAction).to_contain("Enable ultraplan")

step("Reject blank goals")
val invalid = ultraplanCreatePlan(ultraplanDefaultSession("session-3"), "   ")
expect(invalid.ok).to_equal(false)
expect(invalid.status).to_equal("invalid-input")
expect(invalid.summary).to_contain("No goal supplied")
```

</details>

#### keeps source line helper and floor visible

- Check modeled source evidence
   - Expected: ultraplanSourceLine(89) equals `ultraplan source line 89`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check modeled source evidence")
expect(ultraplanSourceLine(89)).to_equal("ultraplan source line 89")
expect(ultraplanSourceLinesModeled()).to_be_greater_than(469)
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
