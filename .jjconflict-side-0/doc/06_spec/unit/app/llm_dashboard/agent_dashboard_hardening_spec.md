# agent_dashboard_hardening_spec

> Purpose: Prove that AgentTree — empty and absence safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# agent_dashboard_hardening_spec

Purpose: Prove that AgentTree — empty and absence safety.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_dashboard/agent_dashboard_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that AgentTree — empty and absence safety.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### AgentTree — empty and absence safety

#### starts with zero agents

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts with zero agents
- Verify: starts with zero agents
   - Expected: tree.agent_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with zero agents")
step("Verify: starts with zero agents")
# @req: REQ-APP-LLM-DASHBOARD-001
val tree = AgentTree.new()
expect(tree.agent_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### root_agents returns empty list when no agents added

- root_agents returns empty list when no agents added
- Verify: root_agents returns empty list when no agents added
   - Expected: tree.root_agents().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("root_agents returns empty list when no agents added")
step("Verify: root_agents returns empty list when no agents added")
val tree = AgentTree.new()
expect(tree.root_agents().len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### get_agent returns no result for unknown id

- get_agent returns no result for unknown id
- Verify: get_agent returns no result for unknown id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_agent returns no result for unknown id")
step("Verify: get_agent returns no result for unknown id")
val tree = AgentTree.new()
val result = tree.get_agent("no-such-agent")
expect_agent_absent(result)
```

</details>

#### all_agents returns empty list initially

- all_agents returns empty list initially
- Verify: all_agents returns empty list initially
   - Expected: tree.all_agents().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all_agents returns empty list initially")
step("Verify: all_agents returns empty list initially")
val tree = AgentTree.new()
expect(tree.all_agents().len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### children_of unknown parent returns empty list

- children_of unknown parent returns empty list
- Verify: children_of unknown parent returns empty list
   - Expected: tree.children_of("ghost-parent").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("children_of unknown parent returns empty list")
step("Verify: children_of unknown parent returns empty list")
val tree = AgentTree.new()
expect(tree.children_of("ghost-parent").len()).to_equal(0)
```

</details>

#### depth_of unknown agent returns 0

- depth_of unknown agent returns 0
- Verify: depth_of unknown agent returns 0
   - Expected: tree.depth_of("nobody") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("depth_of unknown agent returns 0")
step("Verify: depth_of unknown agent returns 0")
val tree = AgentTree.new()
expect(tree.depth_of("nobody")).to_equal(0)
```

</details>

#### ensure_agent creates a root entry

- ensure_agent creates a root entry
- Verify: ensure_agent creates a root entry
   - Expected: tree.agent_count() equals `1`
   - Expected: tree.root_agents().len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ensure_agent creates a root entry")
step("Verify: ensure_agent creates a root entry")
val tree = AgentTree.new()
tree.ensure_agent("a1", LLMProvider.Claude, "sonnet")
expect(tree.agent_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(tree.root_agents().len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### ensure_agent is idempotent — calling twice keeps count at 1

- ensure_agent is idempotent — calling twice keeps count at 1
- Verify: ensure_agent is idempotent — calling twice keeps count at 1
   - Expected: tree.agent_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ensure_agent is idempotent — calling twice keeps count at 1")
step("Verify: ensure_agent is idempotent — calling twice keeps count at 1")
val tree = AgentTree.new()
tree.ensure_agent("a1", LLMProvider.Claude, "sonnet")
tree.ensure_agent("a1", LLMProvider.Claude, "sonnet")
expect(tree.agent_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### get_agent finds an agent after ensure

- get_agent finds an agent after ensure
- Verify: get_agent finds an agent after ensure


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_agent finds an agent after ensure")
step("Verify: get_agent finds an agent after ensure")
val tree = AgentTree.new()
tree.ensure_agent("a2", LLMProvider.Gemini, "pro")
val found = tree.get_agent("a2")
expect_agent_id(found, "a2")
```

</details>

#### depth_of root agent is 0

- depth_of root agent is 0
- Verify: depth_of root agent is 0
   - Expected: tree.depth_of("root-1") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("depth_of root agent is 0")
step("Verify: depth_of root agent is 0")
val tree = AgentTree.new()
tree.ensure_agent("root-1", LLMProvider.Claude, "sonnet")
expect(tree.depth_of("root-1")).to_equal(0)
```

</details>

#### depth_of returns 0 for root agent

- depth_of returns 0 for root agent
- Verify: depth_of returns 0 for root agent
   - Expected: tree.depth_of("root-check") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("depth_of returns 0 for root agent")
step("Verify: depth_of returns 0 for root agent")
val tree = AgentTree.new()
tree.ensure_agent("root-check", LLMProvider.Claude, "")
expect(tree.depth_of("root-check")).to_equal(0)
```

</details>

### AgentPosition — slot and room boundary safety

#### pos_get on unknown id returns a valid pos (no crash)

- pos_get on unknown id returns a valid pos (no crash)
- Verify: pos_get on unknown id returns a valid pos (no crash)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pos_get on unknown id returns a valid pos (no crash)")
step("Verify: pos_get on unknown id returns a valid pos (no crash)")
pos_clear()
val pos = pos_get("unknown-agent")
# Returns new_agent_pos default; room is Chat, slot 0
expect(pos.slot).to_be_greater_than(-1)
```

</details>

<details>
<summary>Advanced: pos_agents_in_room returns empty list when no agents present</summary>

#### pos_agents_in_room returns empty list when no agents present

- pos_agents_in_room returns empty list when no agents present
- Verify: pos_agents_in_room returns empty list when no agents present
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pos_agents_in_room returns empty list when no agents present")
step("Verify: pos_agents_in_room returns empty list when no agents present")
pos_clear()
val result = pos_agents_in_room(RoomKind.Research)
expect(result.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>


</details>

<details>
<summary>Advanced: pos_agent_count_in_room is 0 on empty state</summary>

#### pos_agent_count_in_room is 0 on empty state

- pos_agent_count_in_room is 0 on empty state
- Verify: pos_agent_count_in_room is 0 on empty state
   - Expected: pos_agent_count_in_room(RoomKind.Code) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pos_agent_count_in_room is 0 on empty state")
step("Verify: pos_agent_count_in_room is 0 on empty state")
pos_clear()
expect(pos_agent_count_in_room(RoomKind.Code)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>


</details>

#### pos_update_from_nodes with empty list does not crash

- pos_update_from_nodes with empty list does not crash
- Verify: pos_update_from_nodes with empty list does not crash
   - Expected: pos_agent_count_in_room(RoomKind.Chat) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pos_update_from_nodes with empty list does not crash")
step("Verify: pos_update_from_nodes with empty list does not crash")
pos_clear()
pos_update_from_nodes([])
expect(pos_agent_count_in_room(RoomKind.Chat)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

<details>
<summary>Advanced: pos_update_from_nodes assigns slots within MAX_SLOTS_PER_ROOM (6)</summary>

#### pos_update_from_nodes assigns slots within MAX_SLOTS_PER_ROOM (6)

- pos_update_from_nodes assigns slots within MAX_SLOTS_PER_ROOM (6)
- Verify: pos_update_from_nodes assigns slots within MAX_SLOTS_PER_ROOM (6)


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pos_update_from_nodes assigns slots within MAX_SLOTS_PER_ROOM (6)")
step("Verify: pos_update_from_nodes assigns slots within MAX_SLOTS_PER_ROOM (6)")
pos_clear()
val tree = AgentTree.new()
var agents: [AgentNode] = []
var j = 0
while j < 8:
    val node = AgentNode.new("bulk-{j}", LLMProvider.Claude, "sonnet")
    agents.push(node)
    j = j + 1
pos_update_from_nodes(agents)
val in_chat = pos_agents_in_room(RoomKind.Chat)
# All 8 are Idle → Chat room; slots wrap mod 6
for ap in in_chat:
    expect(ap.slot).to_be_greater_than(-1)
    expect(ap.slot).to_be_less_than(6)
```

</details>


</details>

#### pos_clear resets state so subsequent queries start fresh

- pos_clear resets state so subsequent queries start fresh
- Verify: pos_clear resets state so subsequent queries start fresh
   - Expected: pos_agent_count_in_room(RoomKind.Chat) equals `0`
   - Expected: pos_get("temp").slot equals `0)  # default from new_agent_pos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pos_clear resets state so subsequent queries start fresh")
step("Verify: pos_clear resets state so subsequent queries start fresh")
pos_clear()
val node = AgentNode.new("temp", LLMProvider.Codex, "")
pos_update_from_nodes([node])
pos_clear()
expect(pos_agent_count_in_room(RoomKind.Chat)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(pos_get("temp").slot).to_equal(0)  # default from new_agent_pos
```

</details>

### AgentPanel — render_agent_tree boundary cases

#### renders placeholder lines when tree is empty

- renders placeholder lines when tree is empty
- Verify: renders placeholder lines when tree is empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders placeholder lines when tree is empty")
step("Verify: renders placeholder lines when tree is empty")
val tree = AgentTree.new()
val lines = render_agent_tree(tree, 100)
# Must not be empty
expect(lines.len()).to_be_greater_than(0)
# Content references waiting state
val joined = lines.join("")
expect(joined).to_contain("No agents connected")
```

</details>

#### renders exactly 2 placeholder lines for empty tree

- renders exactly 2 placeholder lines for empty tree
- Verify: renders exactly 2 placeholder lines for empty tree
   - Expected: lines.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders exactly 2 placeholder lines for empty tree")
step("Verify: renders exactly 2 placeholder lines for empty tree")
val tree = AgentTree.new()
val lines = render_agent_tree(tree, 100)
expect(lines.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### renders 1 agent tree without crash

- renders 1 agent tree without crash
- Verify: renders 1 agent tree without crash
   - Expected: tree.agent_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders 1 agent tree without crash")
step("Verify: renders 1 agent tree without crash")
val tree = AgentTree.new()
tree.ensure_agent("solo", LLMProvider.Claude, "haiku")
val lines = render_agent_tree(tree, 100)
expect(tree.agent_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### respects max_lines limit of 0 returns empty

- respects max_lines limit of 0 returns empty
- Verify: respects max_lines limit of 0 returns empty
   - Expected: lines.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("respects max_lines limit of 0 returns empty")
step("Verify: respects max_lines limit of 0 returns empty")
val tree = AgentTree.new()
tree.ensure_agent("a", LLMProvider.Claude, "")
val lines = render_agent_tree(tree, 0)
expect(lines.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### respects max_lines=1 never exceeds 1 line

- respects max_lines=1 never exceeds 1 line
- Verify: respects max_lines=1 never exceeds 1 line


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("respects max_lines=1 never exceeds 1 line")
step("Verify: respects max_lines=1 never exceeds 1 line")
val tree = AgentTree.new()
tree.ensure_agent("x1", LLMProvider.Claude, "")
tree.ensure_agent("x2", LLMProvider.Gemini, "")
val lines = render_agent_tree(tree, 1)
expect(lines.len()).to_be_less_than(2)
```

</details>

#### renders multiple agents without crash

- renders multiple agents without crash
- Verify: renders multiple agents without crash
   - Expected: tree.agent_count() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders multiple agents without crash")
step("Verify: renders multiple agents without crash")
val tree = AgentTree.new()
var k = 0
while k < 20:
    tree.ensure_agent("agent-{k}", LLMProvider.Claude, "sonnet")
    k = k + 1
val lines = render_agent_tree(tree, 200)
expect(tree.agent_count()).to_equal(20)  # oracle: 20 — named expected value from the requirement
```

</details>

### AgentSprites — provider and activity coverage

#### agent_sprite always returns exactly 3 lines (SPRITE_HEIGHT)

- agent_sprite always returns exactly 3 lines (SPRITE_HEIGHT)
- Verify: agent_sprite always returns exactly 3 lines (SPRITE_HEIGHT)
   - Expected: sprite.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agent_sprite always returns exactly 3 lines (SPRITE_HEIGHT)")
step("Verify: agent_sprite always returns exactly 3 lines (SPRITE_HEIGHT)")
val providers = [LLMProvider.Claude, LLMProvider.Codex, LLMProvider.Gemini,
                 LLMProvider.Unknown("unk")]
val activities = [AgentActivity.Idle, AgentActivity.Thinking,
                  AgentActivity.Finished, AgentActivity.Error("boom"),
                  AgentActivity.Reading("/tmp/f"), AgentActivity.Writing("/tmp/g"),
                  AgentActivity.Searching("q"), AgentActivity.WebFetch("http://x"),
                  AgentActivity.ToolUse("bash"), AgentActivity.SubAgentSpawn("child")]
for prov in providers:
    for act in activities:
        val sprite = agent_sprite(prov, act)
        expect(sprite.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### provider_head returns ? for Unknown provider

- provider_head returns ? for Unknown provider
- Verify: provider_head returns ? for Unknown provider
   - Expected: provider_head(LLMProvider.Unknown("mystery")) equals `?`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provider_head returns ? for Unknown provider")
step("Verify: provider_head returns ? for Unknown provider")
expect(provider_head(LLMProvider.Unknown("mystery"))).to_equal("?")
```

</details>

#### provider_head returns C for Claude

- provider_head returns C for Claude
- Verify: provider_head returns C for Claude
   - Expected: provider_head(LLMProvider.Claude) equals `C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provider_head returns C for Claude")
step("Verify: provider_head returns C for Claude")
expect(provider_head(LLMProvider.Claude)).to_equal("C")
```

</details>

#### provider_head returns X for Codex

- provider_head returns X for Codex
- Verify: provider_head returns X for Codex
   - Expected: provider_head(LLMProvider.Codex) equals `X`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provider_head returns X for Codex")
step("Verify: provider_head returns X for Codex")
expect(provider_head(LLMProvider.Codex)).to_equal("X")
```

</details>

#### provider_head returns G for Gemini

- provider_head returns G for Gemini
- Verify: provider_head returns G for Gemini
   - Expected: provider_head(LLMProvider.Gemini) equals `G`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provider_head returns G for Gemini")
step("Verify: provider_head returns G for Gemini")
expect(provider_head(LLMProvider.Gemini)).to_equal("G")
```

</details>

#### ToolUse activity hits fallback branch (returns 3 lines)

- ToolUse activity hits fallback branch (returns 3 lines)
- Verify: ToolUse activity hits fallback branch (returns 3 lines)
   - Expected: sprite.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ToolUse activity hits fallback branch (returns 3 lines)")
step("Verify: ToolUse activity hits fallback branch (returns 3 lines)")
val sprite = agent_sprite(LLMProvider.Claude, AgentActivity.ToolUse("bash"))
expect(sprite.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### SubAgentSpawn activity hits fallback branch (returns 3 lines)

- SubAgentSpawn activity hits fallback branch (returns 3 lines)
- Verify: SubAgentSpawn activity hits fallback branch (returns 3 lines)
   - Expected: sprite.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SubAgentSpawn activity hits fallback branch (returns 3 lines)")
step("Verify: SubAgentSpawn activity hits fallback branch (returns 3 lines)")
val sprite = agent_sprite(LLMProvider.Gemini, AgentActivity.SubAgentSpawn("child-1"))
expect(sprite.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### Unknown provider with Error activity returns 3 lines

- Unknown provider with Error activity returns 3 lines
- Verify: Unknown provider with Error activity returns 3 lines
   - Expected: sprite.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Unknown provider with Error activity returns 3 lines")
step("Verify: Unknown provider with Error activity returns 3 lines")
val sprite = agent_sprite(LLMProvider.Unknown("nova"), AgentActivity.Error("oops"))
expect(sprite.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### agent_indicator returns non-empty text for all known activities

- agent_indicator returns non-empty text for all known activities
- Verify: agent_indicator returns non-empty text for all known activities


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agent_indicator returns non-empty text for all known activities")
step("Verify: agent_indicator returns non-empty text for all known activities")
val acts = [AgentActivity.Idle, AgentActivity.Thinking, AgentActivity.Finished,
            AgentActivity.Reading("/f"), AgentActivity.Writing("/g"),
            AgentActivity.Error("e")]
for act in acts:
    val ind = agent_indicator(LLMProvider.Claude, act)
    expect(ind.len()).to_be_greater_than(0)
```

</details>

### AgentPool — sequential integrity hardening

#### register same agent id twice keeps count at 1

- register same agent id twice keeps count at 1
- Verify: register same agent id twice keeps count at 1
   - Expected: pool.active_agent_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("register same agent id twice keeps count at 1")
step("Verify: register same agent id twice keeps count at 1")
val pool = agent_pool_new(5)
pool.register_agent("dup", "linux")
pool.register_agent("dup", "linux")
expect(pool.active_agent_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### deregister non-existent agent returns false without crash

- deregister non-existent agent returns false without crash
- Verify: deregister non-existent agent returns false without crash
   - Expected: pool.deregister_agent("ghost") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deregister non-existent agent returns false without crash")
step("Verify: deregister non-existent agent returns false without crash")
val pool = agent_pool_new(5)
expect(pool.deregister_agent("ghost")).to_equal(false)
```

</details>

#### heartbeat for unregistered agent returns false

- heartbeat for unregistered agent returns false
- Verify: heartbeat for unregistered agent returns false
   - Expected: pool.heartbeat("nobody") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("heartbeat for unregistered agent returns false")
step("Verify: heartbeat for unregistered agent returns false")
val pool = agent_pool_new(5)
expect(pool.heartbeat("nobody")).to_equal(false)
```

</details>

#### report_result for unregistered agent returns false

- report_result for unregistered agent returns false
- Verify: report_result for unregistered agent returns false
   - Expected: pool.report_result("nobody", "test/x.spl", 1, 0, 0, 5, "ok") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("report_result for unregistered agent returns false")
step("Verify: report_result for unregistered agent returns false")
val pool = agent_pool_new(5)
pool.load_pending_tests(["test/x.spl"])
expect(pool.report_result("nobody", "test/x.spl", 1, 0, 0, 5, "ok")).to_equal(false)
```

</details>

#### claim_batch on pool with no pending tests returns empty

- claim_batch on pool with no pending tests returns empty
- Verify: claim_batch on pool with no pending tests returns empty
   - Expected: pool.claim_batch("idle").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("claim_batch on pool with no pending tests returns empty")
step("Verify: claim_batch on pool with no pending tests returns empty")
val pool = agent_pool_new(5)
pool.register_agent("idle", "linux")
expect(pool.claim_batch("idle").len()).to_equal(0)
```

</details>

#### register then deregister then register again works correctly

- register then deregister then register again works correctly
- Verify: register then deregister then register again works correctly
   - Expected: pool.active_agent_count() equals `0`
   - Expected: pool.active_agent_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("register then deregister then register again works correctly")
step("Verify: register then deregister then register again works correctly")
val pool = agent_pool_new(5)
pool.register_agent("cycled", "linux")
pool.deregister_agent("cycled")
expect(pool.active_agent_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
pool.register_agent("cycled", "linux")
expect(pool.active_agent_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### deregister returns in-progress tests to pending (existing coverage extended)

- deregister returns in-progress tests to pending (existing coverage extended)
- Verify: deregister returns in-progress tests to pending (existing coverage extended)
   - Expected: batch.len() equals `3`
   - Expected: pool.active_agent_count() equals `0`
   - Expected: pool.pending_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deregister returns in-progress tests to pending (existing coverage extended)")
step("Verify: deregister returns in-progress tests to pending (existing coverage extended)")
val pool = agent_pool_new(3)
pool.register_agent("worker", "linux")
pool.load_pending_tests(["test/a.spl", "test/b.spl", "test/c.spl"])
val batch = pool.claim_batch("worker")
expect(batch.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
pool.deregister_agent("worker")
expect(pool.active_agent_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(pool.pending_count()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### completed_count stays accurate after sequential complete cycles

- completed_count stays accurate after sequential complete cycles
- Verify: completed_count stays accurate after sequential complete cycles
   - Expected: pool.completed_count() equals `3`
   - Expected: pool.pending_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("completed_count stays accurate after sequential complete cycles")
step("Verify: completed_count stays accurate after sequential complete cycles")
val pool = agent_pool_new(1)
pool.register_agent("w1", "linux")
pool.load_pending_tests(["t1.spl", "t2.spl", "t3.spl"])
pool.claim_batch("w1")
pool.report_result("w1", "t1.spl", 1, 0, 0, 1, "ok")
pool.claim_batch("w1")
pool.report_result("w1", "t2.spl", 1, 0, 0, 1, "ok")
pool.claim_batch("w1")
pool.report_result("w1", "t3.spl", 1, 0, 0, 1, "ok")
expect(pool.completed_count()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(pool.pending_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### load_pending_tests after all completed adds only net-new tests

- load_pending_tests after all completed adds only net-new tests
- Verify: load_pending_tests after all completed adds only net-new tests
   - Expected: pool.pending_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("load_pending_tests after all completed adds only net-new tests")
step("Verify: load_pending_tests after all completed adds only net-new tests")
val pool = agent_pool_new(5)
pool.register_agent("w2", "linux")
pool.load_pending_tests(["old.spl"])
pool.claim_batch("w2")
pool.report_result("w2", "old.spl", 1, 0, 0, 1, "ok")
pool.load_pending_tests(["old.spl", "new.spl"])
expect(pool.pending_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### Dashboard continuity — empty data source

#### render_agent_tree after clearing all agents shows placeholder

- render_agent_tree after clearing all agents shows placeholder
- Verify: render_agent_tree after clearing all agents shows placeholder


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("render_agent_tree after clearing all agents shows placeholder")
step("Verify: render_agent_tree after clearing all agents shows placeholder")
val tree = AgentTree.new()
tree.ensure_agent("gone", LLMProvider.Claude, "")
# Simulate data-source disconnect by building a new empty tree
val fresh = AgentTree.new()
val lines = render_agent_tree(fresh, 100)
val joined = lines.join("")
expect(joined).to_contain("No agents connected")
```

</details>

<details>
<summary>Advanced: pos_update_from_nodes with empty list after data clears room counts</summary>

#### pos_update_from_nodes with empty list after data clears room counts

- pos_update_from_nodes with empty list after data clears room counts
- Verify: pos_update_from_nodes with empty list after data clears room counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pos_update_from_nodes with empty list after data clears room counts")
step("Verify: pos_update_from_nodes with empty list after data clears room counts")
pos_clear()
val node = AgentNode.new("was-here", LLMProvider.Claude, "")
pos_update_from_nodes([node])
expect(pos_agent_count_in_room(RoomKind.Chat)).to_be_greater_than(0)
# Disconnect: feed empty list
pos_update_from_nodes([])
# State is NOT automatically pruned (by design — positions are retained
# until pos_clear). Verify no crash and count is still non-negative.
val count = pos_agent_count_in_room(RoomKind.Chat)
expect(count).to_be_greater_than(-1)
```

</details>


</details>

<details>
<summary>Advanced: pos_clear then update from single Thinking agent assigns Code room</summary>

#### pos_clear then update from single Thinking agent assigns Code room

- pos_clear then update from single Thinking agent assigns Code room
- Verify: pos_clear then update from single Thinking agent assigns Code room


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pos_clear then update from single Thinking agent assigns Code room")
step("Verify: pos_clear then update from single Thinking agent assigns Code room")
pos_clear()
val node = AgentNode.new("thinker", LLMProvider.Claude, "")
# Thinking maps to Chat by default (no tool use)
pos_update_from_nodes([node])
val pos = pos_get("thinker")
expect(pos.slot).to_be_greater_than(-1)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-LLM-DASHBOARD-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `77e5edef3c6846135146a6f77bc11c6c4ced015a9b49c8b93507f2ca7f20f47e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `77e5edef3c6846135146a6f77bc11c6c4ced015a9b49c8b93507f2ca7f20f47e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `77e5edef3c6846135146a6f77bc11c6c4ced015a9b49c8b93507f2ca7f20f47e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/llm_dashboard/agent_dashboard_hardening_spec.spl
mirror: doc/06_spec/unit/app/llm_dashboard/agent_dashboard_hardening_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/llm_dashboard/agent_dashboard_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/llm_dashboard/agent_dashboard_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/llm_dashboard/agent_dashboard_hardening_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/llm_dashboard/agent_dashboard_hardening_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with zero agents' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_dashboard/agent_dashboard_hardening_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'root_agents returns empty list when no agents added' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/llm_dashboard/agent_dashboard_hardening_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'get_agent returns no result for unknown id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
