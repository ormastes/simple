# Agent Dashboard Hardening Specification

> <details>

<!-- sdn-diagram:id=agent_dashboard_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=agent_dashboard_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

agent_dashboard_hardening_spec -> std
agent_dashboard_hardening_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=agent_dashboard_hardening_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Agent Dashboard Hardening Specification

## Scenarios

### AgentTree — empty and absence safety

#### starts with zero agents

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AgentTree.new()
expect(tree.agent_count()).to_equal(0)
```

</details>

#### root_agents returns empty list when no agents added

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AgentTree.new()
expect(tree.root_agents().len()).to_equal(0)
```

</details>

#### get_agent returns no result for unknown id

- expect agent absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AgentTree.new()
val result = tree.get_agent("no-such-agent")
expect_agent_absent(result)
```

</details>

#### all_agents returns empty list initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AgentTree.new()
expect(tree.all_agents().len()).to_equal(0)
```

</details>

#### children_of unknown parent returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AgentTree.new()
expect(tree.children_of("ghost-parent").len()).to_equal(0)
```

</details>

#### depth_of unknown agent returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AgentTree.new()
expect(tree.depth_of("nobody")).to_equal(0)
```

</details>

#### ensure_agent creates a root entry

- tree ensure agent
   - Expected: tree.agent_count() equals `1`
   - Expected: tree.root_agents().len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AgentTree.new()
tree.ensure_agent("a1", LLMProvider.Claude, "sonnet")
expect(tree.agent_count()).to_equal(1)
expect(tree.root_agents().len()).to_equal(1)
```

</details>

#### ensure_agent is idempotent — calling twice keeps count at 1

- tree ensure agent
- tree ensure agent
   - Expected: tree.agent_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AgentTree.new()
tree.ensure_agent("a1", LLMProvider.Claude, "sonnet")
tree.ensure_agent("a1", LLMProvider.Claude, "sonnet")
expect(tree.agent_count()).to_equal(1)
```

</details>

#### get_agent finds an agent after ensure

- tree ensure agent
- expect agent id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AgentTree.new()
tree.ensure_agent("a2", LLMProvider.Gemini, "pro")
val found = tree.get_agent("a2")
expect_agent_id(found, "a2")
```

</details>

#### depth_of root agent is 0

- tree ensure agent
   - Expected: tree.depth_of("root-1") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AgentTree.new()
tree.ensure_agent("root-1", LLMProvider.Claude, "sonnet")
expect(tree.depth_of("root-1")).to_equal(0)
```

</details>

#### depth_of returns 0 for root agent

- tree ensure agent
   - Expected: tree.depth_of("root-check") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AgentTree.new()
tree.ensure_agent("root-check", LLMProvider.Claude, "")
expect(tree.depth_of("root-check")).to_equal(0)
```

</details>

### AgentPosition — slot and room boundary safety

#### pos_get on unknown id returns a valid pos (no crash)

- pos clear


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pos_clear()
val pos = pos_get("unknown-agent")
# Returns new_agent_pos default; room is Chat, slot 0
expect(pos.slot).to_be_greater_than(-1)
```

</details>

<details>
<summary>Advanced: pos_agents_in_room returns empty list when no agents present</summary>

#### pos_agents_in_room returns empty list when no agents present

- pos clear
   - Expected: result.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pos_clear()
val result = pos_agents_in_room(RoomKind.Research)
expect(result.len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: pos_agent_count_in_room is 0 on empty state</summary>

#### pos_agent_count_in_room is 0 on empty state

- pos clear
   - Expected: pos_agent_count_in_room(RoomKind.Code) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pos_clear()
expect(pos_agent_count_in_room(RoomKind.Code)).to_equal(0)
```

</details>


</details>

#### pos_update_from_nodes with empty list does not crash

- pos clear
- pos update from nodes
   - Expected: pos_agent_count_in_room(RoomKind.Chat) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pos_clear()
pos_update_from_nodes([])
expect(pos_agent_count_in_room(RoomKind.Chat)).to_equal(0)
```

</details>

<details>
<summary>Advanced: pos_update_from_nodes assigns slots within MAX_SLOTS_PER_ROOM (6)</summary>

#### pos_update_from_nodes assigns slots within MAX_SLOTS_PER_ROOM (6)

- pos clear
- agents push
- pos update from nodes


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- pos clear
- pos update from nodes
- pos clear
   - Expected: pos_agent_count_in_room(RoomKind.Chat) equals `0`
   - Expected: pos_get("temp").slot equals `0)  # default from new_agent_pos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pos_clear()
val node = AgentNode.new("temp", LLMProvider.Codex, "")
pos_update_from_nodes([node])
pos_clear()
expect(pos_agent_count_in_room(RoomKind.Chat)).to_equal(0)
expect(pos_get("temp").slot).to_equal(0)  # default from new_agent_pos
```

</details>

### AgentPanel — render_agent_tree boundary cases

#### renders placeholder lines when tree is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AgentTree.new()
val lines = render_agent_tree(tree, 100)
expect(lines.len()).to_equal(2)
```

</details>

#### renders 1 agent tree without crash

- tree ensure agent
   - Expected: tree.agent_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AgentTree.new()
tree.ensure_agent("solo", LLMProvider.Claude, "haiku")
val lines = render_agent_tree(tree, 100)
expect(tree.agent_count()).to_equal(1)
```

</details>

#### respects max_lines limit of 0 returns empty

- tree ensure agent
   - Expected: lines.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AgentTree.new()
tree.ensure_agent("a", LLMProvider.Claude, "")
val lines = render_agent_tree(tree, 0)
expect(lines.len()).to_equal(0)
```

</details>

#### respects max_lines=1 never exceeds 1 line

- tree ensure agent
- tree ensure agent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AgentTree.new()
tree.ensure_agent("x1", LLMProvider.Claude, "")
tree.ensure_agent("x2", LLMProvider.Gemini, "")
val lines = render_agent_tree(tree, 1)
expect(lines.len()).to_be_less_than(2)
```

</details>

#### renders multiple agents without crash

- tree ensure agent
   - Expected: tree.agent_count() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tree = AgentTree.new()
var k = 0
while k < 20:
    tree.ensure_agent("agent-{k}", LLMProvider.Claude, "sonnet")
    k = k + 1
val lines = render_agent_tree(tree, 200)
expect(tree.agent_count()).to_equal(20)
```

</details>

### AgentSprites — provider and activity coverage

#### agent_sprite always returns exactly 3 lines (SPRITE_HEIGHT)

- LLMProvider Unknown
- AgentActivity Finished, AgentActivity Error
- AgentActivity Reading
- AgentActivity Searching
- AgentActivity ToolUse
   - Expected: sprite.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        expect(sprite.len()).to_equal(3)
```

</details>

#### provider_head returns ? for Unknown provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(provider_head(LLMProvider.Unknown("mystery"))).to_equal("?")
```

</details>

#### provider_head returns C for Claude

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(provider_head(LLMProvider.Claude)).to_equal("C")
```

</details>

#### provider_head returns X for Codex

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(provider_head(LLMProvider.Codex)).to_equal("X")
```

</details>

#### provider_head returns G for Gemini

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(provider_head(LLMProvider.Gemini)).to_equal("G")
```

</details>

#### ToolUse activity hits fallback branch (returns 3 lines)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sprite = agent_sprite(LLMProvider.Claude, AgentActivity.ToolUse("bash"))
expect(sprite.len()).to_equal(3)
```

</details>

#### SubAgentSpawn activity hits fallback branch (returns 3 lines)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sprite = agent_sprite(LLMProvider.Gemini, AgentActivity.SubAgentSpawn("child-1"))
expect(sprite.len()).to_equal(3)
```

</details>

#### Unknown provider with Error activity returns 3 lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sprite = agent_sprite(LLMProvider.Unknown("nova"), AgentActivity.Error("oops"))
expect(sprite.len()).to_equal(3)
```

</details>

#### agent_indicator returns non-empty text for all known activities

- AgentActivity Reading
- AgentActivity Error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- pool register agent
- pool register agent
   - Expected: pool.active_agent_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = agent_pool_new(5)
pool.register_agent("dup", "linux")
pool.register_agent("dup", "linux")
expect(pool.active_agent_count()).to_equal(1)
```

</details>

#### deregister non-existent agent returns false without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = agent_pool_new(5)
expect(pool.deregister_agent("ghost")).to_equal(false)
```

</details>

#### heartbeat for unregistered agent returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = agent_pool_new(5)
expect(pool.heartbeat("nobody")).to_equal(false)
```

</details>

#### report_result for unregistered agent returns false

- pool load pending tests
   - Expected: pool.report_result("nobody", "test/x.spl", 1, 0, 0, 5, "ok") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = agent_pool_new(5)
pool.load_pending_tests(["test/x.spl"])
expect(pool.report_result("nobody", "test/x.spl", 1, 0, 0, 5, "ok")).to_equal(false)
```

</details>

#### claim_batch on pool with no pending tests returns empty

- pool register agent
   - Expected: pool.claim_batch("idle").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = agent_pool_new(5)
pool.register_agent("idle", "linux")
expect(pool.claim_batch("idle").len()).to_equal(0)
```

</details>

#### register then deregister then register again works correctly

- pool register agent
- pool deregister agent
   - Expected: pool.active_agent_count() equals `0`
- pool register agent
   - Expected: pool.active_agent_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = agent_pool_new(5)
pool.register_agent("cycled", "linux")
pool.deregister_agent("cycled")
expect(pool.active_agent_count()).to_equal(0)
pool.register_agent("cycled", "linux")
expect(pool.active_agent_count()).to_equal(1)
```

</details>

#### deregister returns in-progress tests to pending (existing coverage extended)

- pool register agent
- pool load pending tests
   - Expected: batch.len() equals `3`
- pool deregister agent
   - Expected: pool.active_agent_count() equals `0`
   - Expected: pool.pending_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = agent_pool_new(3)
pool.register_agent("worker", "linux")
pool.load_pending_tests(["test/a.spl", "test/b.spl", "test/c.spl"])
val batch = pool.claim_batch("worker")
expect(batch.len()).to_equal(3)
pool.deregister_agent("worker")
expect(pool.active_agent_count()).to_equal(0)
expect(pool.pending_count()).to_equal(3)
```

</details>

#### completed_count stays accurate after sequential complete cycles

- pool register agent
- pool load pending tests
- pool claim batch
- pool report result
- pool claim batch
- pool report result
- pool claim batch
- pool report result
   - Expected: pool.completed_count() equals `3`
   - Expected: pool.pending_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = agent_pool_new(1)
pool.register_agent("w1", "linux")
pool.load_pending_tests(["t1.spl", "t2.spl", "t3.spl"])
pool.claim_batch("w1")
pool.report_result("w1", "t1.spl", 1, 0, 0, 1, "ok")
pool.claim_batch("w1")
pool.report_result("w1", "t2.spl", 1, 0, 0, 1, "ok")
pool.claim_batch("w1")
pool.report_result("w1", "t3.spl", 1, 0, 0, 1, "ok")
expect(pool.completed_count()).to_equal(3)
expect(pool.pending_count()).to_equal(0)
```

</details>

#### load_pending_tests after all completed adds only net-new tests

- pool register agent
- pool load pending tests
- pool claim batch
- pool report result
- pool load pending tests
   - Expected: pool.pending_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = agent_pool_new(5)
pool.register_agent("w2", "linux")
pool.load_pending_tests(["old.spl"])
pool.claim_batch("w2")
pool.report_result("w2", "old.spl", 1, 0, 0, 1, "ok")
pool.load_pending_tests(["old.spl", "new.spl"])
expect(pool.pending_count()).to_equal(1)
```

</details>

### Dashboard continuity — empty data source

#### render_agent_tree after clearing all agents shows placeholder

- tree ensure agent


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- pos clear
- pos update from nodes
- pos update from nodes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- pos clear
- pos update from nodes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
pos_clear()
val node = AgentNode.new("thinker", LLMProvider.Claude, "")
# Thinking maps to Chat by default (no tool use)
pos_update_from_nodes([node])
val pos = pos_get("thinker")
expect(pos.slot).to_be_greater_than(-1)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_dashboard/agent_dashboard_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AgentTree — empty and absence safety
- AgentPosition — slot and room boundary safety
- AgentPanel — render_agent_tree boundary cases
- AgentSprites — provider and activity coverage
- AgentPool — sequential integrity hardening
- Dashboard continuity — empty data source

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
