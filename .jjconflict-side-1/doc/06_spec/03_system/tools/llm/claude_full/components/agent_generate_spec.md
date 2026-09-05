# Claude Full Agent Generate

> Checks generateAgent parity helpers; GenerateStep is checked by direct file path.

<!-- sdn-diagram:id=agent_generate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=agent_generate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

agent_generate_spec -> std
agent_generate_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=agent_generate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Agent Generate

Checks generateAgent parity helpers; GenerateStep is checked by direct file path.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/agent_generate_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks generateAgent parity helpers; GenerateStep is checked by direct file path.

## Scenarios

### Claude full agent generation

#### builds prompt options and a generated result

- Clean options and render prompt
   - Expected: options.name equals `review-bot`
   - Expected: options.tools.len() equals `2`
   - Expected: joinGenerateTools(options.tools) equals `read, write`
   - Expected: result.ok is true
   - Expected: result.statusLine() equals `generated | review-bot | sonnet`
   - Expected: result.summary equals `review-bot | sonnet | tools=2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Clean options and render prompt")
val options = generateAgentOptions(" review-bot ", " Reviews diffs ", " sonnet ", ["read", "", "write", "read"], " Be concise. ")
val prompt = generateAgentPrompt(options)
val result = generateAgent(options)

expect(options.name).to_equal("review-bot")
expect(options.tools.len()).to_equal(2)
expect(joinGenerateTools(options.tools)).to_equal("read, write")
expect(prompt.render()).to_contain("Generate agent: review-bot")
expect(prompt.render()).to_contain("Tools: read, write")
expect(result.ok).to_equal(true)
expect(result.statusLine()).to_equal("generated | review-bot | sonnet")
expect(result.summary).to_equal("review-bot | sonnet | tools=2")
```

</details>

#### blocks invalid generation with real errors

- Validate all required fields
   - Expected: options.valid() is false
   - Expected: result.ok is false
   - Expected: result.status equals `blocked`
   - Expected: result.errors.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate all required fields")
val options = generateAgentOptions("", "", "", [], "")
val result = generateAgent(options)

expect(options.valid()).to_equal(false)
expect(result.ok).to_equal(false)
expect(result.status).to_equal("blocked")
expect(result.errors.len()).to_equal(4)
expect(joinGenerateErrors(result.errors)).to_contain("name is required")
expect(generateAgentStatusLine(result)).to_contain("blocked | name is required")
```

</details>

#### exports source-backed helpers

- Check helper constants
   - Expected: generateAgentSourceHelper("helper") equals `generateAgent:helper`
   - Expected: generateAgentSourceHelpersModeled() equals `prompt,options,result,status`
   - Expected: generateAgentSourceLinesModeled() equals `197`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check helper constants")
expect(generateAgentSourceHelper("helper")).to_equal("generateAgent:helper")
expect(generateAgentSourceHelpersModeled()).to_equal("prompt,options,result,status")
expect(generateAgentSourceLinesModeled()).to_equal(197)
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
