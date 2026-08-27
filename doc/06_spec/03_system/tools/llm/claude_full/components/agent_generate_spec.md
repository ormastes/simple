# Claude Full Agent Generate

> Checks generateAgent parity helpers; GenerateStep is checked by direct file path.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks generateAgent parity helpers; GenerateStep is checked by direct file path.

## Scenarios

### Claude full agent generation

#### builds prompt options and a generated result

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds prompt options and a generated result
- Clean options and render prompt
   - Expected: options.name equals `review-bot`
   - Expected: options.tools.len() equals `2`
   - Expected: joinGenerateTools(options.tools) equals `read, write`
   - Expected: result.ok is true
   - Expected: result.statusLine() equals `generated | review-bot | sonnet`
   - Expected: result.summary equals `review-bot | sonnet | tools=2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds prompt options and a generated result")
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

- blocks invalid generation with real errors
- Validate all required fields
   - Expected: options.valid() is false
   - Expected: result.ok is false
   - Expected: result.status equals `blocked`
   - Expected: result.errors.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("blocks invalid generation with real errors")
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

- exports source-backed helpers
- Check helper constants
   - Expected: generateAgentSourceHelper("helper") equals `generateAgent:helper`
   - Expected: generateAgentSourceHelpersModeled() equals `prompt,options,result,status`
   - Expected: generateAgentSourceLinesModeled() equals `197`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed helpers")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `445ee80adbb916e569b47fb0652dd110a1f3d49b4f59f1de9c6e9581cd8bbd7c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `445ee80adbb916e569b47fb0652dd110a1f3d49b4f59f1de9c6e9581cd8bbd7c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `445ee80adbb916e569b47fb0652dd110a1f3d49b4f59f1de9c6e9581cd8bbd7c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/components/agent_generate_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/agent_generate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/agent_generate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/agent_generate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/agent_generate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/agent_generate_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds prompt options and a generated result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/agent_generate_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks invalid generation with real errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/agent_generate_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports source-backed helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
