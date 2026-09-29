# Claude Full slash command parsing

> Pure Simple coverage for slash command input parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full slash command parsing

Pure Simple coverage for slash command input parsing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/slash_command_parsing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for slash command input parsing.

## Scenarios

### Claude full slash command parsing

#### parses plain slash commands

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses plain slash commands
- Check command and args
   - Expected: parsed.commandName equals `search`
   - Expected: parsed.args equals `foo bar`
   - Expected: parsed.isMcp is false
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses plain slash commands")
step("Check command and args")
if val parsed = parseSlashCommand("/search foo bar"):
    expect(parsed.commandName).to_equal("search")
    expect(parsed.args).to_equal("foo bar")
    expect(parsed.isMcp).to_equal(false)
else:
    expect(false).to_equal(true)
```

</details>

#### parses MCP command marker

- parses MCP command marker
- Check MCP marker
   - Expected: parsed.commandName equals `mcp:tool (MCP)`
   - Expected: parsed.args equals `arg1 arg2`
   - Expected: parsed.isMcp is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses MCP command marker")
step("Check MCP marker")
if val parsed = parseSlashCommand("/mcp:tool (MCP) arg1 arg2"):
    expect(parsed.commandName).to_equal("mcp:tool (MCP)")
    expect(parsed.args).to_equal("arg1 arg2")
    expect(parsed.isMcp).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### trims input and rejects non-commands

- trims input and rejects non-commands
- Check invalid inputs
   - Expected: parsed.commandName equals `clear`
   - Expected: parsed.args equals ``
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("trims input and rejects non-commands")
step("Check invalid inputs")
expect(parseSlashCommand("search foo")).to_be_nil()
expect(parseSlashCommand("/")).to_be_nil()
if val parsed = parseSlashCommand("   /clear   "):
    expect(parsed.commandName).to_equal("clear")
    expect(parsed.args).to_equal("")
else:
    expect(false).to_equal(true)
```

</details>

#### preserves split-space argument behavior

- preserves split-space argument behavior
- Check repeated spaces
   - Expected: parsed.commandName equals `search`
   - Expected: parsed.args equals ` foo`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves split-space argument behavior")
step("Check repeated spaces")
if val parsed = parseSlashCommand("/search  foo"):
    expect(parsed.commandName).to_equal("search")
    expect(parsed.args).to_equal(" foo")
else:
    expect(false).to_equal(true)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5765097ec54415b5b10948f6beda79f269a51d398e537eb1d7ccdd0ec1dc6996`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5765097ec54415b5b10948f6beda79f269a51d398e537eb1d7ccdd0ec1dc6996`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5765097ec54415b5b10948f6beda79f269a51d398e537eb1d7ccdd0ec1dc6996`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/slash_command_parsing_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/slash_command_parsing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/slash_command_parsing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/slash_command_parsing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/slash_command_parsing_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses plain slash commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/slash_command_parsing_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses MCP command marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/slash_command_parsing_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trims input and rejects non-commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
