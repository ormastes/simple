# Claude Full Branch Command

> Mirrors `tmp/claude/claude-code-main/src/commands/branch` for branch command

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Branch Command

Mirrors `tmp/claude/claude-code-main/src/commands/branch` for branch command

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/branch_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/commands/branch` for branch command
metadata and the pure branch transcript behaviors.

## Scenarios

### Claude full branch command

#### matches command metadata and fork alias feature gate

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches command metadata and fork alias feature gate
- Load command metadata with fork subagent disabled
   - Expected: command.typeName equals `local-jsx`
   - Expected: command.name equals `branch`
   - Expected: command.aliases.len() equals `1`
   - Expected: command.aliases[0] equals `fork`
   - Expected: command.description equals `Create a branch of the current conversation at this point`
   - Expected: command.argumentHint equals `[name]`
   - Expected: command.loadPath equals `./branch.js`
- Load command metadata with fork subagent enabled
   - Expected: gated.aliases.len() equals `0`
   - Expected: branchIndexSourceLinesModeled() equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches command metadata and fork alias feature gate")
step("Load command metadata with fork subagent disabled")
val command = branchCommand(false)

expect(command.typeName).to_equal("local-jsx")
expect(command.name).to_equal("branch")
expect(command.aliases.len()).to_equal(1)
expect(command.aliases[0]).to_equal("fork")
expect(command.description).to_equal("Create a branch of the current conversation at this point")
expect(command.argumentHint).to_equal("[name]")
expect(command.loadPath).to_equal("./branch.js")

step("Load command metadata with fork subagent enabled")
val gated = branchCommand(true)
expect(gated.aliases.len()).to_equal(0)
expect(branchIndexSourceLinesModeled()).to_equal(14)
```

</details>

#### derives first prompt and collision-safe branch titles

- derives first prompt and collision-safe branch titles
- Collapse multiline user prompts to Claude's single-line title base
   - Expected: deriveFirstPrompt("  fix\n\nthis\tbug  now  ") equals `fix this bug now`
   - Expected: deriveFirstPrompt("") equals `Branched conversation`
- Apply branch suffixes and skip occupied branch names
   - Expected: getUniqueForkName("fix this bug now", existing) equals `fix this bug now (Branch 3)`
   - Expected: effectiveBranchTitle("", messages, []) equals `hello world (Branch)`
   - Expected: effectiveBranchTitle("  named branch  ", messages, []) equals `named branch (Branch)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("derives first prompt and collision-safe branch titles")
step("Collapse multiline user prompts to Claude's single-line title base")
expect(deriveFirstPrompt("  fix\n\nthis\tbug  now  ")).to_equal("fix this bug now")
expect(deriveFirstPrompt("")).to_equal("Branched conversation")

step("Apply branch suffixes and skip occupied branch names")
val existing = ["fix this bug now (Branch)", "fix this bug now (Branch 2)"]
expect(getUniqueForkName("fix this bug now", existing)).to_equal("fix this bug now (Branch 3)")

val messages = [BranchMessage.new("u1", "user", "hello\nworld", false)]
expect(effectiveBranchTitle("", messages, [])).to_equal("hello world (Branch)")
expect(effectiveBranchTitle("  named branch  ", messages, [])).to_equal("named branch (Branch)")
```

</details>

#### forks main transcript messages and preserves replacement records

- forks main transcript messages and preserves replacement records
- Build a fork from mixed main and sidechain transcript messages
   - Expected: fork.sessionId equals `fork-id`
   - Expected: fork.forkPath equals `/tmp/fork.jsonl`
   - Expected: fork.serializedMessages.len() equals `3`
   - Expected: fork.entries.len() equals `3`
   - Expected: fork.entries[0].parentUuid equals ``
   - Expected: fork.entries[1].parentUuid equals `u1`
   - Expected: fork.entries[2].parentUuid equals `u1`
   - Expected: fork.entries[2].forkedFromSessionId equals `orig`
   - Expected: fork.contentReplacementCount equals `1`
   - Expected: branchSourceLinesModeled() equals `296`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forks main transcript messages and preserves replacement records")
step("Build a fork from mixed main and sidechain transcript messages")
val messages = [
    BranchMessage.new("u1", "user", "hello", false),
    BranchMessage.new("s1", "assistant", "side", true),
    BranchMessage.new("p1", "progress", "tick", false),
    BranchMessage.new("a1", "assistant", "done", false),
]
val replacements = [
    BranchReplacement.new("orig", "tool-result-preview"),
    BranchReplacement.new("other", "ignore"),
]
val fork = createFork("orig", "fork-id", "/tmp/fork.jsonl", "named", messages, replacements)

expect(fork.sessionId).to_equal("fork-id")
expect(fork.forkPath).to_equal("/tmp/fork.jsonl")
expect(fork.serializedMessages.len()).to_equal(3)
expect(fork.entries.len()).to_equal(3)
expect(fork.entries[0].parentUuid).to_equal("")
expect(fork.entries[1].parentUuid).to_equal("u1")
expect(fork.entries[2].parentUuid).to_equal("u1")
expect(fork.entries[2].forkedFromSessionId).to_equal("orig")
expect(fork.contentReplacementCount).to_equal(1)
expect(branchSourceLinesModeled()).to_equal(296)
```

</details>

#### returns resume and fallback completion messages

- returns resume and fallback completion messages
- Resume into the fork when a resume callback is available
   - Expected: resumed.ok is true
   - Expected: resumed.resumedSessionId equals `fork-id`
   - Expected: resumed.resumeMode equals `fork`
- Fall back to slash resume when no resume callback exists
   - Expected: fallback.doneMessage equals `Branched conversation. Resume with: /resume fork-id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns resume and fallback completion messages")
step("Resume into the fork when a resume callback is available")
val fork = createFork("orig", "fork-id", "/tmp/fork.jsonl", "named", [BranchMessage.new("u1", "user", "hello", false)], [])
val resumed = callBranch("orig", fork, "named", true)
expect(resumed.ok).to_equal(true)
expect(resumed.resumedSessionId).to_equal("fork-id")
expect(resumed.resumeMode).to_equal("fork")
expect(resumed.doneMessage).to_contain("Branched conversation \"named\". You are now in the branch.")
expect(resumed.doneMessage).to_contain("claude -r orig")

step("Fall back to slash resume when no resume callback exists")
val fallback = callBranch("orig", fork, "", false)
expect(fallback.doneMessage).to_equal("Branched conversation. Resume with: /resume fork-id")
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

- Canonical SPipe generation for source `f4ba3b2f62b6ab1a7e9cc1d2bd515d8021846b1fb328b8a4dcb7b3010dc3f0ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f4ba3b2f62b6ab1a7e9cc1d2bd515d8021846b1fb328b8a4dcb7b3010dc3f0ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f4ba3b2f62b6ab1a7e9cc1d2bd515d8021846b1fb328b8a4dcb7b3010dc3f0ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/commands/branch_command_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/branch_command_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/branch_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/branch_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/branch_command_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/commands/branch_command_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches command metadata and fork alias feature gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/branch_command_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives first prompt and collision-safe branch titles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/branch_command_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'forks main transcript messages and preserves replacement records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
