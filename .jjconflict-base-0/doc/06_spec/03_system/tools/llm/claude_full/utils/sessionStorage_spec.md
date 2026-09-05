# Claude Full Session Storage Project

> Checks Project parity for encoded project paths, transcript append chains,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Session Storage Project

Checks Project parity for encoded project paths, transcript append chains,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/sessionStorage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks Project parity for encoded project paths, transcript append chains,
message removal, flush state, and test reset hooks.

## Scenarios

### Claude full utils sessionStorage Project

#### tracks a project transcript chain and flush snapshot

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tracks a project transcript chain and flush snapshot
- Create a project in an encoded cwd and append two message entries
   - Expected: project.dir equals `~/.claude/projects/-home-dev-my repo`
   - Expected: withAssistant.transcriptPath() equals `~/.claude/projects/-home-dev-my repo/session-1.jsonl`
   - Expected: withAssistant.messages.len() equals `2`
   - Expected: withAssistant.messages[1].parentUuid equals `u1`
   - Expected: withAssistant.lastUuid() equals `a1`
   - Expected: sessionIdExists(withAssistant, "session-1") is true
- Remove a message, flush the JSONL-style snapshot, and reset flush state
   - Expected: removed.messages.len() equals `1`
   - Expected: flushed.flushState.pending is false
   - Expected: flushed.flushState.flushCount equals `1`
   - Expected: reset.flushState.flushCount equals `0`
   - Expected: sessionStorageSourceLinesModeled() equals `4018`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks a project transcript chain and flush snapshot")
step("Create a project in an encoded cwd and append two message entries")
val project = getProject("/home/dev/my repo", "session-1")
val withUser = project.addMessage("u1", "user", "hello")
val withAssistant = withUser.addMessage("a1", "assistant", "world")

expect(project.dir).to_equal("~/.claude/projects/-home-dev-my repo")
expect(withAssistant.transcriptPath()).to_equal("~/.claude/projects/-home-dev-my repo/session-1.jsonl")
expect(withAssistant.messages.len()).to_equal(2)
expect(withAssistant.messages[1].parentUuid).to_equal("u1")
expect(withAssistant.lastUuid()).to_equal("a1")
expect(sessionIdExists(withAssistant, "session-1")).to_equal(true)

step("Remove a message, flush the JSONL-style snapshot, and reset flush state")
val removed = withAssistant.removeTranscriptMessage("u1")
val flushed = removed.flush()
val reset = resetProjectFlushStateForTesting(flushed)

expect(removed.messages.len()).to_equal(1)
expect(flushed.flushState.pending).to_equal(false)
expect(flushed.flushState.flushCount).to_equal(1)
expect(flushed.flushState.lastWrite).to_contain("a1")
expect(reset.flushState.flushCount).to_equal(0)
expect(sessionStorageSourceLinesModeled()).to_equal(4018)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `43aa8c8ef971a21abde56605183d3c941c2f7f5d421e690d59373806122ba588`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `43aa8c8ef971a21abde56605183d3c941c2f7f5d421e690d59373806122ba588`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `43aa8c8ef971a21abde56605183d3c941c2f7f5d421e690d59373806122ba588`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/tools/llm/claude_full/utils/sessionStorage_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/sessionStorage_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/sessionStorage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/sessionStorage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/sessionStorage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/sessionStorage_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks a project transcript chain and flush snapshot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
