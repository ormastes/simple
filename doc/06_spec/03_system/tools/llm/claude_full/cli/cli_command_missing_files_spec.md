# Claude Full CLI/Command Missing Files

> Checks the three missing full-parity targets requested for this lane.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CLI/Command Missing Files

Checks the three missing full-parity targets requested for this lane.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/cli_command_missing_files_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the three missing full-parity targets requested for this lane.

## Scenarios

### Claude full CLI command missing files

#### should create the requested full-parity files at target size

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should create the requested full-parity files at target size
- Check exact target paths and minimum source LOC
   - Expected: file_exists("src/app/llm_caret/claude_full/cli/print.spl") is true
   - Expected: file_exists("src/app/llm_caret/claude_full/cli/update.spl") is true
   - Expected: file_exists("src/app/llm_caret/claude_full/commands/add-dir/add-dir.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create the requested full-parity files at target size")
step("Check exact target paths and minimum source LOC")
expect(file_exists("src/app/llm_caret/claude_full/cli/print.spl")).to_equal(true)
expect(file_exists("src/app/llm_caret/claude_full/cli/update.spl")).to_equal(true)
expect(file_exists("src/app/llm_caret/claude_full/commands/add-dir/add-dir.spl")).to_equal(true)
expect(sourceLineCount("src/app/llm_caret/claude_full/cli/print.spl")).to_be_greater_than(5593)
expect(sourceLineCount("src/app/llm_caret/claude_full/cli/update.spl")).to_be_greater_than(421)
expect(sourceLineCount("src/app/llm_caret/claude_full/commands/add-dir/add-dir.spl")).to_be_greater_than(124)
```

</details>

#### should model print prompt batching and control responses

- should model print prompt batching and control responses
- Exercise the minimal print behavior used by the CLI mirror
   - Expected: toBlocks(user) equals `["hello", "world"]`
   - Expected: joinPromptValues([user, nextUser]) equals `hello\nworld\nagain`
   - Expected: canBatchWith(user, nextUser) is true
   - Expected: canBatchWith(user, tool) is false
   - Expected: trackReceivedMessageUuid(["a"], "a") equals `["a"]`
   - Expected: trackReceivedMessageUuid(["a"], "b") equals `["a", "b"]`
   - Expected: sendControlResponseSuccess("r1", "ok") equals `control_response|r1|success|ok`
   - Expected: sendControlResponseError("r1", "bad") equals `control_response|r1|error|bad`
   - Expected: removeInterruptedMessage(["keep", "interrupted", "done"]) equals `["keep", "done"]`
   - Expected: toScopedConfig("project", "server") equals `project:server`
   - Expected: printSourceLinesModeled() equals `5594`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model print prompt batching and control responses")
step("Exercise the minimal print behavior used by the CLI mirror")
val user = PromptValue.new("user", "hello\nworld")
val nextUser = PromptValue.new("user", "again")
val tool = PromptValue.new("tool", "result")
expect(toBlocks(user)).to_equal(["hello", "world"])
expect(joinPromptValues([user, nextUser])).to_equal("hello\nworld\nagain")
expect(canBatchWith(user, nextUser)).to_equal(true)
expect(canBatchWith(user, tool)).to_equal(false)
expect(trackReceivedMessageUuid(["a"], "a")).to_equal(["a"])
expect(trackReceivedMessageUuid(["a"], "b")).to_equal(["a", "b"])
expect(sendControlResponseSuccess("r1", "ok")).to_equal("control_response|r1|success|ok")
expect(sendControlResponseError("r1", "bad")).to_equal("control_response|r1|error|bad")
expect(removeInterruptedMessage(["keep", "interrupted", "done"])).to_equal(["keep", "done"])
expect(toScopedConfig("project", "server")).to_equal("project:server")
expect(printSourceLinesModeled()).to_equal(5594)
```

</details>

#### should model update decisions

- should model update decisions
- Check current, available, and auto-update outcomes
   - Expected: update("1.0.0", "1.0.0", false) equals `current:1.0.0`
   - Expected: update("1.0.0", "1.1.0", false) equals `available:1.1.0`
   - Expected: update("1.0.0", "1.1.0", true) equals `updated:1.0.0->1.1.0`
   - Expected: updateSourceLinesModeled() equals `422`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model update decisions")
step("Check current, available, and auto-update outcomes")
expect(update("1.0.0", "1.0.0", false)).to_equal("current:1.0.0")
expect(update("1.0.0", "1.1.0", false)).to_equal("available:1.1.0")
expect(update("1.0.0", "1.1.0", true)).to_equal("updated:1.0.0->1.1.0")
expect(updateSourceLinesModeled()).to_equal(422)
```

</details>

#### should keep add-dir command symbols in the hyphenated source file

- should keep add-dir command symbols in the hyphenated source file
- The hyphenated path is checked as source text because it is not import-friendly


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep add-dir command symbols in the hyphenated source file")
step("The hyphenated path is checked as source text because it is not import-friendly")
val source = sourceText("src/app/llm_caret/claude_full/commands/add-dir/add-dir.spl")
expect(source).to_contain("class AddDirError:")
expect(source).to_contain("fn call(path: text, exists: bool, alreadyAdded: bool) -> text:")
expect(source).to_contain("fn handleAddDirectory(path: text, exists: bool, alreadyAdded: bool) -> text:")
expect(source).to_contain("return \"error:missing-directory\"")
expect(source).to_contain("\"ok:added:\" + path")
expect(source).to_contain("fn addDirSourceLinesModeled() -> i64:")
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

- Canonical SPipe generation for source `dafb2b6214f0d73bf0608e27b9cdeb6941d32eb68dc53f5d410c231e1f383ef2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dafb2b6214f0d73bf0608e27b9cdeb6941d32eb68dc53f5d410c231e1f383ef2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dafb2b6214f0d73bf0608e27b9cdeb6941d32eb68dc53f5d410c231e1f383ef2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/03_system/tools/llm/claude_full/cli/cli_command_missing_files_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/cli/cli_command_missing_files_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/cli/cli_command_missing_files_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/cli/cli_command_missing_files_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/cli/cli_command_missing_files_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/cli/cli_command_missing_files_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create the requested full-parity files at target size' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/cli_command_missing_files_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create the requested full-parity files at target size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/cli_command_missing_files_spec.spl:41:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model print prompt batching and control responses' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/cli_command_missing_files_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model print prompt batching and control responses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/cli_command_missing_files_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model update decisions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/cli_command_missing_files_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model update decisions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/cli_command_missing_files_spec.spl:69:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep add-dir command symbols in the hyphenated source file' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
