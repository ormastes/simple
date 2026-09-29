# Claude Full useTypeahead Slice

> Pure Simple/TUI-compatible typeahead helper coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full useTypeahead Slice

Pure Simple/TUI-compatible typeahead helper coverage.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/hooks/useTypeahead_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple/TUI-compatible typeahead helper coverage.

## Scenarios

### Claude full useTypeahead parity

#### should extract completion and search tokens

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should extract completion and search tokens
- Check token extraction
   - Expected: extractCompletionTokenRoute("", 0) equals `nil`
   - Expected: extractCompletionTokenRoute("open @src/ma", 12) equals `5|@src/ma`
   - Expected: extractCompletionTokenRoute("run foobar", 6) equals `4|fo`
   - Expected: extractSearchTokenRoute("@src/main") equals `src/main`
   - Expected: extractSearchTokenRoute("@\"quoted value\"") equals `quoted value`
   - Expected: extractSearchTokenRoute("@'quoted value'") equals `quoted value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should extract completion and search tokens")
step("Check token extraction")
expect(extractCompletionTokenRoute("", 0)).to_equal("nil")
expect(extractCompletionTokenRoute("open @src/ma", 12)).to_equal("5|@src/ma")
expect(extractCompletionTokenRoute("run foobar", 6)).to_equal("4|fo")
expect(extractSearchTokenRoute("@src/main")).to_equal("src/main")
expect(extractSearchTokenRoute("@\"quoted value\"")).to_equal("quoted value")
expect(extractSearchTokenRoute("@'quoted value'")).to_equal("quoted value")
```

</details>

#### should format prompt and shell replacements

- should format prompt and shell replacements
- Check replacement quoting
   - Expected: formatPromptReplacementRoute("src/main") equals `@src/main`
   - Expected: formatPromptReplacementRoute("quoted value") equals `@"quoted value"`
   - Expected: formatBashReplacementRoute("$HOME") equals `$HOME`
   - Expected: formatBashReplacementRoute("two words") equals `"two words"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should format prompt and shell replacements")
step("Check replacement quoting")
expect(formatPromptReplacementRoute("src/main")).to_equal("@src/main")
expect(formatPromptReplacementRoute("quoted value")).to_equal("@\"quoted value\"")
expect(formatBashReplacementRoute("$HOME")).to_equal("$HOME")
expect(formatBashReplacementRoute("two words")).to_equal("\"two words\"")
```

</details>

#### should apply suggestions and preserve selection state

- should apply suggestions and preserve selection state
- Check TUI insertion helpers
   - Expected: applyDirectorySuggestionRoute("open @src", 5, 9, "src/app") equals `open @src/app/`
   - Expected: applyShellSuggestionRoute("echo two", 5, 8, "two words") equals `echo "two words"`
   - Expected: preservedSelectionRoute("src/app", 2, 5) equals `src/app`
   - Expected: preservedSelectionRoute("", 2, 5) equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should apply suggestions and preserve selection state")
step("Check TUI insertion helpers")
expect(applyDirectorySuggestionRoute("open @src", 5, 9, "src/app")).to_equal("open @src/app/")
expect(applyShellSuggestionRoute("echo two", 5, 8, "two words")).to_equal("echo \"two words\"")
expect(preservedSelectionRoute("src/app", 2, 5)).to_equal("src/app")
expect(preservedSelectionRoute("", 2, 5)).to_equal("nil")
```

</details>

#### should detect command arguments

- should detect command arguments
- Check command argument detection
   - Expected: hasCommandWithArgumentsRoute("git") is false
   - Expected: hasCommandWithArgumentsRoute("git status") is true
   - Expected: hasCommandWithArgumentsRoute("git    status") is true
   - Expected: hasCommandWithArgumentsRoute("git\tstatus") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should detect command arguments")
step("Check command argument detection")
expect(hasCommandWithArgumentsRoute("git")).to_equal(false)
expect(hasCommandWithArgumentsRoute("git status")).to_equal(true)
expect(hasCommandWithArgumentsRoute("git    status")).to_equal(true)
expect(hasCommandWithArgumentsRoute("git\tstatus")).to_equal(true)
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

- Canonical SPipe generation for source `e7d1ad431769314c6079fb76a072ce045bc9f15e73f2930155446006ba691f9f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e7d1ad431769314c6079fb76a072ce045bc9f15e73f2930155446006ba691f9f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e7d1ad431769314c6079fb76a072ce045bc9f15e73f2930155446006ba691f9f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/tools/llm/claude_full/hooks/useTypeahead_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/hooks/useTypeahead_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/hooks/useTypeahead_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/hooks/useTypeahead_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/hooks/useTypeahead_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should extract completion and search tokens' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/hooks/useTypeahead_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should extract completion and search tokens' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/hooks/useTypeahead_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should format prompt and shell replacements' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/hooks/useTypeahead_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should format prompt and shell replacements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/hooks/useTypeahead_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should apply suggestions and preserve selection state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/hooks/useTypeahead_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should apply suggestions and preserve selection state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/hooks/useTypeahead_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should detect command arguments' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
