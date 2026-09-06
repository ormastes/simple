# Claude Full Bash ParsedCommand

> Checks regex fallback and tree-sitter parsed command surfaces.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bash ParsedCommand

Checks regex fallback and tree-sitter parsed command surfaces.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/bash/ParsedCommand_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks regex fallback and tree-sitter parsed command surfaces.

## Scenarios

### Claude full ParsedCommand

#### should expose regex parsed command behavior

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose regex parsed command behavior
   - Expected: parsed.toString() equals `echo one | grep o > out.txt`
   - Expected: parsed.getPipeSegments() equals `["echo one", "grep o > out.txt"]`
   - Expected: parsed.withoutOutputRedirections() equals `echo one | grep o`
   - Expected: parsed.getOutputRedirections()[0].target equals `out.txt`
   - Expected: parsed.getOutputRedirections()[0].operator equals `>`
   - Expected: parsed.getTreeSitterAnalysis().summary equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose regex parsed command behavior")
val parsed = RegexParsedCommand_DEPRECATED.new("echo one | grep o > out.txt")
expect(parsed.toString()).to_equal("echo one | grep o > out.txt")
expect(parsed.getPipeSegments()).to_equal(["echo one", "grep o > out.txt"])
expect(parsed.withoutOutputRedirections()).to_equal("echo one | grep o")
expect(parsed.getOutputRedirections()[0].target).to_equal("out.txt")
expect(parsed.getOutputRedirections()[0].operator).to_equal(">")
expect(parsed.getTreeSitterAnalysis().summary).to_equal("")
```

</details>

#### should expose tree-sitter parsed command behavior

- should expose tree-sitter parsed command behavior
   - Expected: parsed.toString() equals `printf ok | tee >> log.txt`
   - Expected: parsed.getPipeSegments() equals `["printf ok", "tee >> log.txt"]`
   - Expected: parsed.withoutOutputRedirections() equals `printf ok | tee`
   - Expected: parsed.getOutputRedirections()[0].operator equals `>>`
   - Expected: parsed.getTreeSitterAnalysis().safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose tree-sitter parsed command behavior")
val redir = OutputRedirection.new("log.txt", ">>")
val parsed = TreeSitterParsedCommand.new("printf ok | tee >> log.txt", [10], [redir], TreeSitterAnalysis.new(true, "safe"))
expect(parsed.toString()).to_equal("printf ok | tee >> log.txt")
expect(parsed.getPipeSegments()).to_equal(["printf ok", "tee >> log.txt"])
expect(parsed.withoutOutputRedirections()).to_equal("printf ok | tee")
expect(parsed.getOutputRedirections()[0].operator).to_equal(">>")
expect(parsed.getTreeSitterAnalysis().safe).to_equal(true)
```

</details>

#### should build parsed commands from precomputed root data

- should build parsed commands from precomputed root data
   - Expected: built.getPipeSegments() equals `["echo ok"]`
   - Expected: parseParsedCommand("echo fallback", false).toString() equals `echo fallback`
   - Expected: parsedCommandSourceLinesModeled() equals `318`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should build parsed commands from precomputed root data")
val built = buildParsedCommandFromRoot("echo ok", [], [], TreeSitterAnalysis.new(true, "ok"))
expect(built.getPipeSegments()).to_equal(["echo ok"])
expect(parseParsedCommand("echo fallback", false).toString()).to_equal("echo fallback")
expect(parsedCommandSourceLinesModeled()).to_equal(318)
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

- Canonical SPipe generation for source `29add594c87d61cbe2563cd193c6a8f177407ee0f96229f7f6edbce2e9f08597`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `29add594c87d61cbe2563cd193c6a8f177407ee0f96229f7f6edbce2e9f08597`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `29add594c87d61cbe2563cd193c6a8f177407ee0f96229f7f6edbce2e9f08597`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/bash/ParsedCommand_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/bash/ParsedCommand_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/bash/ParsedCommand_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/bash/ParsedCommand_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/bash/ParsedCommand_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/bash/ParsedCommand_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose regex parsed command behavior' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/bash/ParsedCommand_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose regex parsed command behavior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/bash/ParsedCommand_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose tree-sitter parsed command behavior' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/bash/ParsedCommand_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose tree-sitter parsed command behavior' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/bash/ParsedCommand_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should build parsed commands from precomputed root data' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/bash/ParsedCommand_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should build parsed commands from precomputed root data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
