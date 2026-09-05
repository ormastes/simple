# Claude Full CLI Exit

> Checks centralized CLI exit result behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CLI Exit

Checks centralized CLI exit result behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/exit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks centralized CLI exit result behavior.

## Scenarios

### Claude full cli exit

#### models error exits

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- models error exits
- Error writes optional stderr and exits 1
   - Expected: withMessage.code equals `cliErrorExitCode()`
   - Expected: withMessage.stderr equals `bad`
   - Expected: withMessage.stdout equals ``
   - Expected: withMessage.returnedNever is true
   - Expected: empty.stderr equals ``
   - Expected: empty.code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models error exits")
step("Error writes optional stderr and exits 1")
val withMessage = cliError("bad")
expect(withMessage.code).to_equal(cliErrorExitCode())
expect(withMessage.stderr).to_equal("bad")
expect(withMessage.stdout).to_equal("")
expect(withMessage.returnedNever).to_equal(true)
val empty = cliError("")
expect(empty.stderr).to_equal("")
expect(empty.code).to_equal(1)
```

</details>

#### models ok exits

- models ok exits
- Ok writes optional stdout newline and exits 0
   - Expected: withMessage.code equals `cliOkExitCode()`
   - Expected: withMessage.stdout equals `done\n`
   - Expected: withMessage.stderr equals ``
   - Expected: cliOk("").stdout equals ``
   - Expected: cliOkAddsNewline() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models ok exits")
step("Ok writes optional stdout newline and exits 0")
val withMessage = cliOk("done")
expect(withMessage.code).to_equal(cliOkExitCode())
expect(withMessage.stdout).to_equal("done\n")
expect(withMessage.stderr).to_equal("")
expect(cliOk("").stdout).to_equal("")
expect(cliOkAddsNewline()).to_equal(true)
```

</details>

#### exports source-backed CLI exit notes

- exports source-backed CLI exit notes
- Pin centralized output targets and test-spy contracts
   - Expected: cliErrorOutputTarget() equals `stderr`
   - Expected: cliOkOutputTarget() equals `stdout`
   - Expected: centralizedCliExitPoint() is true
   - Expected: processExitLintSuppressedHere() is true
   - Expected: testsSpyOnProcessExit() is true
   - Expected: testsSpyOnConsoleError() is true
   - Expected: testsSpyOnStdoutWrite() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed CLI exit notes")
step("Pin centralized output targets and test-spy contracts")
expect(cliErrorOutputTarget()).to_equal("stderr")
expect(cliOkOutputTarget()).to_equal("stdout")
expect(centralizedCliExitPoint()).to_equal(true)
expect(processExitLintSuppressedHere()).to_equal(true)
expect(testsSpyOnProcessExit()).to_equal(true)
expect(testsSpyOnConsoleError()).to_equal(true)
expect(testsSpyOnStdoutWrite()).to_equal(true)
expect(neverReturnTypePurpose()).to_contain("narrow control flow")
expect(copiedHandlerBlockReplaced()).to_contain("exit")
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

- Canonical SPipe generation for source `f85fb9a2ed494953ff687ab5bba5bdb32a1dd805b593e7a172e59c2daee7af27`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f85fb9a2ed494953ff687ab5bba5bdb32a1dd805b593e7a172e59c2daee7af27`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f85fb9a2ed494953ff687ab5bba5bdb32a1dd805b593e7a172e59c2daee7af27`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/cli/exit_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/cli/exit_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/cli/exit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/cli/exit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/cli/exit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/cli/exit_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models error exits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/exit_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models ok exits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/exit_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports source-backed CLI exit notes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
