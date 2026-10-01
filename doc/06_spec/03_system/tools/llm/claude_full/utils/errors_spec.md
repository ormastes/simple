# Claude Full Errors

> Checks error classes and small helper predicates.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Errors

Checks error classes and small helper predicates.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/errors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks error classes and small helper predicates.

## Scenarios

### Claude full errors

#### should expose core error classes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose core error classes
   - Expected: ClaudeError.new("bad").name equals `ClaudeError`
   - Expected: MalformedCommandError.new("malformed").message equals `malformed`
   - Expected: AbortError.new("stop").name equals `AbortError`
   - Expected: isAbortErrorName("AbortError") is true
   - Expected: isAbortErrorName("Other") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose core error classes")
expect(ClaudeError.new("bad").name).to_equal("ClaudeError")
expect(MalformedCommandError.new("malformed").message).to_equal("malformed")
expect(AbortError.new("stop").name).to_equal("AbortError")
expect(isAbortErrorName("AbortError")).to_equal(true)
expect(isAbortErrorName("Other")).to_equal(false)
```

</details>

#### should expose config shell and teleport errors

- should expose config shell and teleport errors
   - Expected: config.name equals `ConfigParseError`
   - Expected: config.filePath equals `/tmp/c.json`
   - Expected: shell.message equals `Shell command failed`
   - Expected: shell.code equals `7`
   - Expected: shell.interrupted is true
   - Expected: teleport.formattedMessage equals `formatted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose config shell and teleport errors")
val config = ConfigParseError.new("bad config", "/tmp/c.json", "{}")
expect(config.name).to_equal("ConfigParseError")
expect(config.filePath).to_equal("/tmp/c.json")
val shell = ShellError.new("out", "err", 7, true)
expect(shell.message).to_equal("Shell command failed")
expect(shell.code).to_equal(7)
expect(shell.interrupted).to_equal(true)
val teleport = TeleportOperationError.new("failed", "formatted")
expect(teleport.formattedMessage).to_equal("formatted")
```

</details>

#### should expose telemetry safe error and helpers

- should expose telemetry safe error and helpers
   - Expected: same.name equals `TelemetrySafeError`
   - Expected: same.telemetryMessage equals `timeout`
   - Expected: redacted.telemetryMessage equals `timeout`
   - Expected: hasExactErrorMessage("x", "x") is true
   - Expected: isEnoent("ENOENT") is true
   - Expected: isEacces("EACCES") is true
   - Expected: errorsSourceLinesModeled() equals `238`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose telemetry safe error and helpers")
val same = TelemetrySafeError_I_VERIFIED_THIS_IS_NOT_CODE_OR_FILEPATHS.new("timeout", "")
expect(same.name).to_equal("TelemetrySafeError")
expect(same.telemetryMessage).to_equal("timeout")
val redacted = TelemetrySafeError_I_VERIFIED_THIS_IS_NOT_CODE_OR_FILEPATHS.new("timeout /tmp/a", "timeout")
expect(redacted.telemetryMessage).to_equal("timeout")
expect(hasExactErrorMessage("x", "x")).to_equal(true)
expect(isEnoent("ENOENT")).to_equal(true)
expect(isEacces("EACCES")).to_equal(true)
expect(errorsSourceLinesModeled()).to_equal(238)
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

- Canonical SPipe generation for source `8d0ae7a6eaa84577d1c4edbcac6d2cf0476179f26af01c25a1d6284c43ad6ce5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8d0ae7a6eaa84577d1c4edbcac6d2cf0476179f26af01c25a1d6284c43ad6ce5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8d0ae7a6eaa84577d1c4edbcac6d2cf0476179f26af01c25a1d6284c43ad6ce5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/errors_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/errors_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/errors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/errors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/errors_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/errors_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose core error classes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/errors_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose core error classes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/errors_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose config shell and teleport errors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/errors_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose config shell and teleport errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/errors_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose telemetry safe error and helpers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/errors_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose telemetry safe error and helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
