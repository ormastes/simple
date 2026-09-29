# Claude Full Bash Read-Only Validation Slice

> Focused coverage for top-level read-only command routing from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bash Read-Only Validation Slice

Focused coverage for top-level read-only command routing from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tools/BashTool/readOnlyValidation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused coverage for top-level read-only command routing from
tools/BashTool/readOnlyValidation.ts.

## Scenarios

### Claude full bash read only validation parity

#### should model read only allow routes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model read only allow routes
- Check allow routes
   - Expected: checkReadOnlyConstraintsRoute("pwd", true, false, false, false) equals `allow`
   - Expected: checkReadOnlyConstraintsRoute("echo hi 2>&1", true, false, false, false) equals `allow`
   - Expected: isCommandSafeViaFlagParsingRoute("git status") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model read only allow routes")
step("Check allow routes")
expect(checkReadOnlyConstraintsRoute("pwd", true, false, false, false)).to_equal("allow")
expect(checkReadOnlyConstraintsRoute("echo hi 2>&1", true, false, false, false)).to_equal("allow")
expect(isCommandSafeViaFlagParsingRoute("git status")).to_equal(true)
```

</details>

#### should model passthrough safety gates

- should model passthrough safety gates
- Check passthrough routes
   - Expected: checkReadOnlyConstraintsRoute("malformed", false, false, false, false) equals `passthrough`
   - Expected: checkReadOnlyConstraintsRoute("cat *", true, false, false, false) equals `passthrough`
   - Expected: checkReadOnlyConstraintsRoute("uniq --skip-chars=0$_", true, false, false, false) equals `passthrough`
   - Expected: checkReadOnlyConstraintsRoute("git -c core.fsmonitor=true status", true, false, false, false) equals `passthrough`
   - Expected: checkReadOnlyConstraintsRoute("git --exec-path=/tmp/bin status", true, false, false, false) equals `passthrough`
   - Expected: checkReadOnlyConstraintsRoute("git --config-env=foo status", true, false, false, false) equals `passthrough`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model passthrough safety gates")
step("Check passthrough routes")
expect(checkReadOnlyConstraintsRoute("malformed", false, false, false, false)).to_equal("passthrough")
expect(checkReadOnlyConstraintsRoute("cat *", true, false, false, false)).to_equal("passthrough")
expect(checkReadOnlyConstraintsRoute("uniq --skip-chars=0$_", true, false, false, false)).to_equal("passthrough")
expect(checkReadOnlyConstraintsRoute("git -c core.fsmonitor=true status", true, false, false, false)).to_equal("passthrough")
expect(checkReadOnlyConstraintsRoute("git --exec-path=/tmp/bin status", true, false, false, false)).to_equal("passthrough")
expect(checkReadOnlyConstraintsRoute("git --config-env=foo status", true, false, false, false)).to_equal("passthrough")
```

</details>

#### should model path and git escape routes

- should model path and git escape routes
- Check path risk routes
   - Expected: checkReadOnlyConstraintsRoute("cat //server/share/file", true, true, false, false) equals `ask unc path`
   - Expected: checkReadOnlyConstraintsRoute("cd /tmp && git status", true, false, false, false) equals `passthrough`
   - Expected: checkReadOnlyConstraintsRoute("git status", true, false, true, false) equals `passthrough`
   - Expected: checkReadOnlyConstraintsRoute("git status", true, false, false, true) equals `passthrough`
   - Expected: checkReadOnlyConstraintsRoute("echo x > hooks/pre-commit && git status", true, false, false, false) equals `passthrough`
   - Expected: bashReadOnlyValidationSourceLinesModeled() equals `1990`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model path and git escape routes")
step("Check path risk routes")
expect(checkReadOnlyConstraintsRoute("cat //server/share/file", true, true, false, false)).to_equal("ask unc path")
expect(checkReadOnlyConstraintsRoute("cd /tmp && git status", true, false, false, false)).to_equal("passthrough")
expect(checkReadOnlyConstraintsRoute("git status", true, false, true, false)).to_equal("passthrough")
expect(checkReadOnlyConstraintsRoute("git status", true, false, false, true)).to_equal("passthrough")
expect(checkReadOnlyConstraintsRoute("echo x > hooks/pre-commit && git status", true, false, false, false)).to_equal("passthrough")
expect(bashReadOnlyValidationSourceLinesModeled()).to_equal(1990)
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

- Canonical SPipe generation for source `0d7c2159a98992725064e421b4a42fbf216c378a840bff9c6d2d37442df85fda`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d7c2159a98992725064e421b4a42fbf216c378a840bff9c6d2d37442df85fda`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d7c2159a98992725064e421b4a42fbf216c378a840bff9c6d2d37442df85fda`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/tools/BashTool/readOnlyValidation_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/tools/BashTool/readOnlyValidation_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/tools/BashTool/readOnlyValidation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/tools/BashTool/readOnlyValidation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/tools/BashTool/readOnlyValidation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/tools/BashTool/readOnlyValidation_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model read only allow routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/BashTool/readOnlyValidation_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model read only allow routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/BashTool/readOnlyValidation_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model passthrough safety gates' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/BashTool/readOnlyValidation_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model passthrough safety gates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/BashTool/readOnlyValidation_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model path and git escape routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/BashTool/readOnlyValidation_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model path and git escape routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
