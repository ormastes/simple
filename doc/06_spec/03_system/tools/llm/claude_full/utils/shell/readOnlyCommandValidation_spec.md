# Claude Full Shell Read-Only Command Validation Slice

> Focused coverage for flag, UNC, GitHub, and git-tag routes from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Shell Read-Only Command Validation Slice

Focused coverage for flag, UNC, GitHub, and git-tag routes from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/shell/readOnlyCommandValidation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused coverage for flag, UNC, GitHub, and git-tag routes from
utils/shell/readOnlyCommandValidation.ts.

## Scenarios

### Claude full shell read only command validation parity

#### should model flag argument validation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model flag argument validation
- Check flag argument routes
   - Expected: validateFlagArgumentRoute("3", "number") is true
   - Expected: validateFlagArgumentRoute("3a", "number") is false
   - Expected: validateFlagArgumentRoute("x", "char") is true
   - Expected: validateFlagArgumentRoute("xy", "char") is false
   - Expected: validateFlagArgumentRoute("{}", "{}") is true
   - Expected: validateFlagArgumentRoute("x", "{}") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model flag argument validation")
step("Check flag argument routes")
expect(validateFlagArgumentRoute("3", "number")).to_equal(true)
expect(validateFlagArgumentRoute("3a", "number")).to_equal(false)
expect(validateFlagArgumentRoute("x", "char")).to_equal(true)
expect(validateFlagArgumentRoute("xy", "char")).to_equal(false)
expect(validateFlagArgumentRoute("{}", "{}")).to_equal(true)
expect(validateFlagArgumentRoute("x", "{}")).to_equal(false)
```

</details>

#### should model UNC and gh dangerous routes

- should model UNC and gh dangerous routes
- Check path and gh routes
   - Expected: containsVulnerableUncPathRoute("//server/share", false) is false
   - Expected: containsVulnerableUncPathRoute("//server/share", true) is true
   - Expected: containsVulnerableUncPathRoute("\\\\server\\share", true) is true
   - Expected: containsVulnerableUncPathRoute("https://host/x", true) is false
   - Expected: ghIsDangerousCallbackRoute("--repo=evil.com/secret/x") is true
   - Expected: ghIsDangerousCallbackRoute("https://evil.com/owner/repo/pull/1") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model UNC and gh dangerous routes")
step("Check path and gh routes")
expect(containsVulnerableUncPathRoute("//server/share", false)).to_equal(false)
expect(containsVulnerableUncPathRoute("//server/share", true)).to_equal(true)
expect(containsVulnerableUncPathRoute("\\\\server\\share", true)).to_equal(true)
expect(containsVulnerableUncPathRoute("https://host/x", true)).to_equal(false)
expect(ghIsDangerousCallbackRoute("--repo=evil.com/secret/x")).to_equal(true)
expect(ghIsDangerousCallbackRoute("https://evil.com/owner/repo/pull/1")).to_equal(true)
```

</details>

#### should model flag scanning and git tag routes

- should model flag scanning and git tag routes
- Check flag scanning
   - Expected: validateFlagsRoute("git log -- --not-a-flag", true) equals `stop at double dash`
   - Expected: validateFlagsRoute("git log -- --still-scan", false) equals `scan past double dash`
   - Expected: validateFlagsRoute("rg -E=", true) equals `reject empty inline arg`
   - Expected: validateFlagsRoute("grep -rI x", true) equals `reject bundled arg flag`
   - Expected: validateFlagsRoute("git diff -3", true) equals `accept git numeric shorthand`
   - Expected: gitTagRoute("git tag v1") equals `git tag creation blocked`
   - Expected: gitTagRoute("git tag -l foo") equals `git tag list safe`
   - Expected: shellReadOnlyCommandValidationSourceLinesModeled() equals `1893`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model flag scanning and git tag routes")
step("Check flag scanning")
expect(validateFlagsRoute("git log -- --not-a-flag", true)).to_equal("stop at double dash")
expect(validateFlagsRoute("git log -- --still-scan", false)).to_equal("scan past double dash")
expect(validateFlagsRoute("rg -E=", true)).to_equal("reject empty inline arg")
expect(validateFlagsRoute("grep -rI x", true)).to_equal("reject bundled arg flag")
expect(validateFlagsRoute("git diff -3", true)).to_equal("accept git numeric shorthand")
expect(gitTagRoute("git tag v1")).to_equal("git tag creation blocked")
expect(gitTagRoute("git tag -l foo")).to_equal("git tag list safe")
expect(shellReadOnlyCommandValidationSourceLinesModeled()).to_equal(1893)
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

- Canonical SPipe generation for source `7935f2397411b3b094904bc7f324db901de0c6b4a098bb0504be83c9648c0bff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7935f2397411b3b094904bc7f324db901de0c6b4a098bb0504be83c9648c0bff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7935f2397411b3b094904bc7f324db901de0c6b4a098bb0504be83c9648c0bff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/shell/readOnlyCommandValidation_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/shell/readOnlyCommandValidation_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/shell/readOnlyCommandValidation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/shell/readOnlyCommandValidation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/shell/readOnlyCommandValidation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/shell/readOnlyCommandValidation_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model flag argument validation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/shell/readOnlyCommandValidation_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model flag argument validation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/shell/readOnlyCommandValidation_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model UNC and gh dangerous routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/shell/readOnlyCommandValidation_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model UNC and gh dangerous routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/shell/readOnlyCommandValidation_spec.spl:41:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model flag scanning and git tag routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/shell/readOnlyCommandValidation_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model flag scanning and git tag routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
