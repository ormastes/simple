# Claude Full Bash Security Slice

> Focused coverage for sync-safe gate routes from tools/BashTool/bashSecurity.ts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bash Security Slice

Focused coverage for sync-safe gate routes from tools/BashTool/bashSecurity.ts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tools/BashTool/bashSecurity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused coverage for sync-safe gate routes from tools/BashTool/bashSecurity.ts.

## Scenarios

### Claude full bash security parity

#### should model empty and incomplete command routes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model empty and incomplete command routes
- Check command gate basics
   - Expected: bashCommandIsSafeDeprecatedRoute("") equals `passthrough`
   - Expected: bashCommandIsSafeDeprecatedRoute("   \t ") equals `passthrough`
   - Expected: bashCommandIsSafeDeprecatedRoute("\tgit status") equals `ask incomplete command`
   - Expected: bashCommandIsSafeDeprecatedRoute("&& whoami") equals `ask incomplete command`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model empty and incomplete command routes")
step("Check command gate basics")
expect(bashCommandIsSafeDeprecatedRoute("")).to_equal("passthrough")
expect(bashCommandIsSafeDeprecatedRoute("   \t ")).to_equal("passthrough")
expect(bashCommandIsSafeDeprecatedRoute("\tgit status")).to_equal("ask incomplete command")
expect(bashCommandIsSafeDeprecatedRoute("&& whoami")).to_equal("ask incomplete command")
```

</details>

#### should model heredoc substitution routes

- should model heredoc substitution routes
- Check heredoc routes
   - Expected: stripSafeHeredocSubstitutionsRoute(true, true) equals `stripped safe heredoc substitution`
   - Expected: hasSafeHeredocSubstitutionRoute(true, true) is true
   - Expected: hasSafeHeredocSubstitutionRoute(false, true) is false
   - Expected: bashCommandIsSafeDeprecatedRoute("$(cat <<'EOF' ok EOF)") equals `passthrough`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model heredoc substitution routes")
step("Check heredoc routes")
expect(stripSafeHeredocSubstitutionsRoute(true, true)).to_equal("stripped safe heredoc substitution")
expect(hasSafeHeredocSubstitutionRoute(true, true)).to_equal(true)
expect(hasSafeHeredocSubstitutionRoute(false, true)).to_equal(false)
expect(bashCommandIsSafeDeprecatedRoute("$(cat <<'EOF' ok EOF)")).to_equal("passthrough")
```

</details>

#### should model git jq and async routes

- should model git jq and async routes
- Check validator routes
   - Expected: bashCommandIsSafeDeprecatedRoute("git commit -m \"ok\"") equals `passthrough`
   - Expected: bashCommandIsSafeDeprecatedRoute("git commit -m \"$(printf pwn)\"") equals `ask git commit substitution`
   - Expected: bashCommandIsSafeDeprecatedRoute("jq -f /tmp/rules.jq") equals `ask jq file`
   - Expected: bashCommandIsSafeDeprecatedRoute("find . -name 'x'") equals `passthrough`
   - Expected: bashCommandIsSafeAsyncDeprecatedRoute("find . -name 'x'") equals `passthrough`
   - Expected: bashSecuritySourceLinesModeled() equals `2592`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model git jq and async routes")
step("Check validator routes")
expect(bashCommandIsSafeDeprecatedRoute("git commit -m \"ok\"")).to_equal("passthrough")
expect(bashCommandIsSafeDeprecatedRoute("git commit -m \"$(printf pwn)\"")).to_equal("ask git commit substitution")
expect(bashCommandIsSafeDeprecatedRoute("jq -f /tmp/rules.jq")).to_equal("ask jq file")
expect(bashCommandIsSafeDeprecatedRoute("find . -name 'x'")).to_equal("passthrough")
expect(bashCommandIsSafeAsyncDeprecatedRoute("find . -name 'x'")).to_equal("passthrough")
expect(bashSecuritySourceLinesModeled()).to_equal(2592)
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

- Canonical SPipe generation for source `082f29f78df410ffd3237467707b99416202b693bc333f059849e251275fd312`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `082f29f78df410ffd3237467707b99416202b693bc333f059849e251275fd312`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `082f29f78df410ffd3237467707b99416202b693bc333f059849e251275fd312`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/tools/BashTool/bashSecurity_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/tools/BashTool/bashSecurity_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/tools/BashTool/bashSecurity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/tools/BashTool/bashSecurity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/tools/BashTool/bashSecurity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/tools/BashTool/bashSecurity_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model empty and incomplete command routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/BashTool/bashSecurity_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model empty and incomplete command routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/BashTool/bashSecurity_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model heredoc substitution routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/BashTool/bashSecurity_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model heredoc substitution routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/BashTool/bashSecurity_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model git jq and async routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/BashTool/bashSecurity_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model git jq and async routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
