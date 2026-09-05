# Claude Full Bash Commands Slice

> Focused pure-Simple coverage for deterministic bash command helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bash Commands Slice

Focused pure-Simple coverage for deterministic bash command helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/bash/commands_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused pure-Simple coverage for deterministic bash command helpers.

## Scenarios

### Claude full bash commands parity

#### should recognize simple help commands

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should recognize simple help commands
- Check exact help forms
   - Expected: isHelpCommandRoute("foo --help") is true
   - Expected: isHelpCommandRoute("  foo --help  ") is true
   - Expected: isHelpCommandRoute("foo    --help") is true
   - Expected: isHelpCommandRoute("foo\t--help") is true
   - Expected: isHelpCommandRoute("foo -h") is true
   - Expected: isHelpCommandRoute("\"foo\" --help") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should recognize simple help commands")
step("Check exact help forms")
expect(isHelpCommandRoute("foo --help")).to_equal(true)
expect(isHelpCommandRoute("  foo --help  ")).to_equal(true)
expect(isHelpCommandRoute("foo    --help")).to_equal(true)
expect(isHelpCommandRoute("foo\t--help")).to_equal(true)
expect(isHelpCommandRoute("foo -h")).to_equal(true)
expect(isHelpCommandRoute("\"foo\" --help")).to_equal(true)
```

</details>

#### should reject commands that are not single help requests

- should reject commands that are not single help requests
- Check unsafe and ambiguous forms
   - Expected: isHelpCommandRoute("foo --help --verbose") is false
   - Expected: isHelpCommandRoute("foo;bar --help") is false
   - Expected: isHelpCommandRoute("foo && bar --help") is false
   - Expected: isHelpCommandRoute("foo --version") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject commands that are not single help requests")
step("Check unsafe and ambiguous forms")
expect(isHelpCommandRoute("foo --help --verbose")).to_equal(false)
expect(isHelpCommandRoute("foo;bar --help")).to_equal(false)
expect(isHelpCommandRoute("foo && bar --help")).to_equal(false)
expect(isHelpCommandRoute("foo --version")).to_equal(false)
```

</details>

#### should filter shell control operators for summaries

- should filter shell control operators for summaries
- Check control operator filtering
   - Expected: filterControlOperatorsRoute("foo; bar && baz || qux | cat") equals `foo  bar   baz   qux   cat`
   - Expected: filterControlOperatorsRoute("echo \"a|b\" && cat") equals `echo "a|b"   cat`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should filter shell control operators for summaries")
step("Check control operator filtering")
expect(filterControlOperatorsRoute("foo; bar && baz || qux | cat")).to_equal("foo  bar   baz   qux   cat")
expect(filterControlOperatorsRoute("echo \"a|b\" && cat")).to_equal("echo \"a|b\"   cat")
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

- Canonical SPipe generation for source `cddb4fcc13c21534132c1df831ffcf9beaf4ad8aba2c94eef3c849a0496c55d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cddb4fcc13c21534132c1df831ffcf9beaf4ad8aba2c94eef3c849a0496c55d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cddb4fcc13c21534132c1df831ffcf9beaf4ad8aba2c94eef3c849a0496c55d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/utils/bash/commands_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/bash/commands_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/bash/commands_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/bash/commands_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/bash/commands_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should recognize simple help commands' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/bash/commands_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should recognize simple help commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/bash/commands_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject commands that are not single help requests' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/bash/commands_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject commands that are not single help requests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/bash/commands_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should filter shell control operators for summaries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/bash/commands_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should filter shell control operators for summaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
