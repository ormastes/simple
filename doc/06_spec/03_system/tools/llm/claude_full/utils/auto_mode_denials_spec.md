# Claude Full auto mode denials

> Pure Simple coverage for classifier-gated auto mode denial history.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full auto mode denials

Pure Simple coverage for classifier-gated auto mode denial history.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/auto_mode_denials_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for classifier-gated auto mode denial history.

## Scenarios

### Claude full auto mode denials

#### ignores denied commands when the classifier feature is disabled

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ignores denied commands when the classifier feature is disabled
- Check feature gate
   - Expected: getAutoModeDenials().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ignores denied commands when the classifier feature is disabled")
step("Check feature gate")
clearAutoModeDenials()
recordAutoModeDenial(AutoModeDenial.new("Bash", "rm -rf /tmp/a", "blocked", 10), false)
expect(getAutoModeDenials().len()).to_equal(0)
```

</details>

#### prepends enabled denials

- prepends enabled denials
- Check newest first
   - Expected: denials.len() equals `2`
   - Expected: denials[0].toolName equals `Bash`
   - Expected: denials[1].toolName equals `Read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prepends enabled denials")
step("Check newest first")
clearAutoModeDenials()
recordAutoModeDenial(AutoModeDenial.new("Read", "a.txt", "no", 1), true)
recordAutoModeDenial(AutoModeDenial.new("Bash", "ls", "deny", 2), true)
val denials = getAutoModeDenials()
expect(denials.len()).to_equal(2)
expect(denials[0].toolName).to_equal("Bash")
expect(denials[1].toolName).to_equal("Read")
```

</details>

#### caps denial history at twenty entries

- caps denial history at twenty entries
- Check maximum history
   - Expected: denials.len() equals `autoModeDenialsMax()`
   - Expected: denials[0].timestamp equals `24`
   - Expected: denials[19].timestamp equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("caps denial history at twenty entries")
step("Check maximum history")
clearAutoModeDenials()
var i = 0
while i < 25:
    recordAutoModeDenial(AutoModeDenial.new("Tool", "item", "reason", i), true)
    i = i + 1
val denials = getAutoModeDenials()
expect(denials.len()).to_equal(autoModeDenialsMax())
expect(denials[0].timestamp).to_equal(24)
expect(denials[19].timestamp).to_equal(5)
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

- Canonical SPipe generation for source `18dc811509258d3444c05ce6f4a9705a302d05d6e796a81db361c09336e27009`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `18dc811509258d3444c05ce6f4a9705a302d05d6e796a81db361c09336e27009`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `18dc811509258d3444c05ce6f4a9705a302d05d6e796a81db361c09336e27009`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/auto_mode_denials_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/auto_mode_denials_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/auto_mode_denials_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/auto_mode_denials_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/auto_mode_denials_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/auto_mode_denials_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores denied commands when the classifier feature is disabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/auto_mode_denials_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prepends enabled denials' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/auto_mode_denials_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'caps denial history at twenty entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
