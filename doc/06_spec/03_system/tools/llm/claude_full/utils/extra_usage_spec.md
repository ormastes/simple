# Claude Full extra usage utils

> Pure Simple coverage for extra-usage billing classification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full extra usage utils

Pure Simple coverage for extra-usage billing classification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/extra_usage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for extra-usage billing classification.

## Scenarios

### Claude full extra usage utils

#### bills fast mode as extra usage

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- bills fast mode as extra usage
- Check fast mode billing
   - Expected: isBilledAsExtraUsage("sonnet", true, false) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bills fast mode as extra usage")
step("Check fast mode billing")
expect(isBilledAsExtraUsage("sonnet", true, false)).to_equal(true)
```

</details>

#### bills Opus 1M as extra usage unless merge is enabled

- bills Opus 1M as extra usage unless merge is enabled
- Check Opus 1M billing
   - Expected: isBilledAsExtraUsage("opus[1m]", false, false) is true
   - Expected: isBilledAsExtraUsage("CLAUDE-OPUS-4-6[1M]", false, false) is true
   - Expected: isBilledAsExtraUsage("opus[1m]", false, true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bills Opus 1M as extra usage unless merge is enabled")
step("Check Opus 1M billing")
expect(isBilledAsExtraUsage("opus[1m]", false, false)).to_equal(true)
expect(isBilledAsExtraUsage("CLAUDE-OPUS-4-6[1M]", false, false)).to_equal(true)
expect(isBilledAsExtraUsage("opus[1m]", false, true)).to_equal(false)
```

</details>

#### does not bill ordinary models without fast mode

- does not bill ordinary models without fast mode
- Check ordinary model billing
   - Expected: isBilledAsExtraUsage("", false, false) is false
   - Expected: isBilledAsExtraUsage("opus", false, false) is false
   - Expected: isBilledAsExtraUsage("sonnet[1m]", false, false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not bill ordinary models without fast mode")
step("Check ordinary model billing")
expect(isBilledAsExtraUsage("", false, false)).to_equal(false)
expect(isBilledAsExtraUsage("opus", false, false)).to_equal(false)
expect(isBilledAsExtraUsage("sonnet[1m]", false, false)).to_equal(false)
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

- Canonical SPipe generation for source `8735b083e2fb03e35864973548481bbdd0b7dfe9336312468c656f66b9338207`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8735b083e2fb03e35864973548481bbdd0b7dfe9336312468c656f66b9338207`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8735b083e2fb03e35864973548481bbdd0b7dfe9336312468c656f66b9338207`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/extra_usage_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/extra_usage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/extra_usage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/extra_usage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/extra_usage_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bills fast mode as extra usage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/extra_usage_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bills Opus 1M as extra usage unless merge is enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/extra_usage_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not bill ordinary models without fast mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
