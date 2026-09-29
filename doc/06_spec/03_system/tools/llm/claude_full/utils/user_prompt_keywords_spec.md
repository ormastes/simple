# Claude Full user prompt keywords

> Pure Simple coverage for negative and continuation prompt keyword matching.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full user prompt keywords

Pure Simple coverage for negative and continuation prompt keyword matching.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/user_prompt_keywords_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for negative and continuation prompt keyword matching.

## Scenarios

### Claude full user prompt keywords

#### matches negative keyword words and phrases case-insensitively

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches negative keyword words and phrases case-insensitively
- Check negative phrases
   - Expected: matchesNegativeKeyword("This is HORRIBLE") is true
   - Expected: matchesNegativeKeyword("what the hell happened") is true
   - Expected: matchesNegativeKeyword("this sucks") is true
   - Expected: matchesNegativeKeyword("piss off") is true
   - Expected: matchesNegativeKeyword("that is fuckin useless") is true
   - Expected: matchesNegativeKeyword("that is fucking terrible") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches negative keyword words and phrases case-insensitively")
step("Check negative phrases")
expect(matchesNegativeKeyword("This is HORRIBLE")).to_equal(true)
expect(matchesNegativeKeyword("what the hell happened")).to_equal(true)
expect(matchesNegativeKeyword("this sucks")).to_equal(true)
expect(matchesNegativeKeyword("piss off")).to_equal(true)
expect(matchesNegativeKeyword("that is fuckin useless")).to_equal(true)
expect(matchesNegativeKeyword("that is fucking terrible")).to_equal(true)
```

</details>

#### does not match negative keywords inside larger words

- does not match negative keywords inside larger words
- Check word boundaries
   - Expected: matchesNegativeKeyword("awfully close") is false
   - Expected: matchesNegativeKeyword("classic shell command") is false
   - Expected: matchesNegativeKeyword("fuck broken") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not match negative keywords inside larger words")
step("Check word boundaries")
expect(matchesNegativeKeyword("awfully close")).to_equal(false)
expect(matchesNegativeKeyword("classic shell command")).to_equal(false)
expect(matchesNegativeKeyword("fuck broken")).to_equal(false)
```

</details>

#### matches exact continue after trimming

- matches exact continue after trimming
- Check continue
   - Expected: matchesKeepGoingKeyword(" continue ") is true
   - Expected: matchesKeepGoingKeyword("continue please") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches exact continue after trimming")
step("Check continue")
expect(matchesKeepGoingKeyword(" continue ")).to_equal(true)
expect(matchesKeepGoingKeyword("continue please")).to_equal(false)
```

</details>

#### matches keep-going phrases anywhere with boundaries

- matches keep-going phrases anywhere with boundaries
- Check keep going phrases
   - Expected: matchesKeepGoingKeyword("please keep going now") is true
   - Expected: matchesKeepGoingKeyword("can you go on?") is true
   - Expected: matchesKeepGoingKeyword("undergo ongoing work") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches keep-going phrases anywhere with boundaries")
step("Check keep going phrases")
expect(matchesKeepGoingKeyword("please keep going now")).to_equal(true)
expect(matchesKeepGoingKeyword("can you go on?")).to_equal(true)
expect(matchesKeepGoingKeyword("undergo ongoing work")).to_equal(false)
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

- Canonical SPipe generation for source `036b494660f5fc4215aa2e26077da5da5e234d4efb5845fb1f54d2850e633126`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `036b494660f5fc4215aa2e26077da5da5e234d4efb5845fb1f54d2850e633126`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `036b494660f5fc4215aa2e26077da5da5e234d4efb5845fb1f54d2850e633126`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/user_prompt_keywords_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/user_prompt_keywords_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/user_prompt_keywords_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/user_prompt_keywords_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/user_prompt_keywords_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches negative keyword words and phrases case-insensitively' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/user_prompt_keywords_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not match negative keywords inside larger words' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/user_prompt_keywords_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches exact continue after trimming' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
