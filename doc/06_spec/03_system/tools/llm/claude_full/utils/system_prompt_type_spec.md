# Claude Full system prompt type

> Pure Simple coverage for the dependency-free system prompt brand wrapper.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full system prompt type

Pure Simple coverage for the dependency-free system prompt brand wrapper.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/system_prompt_type_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for the dependency-free system prompt brand wrapper.

## Scenarios

### Claude full system prompt type

#### brands prompt string arrays

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- brands prompt string arrays
- Check brand marker
   - Expected: prompt.brand equals `SystemPrompt`
   - Expected: systemPromptBrandName() equals `SystemPrompt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("brands prompt string arrays")
step("Check brand marker")
val prompt = asSystemPrompt(["alpha", "beta"])
expect(prompt.brand).to_equal("SystemPrompt")
expect(systemPromptBrandName()).to_equal("SystemPrompt")
```

</details>

#### preserves prompt values in order

- preserves prompt values in order
- Check array preservation
   - Expected: prompt.values equals `["one", "two", "three"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves prompt values in order")
step("Check array preservation")
val prompt = asSystemPrompt(["one", "two", "three"])
expect(prompt.values).to_equal(["one", "two", "three"])
```

</details>

#### accepts empty prompt arrays

- accepts empty prompt arrays
- Check empty prompt
   - Expected: prompt.values equals `[]`
   - Expected: prompt.brand equals `SystemPrompt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts empty prompt arrays")
step("Check empty prompt")
val prompt = asSystemPrompt([])
expect(prompt.values).to_equal([])
expect(prompt.brand).to_equal("SystemPrompt")
```

</details>

#### keeps the module dependency free

- keeps the module dependency free
- Check dependency policy marker
   - Expected: systemPromptModuleDependencyPolicy() equals `dependency-free`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the module dependency free")
step("Check dependency policy marker")
expect(systemPromptModuleDependencyPolicy()).to_equal("dependency-free")
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

- Canonical SPipe generation for source `3753d1442edd2aba4f9048a27950bdef4c54da5c68a8a2319e0d26a18a73f334`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3753d1442edd2aba4f9048a27950bdef4c54da5c68a8a2319e0d26a18a73f334`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3753d1442edd2aba4f9048a27950bdef4c54da5c68a8a2319e0d26a18a73f334`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/system_prompt_type_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/system_prompt_type_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/system_prompt_type_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/system_prompt_type_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/system_prompt_type_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'brands prompt string arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/system_prompt_type_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves prompt values in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/system_prompt_type_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts empty prompt arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
