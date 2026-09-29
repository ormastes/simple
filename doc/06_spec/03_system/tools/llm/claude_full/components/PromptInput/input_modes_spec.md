# Claude Full PromptInput input modes

> Pure Simple coverage for PromptInput bash mode prefix helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full PromptInput input modes

Pure Simple coverage for PromptInput bash mode prefix helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/PromptInput/input_modes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for PromptInput bash mode prefix helpers.

## Scenarios

### Claude full PromptInput input modes

#### prepends the bash mode character only for bash mode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- prepends the bash mode character only for bash mode
- Check mode serialization
   - Expected: prependModeCharacterToInput("ls", "bash") equals `!ls`
   - Expected: prependModeCharacterToInput("hello", "prompt") equals `hello`
   - Expected: prependModeCharacterToInput("hello", "other") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prepends the bash mode character only for bash mode")
step("Check mode serialization")
expect(prependModeCharacterToInput("ls", "bash")).to_equal("!ls")
expect(prependModeCharacterToInput("hello", "prompt")).to_equal("hello")
expect(prependModeCharacterToInput("hello", "other")).to_equal("hello")
```

</details>

#### detects bash history mode from leading bang

- detects bash history mode from leading bang
- Check mode detection
   - Expected: getModeFromInput("!ls") equals `bash`
   - Expected: getModeFromInput("hello") equals `prompt`
   - Expected: getModeFromInput("") equals `prompt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects bash history mode from leading bang")
step("Check mode detection")
expect(getModeFromInput("!ls")).to_equal("bash")
expect(getModeFromInput("hello")).to_equal("prompt")
expect(getModeFromInput("")).to_equal("prompt")
```

</details>

#### strips the bash prefix when reading input value

- strips the bash prefix when reading input value
- Check value extraction
   - Expected: getValueFromInput("!ls -la") equals `ls -la`
   - Expected: getValueFromInput("hello") equals `hello`
   - Expected: getValueFromInput("!") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("strips the bash prefix when reading input value")
step("Check value extraction")
expect(getValueFromInput("!ls -la")).to_equal("ls -la")
expect(getValueFromInput("hello")).to_equal("hello")
expect(getValueFromInput("!")).to_equal("")
```

</details>

#### recognizes only the mode character itself

- recognizes only the mode character itself
- Check mode character
   - Expected: isInputModeCharacter("!") is true
   - Expected: isInputModeCharacter("!!") is false
   - Expected: isInputModeCharacter("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recognizes only the mode character itself")
step("Check mode character")
expect(isInputModeCharacter("!")).to_equal(true)
expect(isInputModeCharacter("!!")).to_equal(false)
expect(isInputModeCharacter("")).to_equal(false)
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

- Canonical SPipe generation for source `21e7f16608cdfd92221baf7632f619e5553b0dc5603cff4145f163cae7fd18d3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `21e7f16608cdfd92221baf7632f619e5553b0dc5603cff4145f163cae7fd18d3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `21e7f16608cdfd92221baf7632f619e5553b0dc5603cff4145f163cae7fd18d3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/components/PromptInput/input_modes_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/PromptInput/input_modes_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/PromptInput/input_modes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/PromptInput/input_modes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/PromptInput/input_modes_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prepends the bash mode character only for bash mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/PromptInput/input_modes_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects bash history mode from leading bang' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/PromptInput/input_modes_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'strips the bash prefix when reading input value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
