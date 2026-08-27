# LLM Caret Local-Torch Exchange

> Checks shell-free Python literal escaping, inline script construction,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Local-Torch Exchange

Checks shell-free Python literal escaping, inline script construction,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/local_torch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks shell-free Python literal escaping, inline script construction,
completion, fail-closed configuration, and production process ordering for the
shipped local-torch provider.

Requirements: N/A. These scenarios do not launch Python, load a model, or
write/delete temporary files. The production-send scenario reads source text
only and therefore makes no subprocess, model-availability, or latency claim.

## Scenarios

### LLM Caret local-torch exchange

### avoiding temporary artifacts

#### should embed the prompt and emit output without temporary files

- should embed the prompt and emit output without temporary files
- Prepare local-torch inputs
- Build or complete the production process exchange
- Check exact script response and process ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should embed the prompt and emit output without temporary files")
step("Prepare local-torch inputs")
val prompt = "inline prompt"
step("Build or complete the production process exchange")
val script = build_torch_script("local/model", prompt, 8)
step("Check exact script response and process ownership")
expect(script).to_contain("prompt = 'inline prompt'")
expect(script).to_contain("sys.stdout.write(result)")
expect(script.contains("/tmp/")).to_be(false)
expect(script.contains("open(")).to_be(false)
```

</details>

### escaping Python path literals

#### should escape quotes backslashes and newlines in one quoted path

- should escape quotes backslashes and newlines in one quoted path
- Prepare local-torch inputs
- Build or complete the production process exchange
- Check exact script response and process ownership
   - Expected: quoted equals `'models\\\\team\\'s\\nlatest'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should escape quotes backslashes and newlines in one quoted path")
step("Prepare local-torch inputs")
val path = "models\\team's\nlatest"
step("Build or complete the production process exchange")
val quoted = python_single_quoted(path)
step("Check exact script response and process ownership")
expect(quoted).to_equal("'models\\\\team\\'s\\nlatest'")
```

</details>

#### should escape every interpolated model and prompt value

- should escape every interpolated model and prompt value
- Prepare local-torch inputs
- Build or complete the production process exchange
- Check exact script response and process ownership
   - Expected: script.split(quotedModel).len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should escape every interpolated model and prompt value")
step("Prepare local-torch inputs")
val modelPath = "models\\team's\nlatest"
val prompt = "prompt's\\line\nnext"
step("Build or complete the production process exchange")
val script = build_torch_script(modelPath, prompt, 0)
val quotedModel = python_single_quoted(modelPath)
val quotedPrompt = python_single_quoted(prompt)
step("Check exact script response and process ownership")
expect(script).to_contain("prompt = " + quotedPrompt)
expect(script.split(quotedModel).len()).to_equal(3)
```

</details>

### building token limits

#### should use the default token limit for zero and negative inputs

- should use the default token limit for zero and negative inputs
- Prepare local-torch inputs
- Build or complete the production process exchange
- Check exact script response and process ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should use the default token limit for zero and negative inputs")
step("Prepare local-torch inputs")
val zeroTokens = 0
val negativeTokens = -9
step("Build or complete the production process exchange")
val zeroScript = build_torch_script("model", "prompt", zeroTokens)
val negativeScript = build_torch_script("model", "prompt", negativeTokens)
step("Check exact script response and process ownership")
expect(zeroScript).to_contain("max_new_tokens=256")
expect(negativeScript).to_contain("max_new_tokens=256")
```

</details>

#### should preserve an explicit positive token limit

- should preserve an explicit positive token limit
- Prepare local-torch inputs
- Build or complete the production process exchange
- Check exact script response and process ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should preserve an explicit positive token limit")
step("Prepare local-torch inputs")
val maxTokens = 8192
step("Build or complete the production process exchange")
val script = build_torch_script("model", "prompt", maxTokens)
step("Check exact script response and process ownership")
expect(script).to_contain("max_new_tokens=8192")
```

</details>

### completing injected process results

#### should preserve exact successful output and model fields

- should preserve exact successful output and model fields
- Prepare local-torch inputs
- Build or complete the production process exchange
- Check exact script response and process ownership
   - Expected: response.content equals `local answer`
   - Expected: response.model equals `local/model`
   - Expected: response.error equals ``
   - Expected: response.is_error is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should preserve exact successful output and model fields")
step("Prepare local-torch inputs")
val output = "local answer"
step("Build or complete the production process exchange")
val response = complete_local_torch_exchange("local/model", output, "", 0)
step("Check exact script response and process ownership")
expect(response.content).to_equal("local answer")
expect(response.model).to_equal("local/model")
expect(response.error).to_equal("")
expect(response.is_error).to_equal(false)
```

</details>

#### should expose exact Python stderr and suppress failed output

- should expose exact Python stderr and suppress failed output
- Prepare local-torch inputs
- Build or complete the production process exchange
- Check exact script response and process ownership
   - Expected: response.content equals ``
   - Expected: response.model equals `local/model`
   - Expected: response.error equals `Python error: CUDA device unavailable`
   - Expected: response.is_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should expose exact Python stderr and suppress failed output")
step("Prepare local-torch inputs")
val stderr = "CUDA device unavailable"
step("Build or complete the production process exchange")
val response = complete_local_torch_exchange("local/model", "ignored output", stderr, 7)
step("Check exact script response and process ownership")
expect(response.content).to_equal("")
expect(response.model).to_equal("local/model")
expect(response.error).to_equal("Python error: CUDA device unavailable")
expect(response.is_error).to_equal(true)
```

</details>

### guarding and ordering production send

#### should fail closed before path or process effects when the model is absent

- should fail closed before path or process effects when the model is absent
- Prepare local-torch inputs
- Build or complete the production process exchange
- Check exact script response and process ownership
   - Expected: response.content equals ``
   - Expected: response.model equals ``
   - Expected: response.error equals `model_path not configured`
   - Expected: response.is_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should fail closed before path or process effects when the model is absent")
step("Prepare local-torch inputs")
val modelPath = ""
step("Build or complete the production process exchange")
val response = local_torch_send("", modelPath, "must not be written", 1)
step("Check exact script response and process ownership")
expect(response.content).to_equal("")
expect(response.model).to_equal("")
expect(response.error).to_equal("model_path not configured")
expect(response.is_error).to_equal(true)
```

</details>

#### should run one shell-free process with no file or cleanup effects

- should run one shell-free process with no file or cleanup effects
- Prepare local-torch inputs
- Build or complete the production process exchange
- Check exact script response and process ownership
   - Expected: sendParts.len() equals `2`
   - Expected: buildParts.len() equals `2`
   - Expected: sendSource.split("process_run(").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should run one shell-free process with no file or cleanup effects")
step("Prepare local-torch inputs")
val source = file_read_text("src/app/llm_caret/local_torch.spl")
val sendParts = source.split("fn local_torch_send(")
var sendSource = ""
if sendParts.len() == 2:
    sendSource = sendParts[1]
step("Build or complete the production process exchange")
val buildParts = source.split("fn build_torch_script(")
step("Check exact script response and process ownership")
expect(sendParts.len()).to_equal(2)
expect(buildParts.len()).to_equal(2)
expect(sendSource.split("process_run(").len()).to_equal(2)
expect(sendSource).to_contain("process_run(py, [\"-c\", script])")
expect(source.contains("extern fn rt_file_")).to_be(false)
expect(source.contains("extern fn rt_time_")).to_be(false)
expect(source.contains("file_atomic_write")).to_be(false)
expect(source.contains("file_read_text")).to_be(false)
expect(source.contains("file_delete")).to_be(false)
expect(source.contains("/tmp/")).to_be(false)
if buildParts.len() == 2:
    expect(buildParts[1]).to_contain("sys.stdout.write(result)")
expect(sendSource.index_of("if model_path == \"\"")).to_be_less_than(sendSource.index_of("build_torch_script("))
expect(sendSource.index_of("build_torch_script(")).to_be_less_than(sendSource.index_of("process_run("))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dd40f7b2ce11ad37e303f496022d72136612f6edeb0befd876bbe33baade54b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dd40f7b2ce11ad37e303f496022d72136612f6edeb0befd876bbe33baade54b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dd40f7b2ce11ad37e303f496022d72136612f6edeb0befd876bbe33baade54b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **66/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/local_torch_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/local_torch_spec.md (current)
findings: 14 blockers: 2
  narrative=100 structure=70 oracle=20
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=66; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/local_torch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/local_torch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/local_torch_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/llm_caret/local_torch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/local_torch_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/local_torch_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should embed the prompt and emit output without temporary files' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/local_torch_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should embed the prompt and emit output without temporary files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/local_torch_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should escape quotes backslashes and newlines in one quoted path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/local_torch_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should escape quotes backslashes and newlines in one quoted path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/local_torch_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should escape every interpolated model and prompt value' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/local_torch_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should escape every interpolated model and prompt value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/local_torch_spec.spl:71:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use the default token limit for zero and negative inputs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/local_torch_spec.spl:84:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve an explicit positive token limit' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/local_torch_spec.spl:95:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve exact successful output and model fields' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
