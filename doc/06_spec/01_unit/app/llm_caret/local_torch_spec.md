# LLM Caret Local-Torch Exchange

> Hermetic script, completion, guard, and shell-free process evidence for the
> shipped local-torch provider boundary.

| Field | Value |
|---|---|
| Source | `test/01_unit/app/llm_caret/local_torch_spec.spl` |
| Executable scenarios | 9 |
| Execution in this tranche | 0 scenarios executed |
| Result | Not executed; no PASS is claimed |
| Requirement | N/A; focused shipped-provider unit evidence |

## Scope and Claim Boundary

The scenarios call `python_single_quoted`, `build_torch_script`, and
`complete_local_torch_exchange` directly. They cover default and override
tokens, quote/backslash/newline escaping, successful and failed completion,
and the empty-model guard. One static source scenario verifies exactly one
shell-free `process_run` call site and the absence of temporary file,
read/write, and cleanup effects.

No scenario launches Python or loads a model. The static scenario reads
repository source only. This manual therefore makes no subprocess execution,
model availability, GPU/CPU compatibility, generated text quality, or latency
claim.

## Frozen Flow

1. **Prepare local-torch inputs**
2. **Build or complete the production process exchange**
3. **Check exact script response and process ownership**

## Scenarios

1. should embed the prompt and emit output without temporary files
2. should escape quotes backslashes and newlines in one quoted path
3. should escape every interpolated model and prompt value
4. should use the default token limit for zero and negative inputs
5. should preserve an explicit positive token limit
6. should preserve exact successful output and model fields
7. should expose exact Python stderr and suppress failed output
8. should fail closed before path or process effects when the model is absent
9. should run one shell-free process with no file or cleanup effects

## Complete Executable SSpec

The folded scenario source is synchronized exactly with the executable spec.

<details>
<summary>Executable SSpec</summary>

```simple
describe "LLM Caret local-torch exchange":
    describe "avoiding temporary artifacts":
        it "should embed the prompt and emit output without temporary files":
            step("Prepare local-torch inputs")
            val prompt = "inline prompt"
            step("Build or complete the production process exchange")
            val script = build_torch_script("local/model", prompt, 8)
            step("Check exact script response and process ownership")
            expect(script).to_contain("prompt = 'inline prompt'")
            expect(script).to_contain("sys.stdout.write(result)")
            expect(script.contains("/tmp/")).to_be(false)
            expect(script.contains("open(")).to_be(false)

    describe "escaping Python path literals":
        it "should escape quotes backslashes and newlines in one quoted path":
            step("Prepare local-torch inputs")
            val path = "models\\team's\nlatest"
            step("Build or complete the production process exchange")
            val quoted = python_single_quoted(path)
            step("Check exact script response and process ownership")
            expect(quoted).to_equal("'models\\\\team\\'s\\nlatest'")

        it "should escape every interpolated model and prompt value":
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

    describe "building token limits":
        it "should use the default token limit for zero and negative inputs":
            step("Prepare local-torch inputs")
            val zeroTokens = 0
            val negativeTokens = -9
            step("Build or complete the production process exchange")
            val zeroScript = build_torch_script("model", "prompt", zeroTokens)
            val negativeScript = build_torch_script("model", "prompt", negativeTokens)
            step("Check exact script response and process ownership")
            expect(zeroScript).to_contain("max_new_tokens=256")
            expect(negativeScript).to_contain("max_new_tokens=256")

        it "should preserve an explicit positive token limit":
            step("Prepare local-torch inputs")
            val maxTokens = 8192
            step("Build or complete the production process exchange")
            val script = build_torch_script("model", "prompt", maxTokens)
            step("Check exact script response and process ownership")
            expect(script).to_contain("max_new_tokens=8192")

    describe "completing injected process results":
        it "should preserve exact successful output and model fields":
            step("Prepare local-torch inputs")
            val output = "local answer"
            step("Build or complete the production process exchange")
            val response = complete_local_torch_exchange("local/model", output, "", 0)
            step("Check exact script response and process ownership")
            expect(response.content).to_equal("local answer")
            expect(response.model).to_equal("local/model")
            expect(response.error).to_equal("")
            expect(response.is_error).to_equal(false)

        it "should expose exact Python stderr and suppress failed output":
            step("Prepare local-torch inputs")
            val stderr = "CUDA device unavailable"
            step("Build or complete the production process exchange")
            val response = complete_local_torch_exchange("local/model", "ignored output", stderr, 7)
            step("Check exact script response and process ownership")
            expect(response.content).to_equal("")
            expect(response.model).to_equal("local/model")
            expect(response.error).to_equal("Python error: CUDA device unavailable")
            expect(response.is_error).to_equal(true)

    describe "guarding and ordering production send":
        it "should fail closed before path or process effects when the model is absent":
            step("Prepare local-torch inputs")
            val modelPath = ""
            step("Build or complete the production process exchange")
            val response = local_torch_send("", modelPath, "must not be written", 1)
            step("Check exact script response and process ownership")
            expect(response.content).to_equal("")
            expect(response.model).to_equal("")
            expect(response.error).to_equal("model_path not configured")
            expect(response.is_error).to_equal(true)

        it "should run one shell-free process with no file or cleanup effects":
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
