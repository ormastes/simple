# caret_slang_local_hello_system_spec

> As an operator with no cloud agent I point caret at a small local GGUF model

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# caret_slang_local_hello_system_spec

As an operator with no cloud agent I point caret at a small local GGUF model

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/llm_caret/caret_slang_local_hello_system_spec.spl` |
| Updated | 2026-10-03 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
As an operator with no cloud agent I point caret at a small local GGUF model
through slang's in-process ggml backend and talk to it the way I talk to
Claude: one prompt in, a reply out. This spec launches the REAL model. It is
for the maintainers of slang (`src/lib/gc_async_mut/slang/`) and of caret's
`slang_local` provider.
## Operator workflow
SIMPLE_BINARY=<simple> SLANG_MODEL_ROOT=<model root> \
bin/simple test test/03_system/app/llm_caret/caret_slang_local_hello_system_spec.spl
`CARET_SLANG_MODEL` picks the model directory (default
`Qwen2.5-1.5B-Instruct-GGUF`). The ggml shim must be built first:
`sh scripts/check/build-slang-ggml-shim.shs` (Windows: `slang_ggml.dll`).
## Compatibility and limitations
A missing binary, model root, model or shim is a FAILED scenario that names
what is missing, never a skip. The 0.5B Qwen2.5 model loads and generates but
does not follow caret's raw transcript format; see
doc/08_tracking/bug/caret_slang_local_ignores_gguf_chat_template_2026-10-03.md.
## Verification guidance and troubleshooting
"refusing to load" means the memory gate found too little free RAM for the
model plus caret's context window; close other processes and rerun.
"backend unavailable" means the shim was not built in this tree.

## Scenarios

### caret talks to a small local model through slang

#### the inference gate reaches a generation verdict for the local model root

- Confirm the binary and the model root are in place
   - Expected: _missing() equals ``
- Run the slang inference gate over the model root
- The gate passes and at least one model generated tokens
   - Text capture: after_step
   - Evidence: text output verified by 3 expected checks
   - Expected: code equals `0`
   - Expected: out does not contain ` 0 generated`
   - Expected: err does not contain `silent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CARET-SLANG-001
step("Confirm the binary and the model root are in place")
expect(_missing()).to_equal("")
step("Run the slang inference gate over the model root")
val (out, err, code) = process_run_bounded("sh",
    ["scripts/check/check-slang-ggml-inference.shs", "--models", _env("SLANG_MODEL_ROOT")],
    RUN_TIMEOUT_MS, MAX_OUTPUT_BYTES)
step("The gate passes and at least one model generated tokens")
expect(code).to_equal(0)
expect(out).to_contain("PASS")
expect(out.contains(" 0 generated")).to_equal(false)
expect(err.contains("silent")).to_equal(false)
```

</details>

#### caret answers 'hello' from the local model like it does from Claude

- Confirm the binary and the model are in place
   - Expected: _missing() equals ``
- Send one prompt through caret's slang_local provider
- caret exits cleanly and the model's reply says hello
   - Protocol capture: after_step
   - Evidence: protocol response verified by 3 expected checks
   - Expected: err does not contain `refusing to load`
   - Expected: err does not contain `backend unavailable`
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CARET-SLANG-002
step("Confirm the binary and the model are in place")
expect(_missing()).to_equal("")
step("Send one prompt through caret's slang_local provider")
val (out, err, code) = process_run_bounded(_env("SIMPLE_BINARY"),
    ["run", "src/app/llm_caret/main.spl", "--provider", "slang_local",
        "--model", _model(), "--prompt", "Say exactly: hello"],
    RUN_TIMEOUT_MS, MAX_OUTPUT_BYTES)
step("caret exits cleanly and the model's reply says hello")
expect(err.contains("refusing to load")).to_equal(false)
expect(err.contains("backend unavailable")).to_equal(false)
expect(code).to_equal(0)
expect(out.lower()).to_contain("hello")
```

</details>

#### rejects a model that is not under the model root instead of inventing a reply

- Ask caret for a model directory that does not exist
   - Expected: _env("SIMPLE_BINARY") != "" is true
- caret names the missing model and prints no reply
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: out.lower() does not contain `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-CARET-SLANG-003
step("Ask caret for a model directory that does not exist")
expect(_env("SIMPLE_BINARY") != "").to_equal(true)
val (out, err, code) = process_run_bounded(_env("SIMPLE_BINARY"),
    ["run", "src/app/llm_caret/main.spl", "--provider", "slang_local",
        "--model", "no-such-model-9f2", "--prompt", "Say exactly: hello"],
    RUN_TIMEOUT_MS, MAX_OUTPUT_BYTES)
step("caret names the missing model and prints no reply")
expect((out + err)).to_contain("no-such-model-9f2")
expect(out.lower().contains("hello")).to_equal(false)
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
