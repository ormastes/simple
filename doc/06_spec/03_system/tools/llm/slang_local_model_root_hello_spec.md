# slang_local_model_root_hello_spec

> Purpose: pin the contract an operator relies on when caret is pointed at a real

<!-- sdn-diagram:id=slang_local_model_root_hello_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=slang_local_model_root_hello_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

slang_local_model_root_hello_spec -> std
slang_local_model_root_hello_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=slang_local_model_root_hello_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# slang_local_model_root_hello_spec

Purpose: pin the contract an operator relies on when caret is pointed at a real

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/slang_local_model_root_hello_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: pin the contract an operator relies on when caret is pointed at a real
local model root -- every model directory reaches a verdict, exactly the
runnable ones claim to be runnable, every refusal carries its reason, and the
runnable one answers a greeting with tokens a model produced.
Audience: an operator running `caret --provider slang_local` against a
downloaded model root such as /home/yoon/dev/model.

## Operator workflow
I point slang at my model root. It must tell me about EVERY model it finds --
not only the ones it can run -- because the failure this guards against is not
a crash, it is silence: a root holding three multi-gigabyte checkouts reporting
nothing and looking healthy. Then I say hello to the runnable one through
caret, and I must get real generated text back, tagged with the engine that
produced it.

## Compatibility and limitations
Recognition runs whenever SLANG_MODEL_ROOT names a directory. Generation is
additionally gated on SLANG_LIVE=1 because it loads tens of gigabytes of
weights; the shell gate
`sh scripts/check/check-slang-ggml-inference.shs --models DIR` drives the same
caret command over every model in the root.

## Scenarios

### slang over a real local model root

#### reports every model in the root, refusals included

- Point slang at the operator's model root
- Every directory comes back described, none silently dropped
- No refusal is issued without a reason
   - Expected: _refusals_without_reason(root) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _model_root()
if root == "":
    skip("reports every model in the root, refusals included", "SLANG_MODEL_ROOT is not a directory")
else:
    step("Point slang at the operator's model root")
    val found = slang_models(root)

    step("Every directory comes back described, none silently dropped")
    expect(found.len()).to_be_greater_than(0)

    step("No refusal is issued without a reason")
    expect(_refusals_without_reason(root)).to_equal(0)
```

</details>

#### answers a greeting with generated tokens through caret

- Send hello to the runnable model through caret's own dispatch
- Caret reports success, not a swallowed error
   - Expected: answer.is_error is false
- The reply carries text the engine generated
- Provenance names the engine that produced it, so a stub cannot pass as a reply
   - Expected: answer.provider equals `slang_local/ggml`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _model_root()
val live = env_get("SLANG_LIVE") ?? ""
val runnable = _runnable_ids(root)
if root == "" or live != "1" or not engine_backend_available() or runnable.len() == 0:
    skip("answers a greeting with generated tokens through caret", "needs SLANG_LIVE=1, a built ggml backend, and a runnable model")
else:
    step("Send hello to the runnable model through caret's own dispatch")
    val answer = dispatch_send(
        "slang_local", "Say hello in one short sentence.", runnable[0],
        "", root, "", "", "", 1, 40, ""
    )

    step("Caret reports success, not a swallowed error")
    expect(answer.is_error).to_equal(false)

    step("The reply carries text the engine generated")
    expect(answer.content.trim().len()).to_be_greater_than(0)

    step("Provenance names the engine that produced it, so a stub cannot pass as a reply")
    expect(answer.provider).to_equal("slang_local/ggml")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

## Generation history

Generated by `simple spipe-docgen` (Simple).
Source SHA-256: `3c009c2cf528598a3b43c53bdd3fa68d38e0214085860b3372077ce9963c4ddb`
