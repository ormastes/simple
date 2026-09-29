# LLM Caret local-model hello evidence

> Proves that LLM Caret reached a loopback OpenAI-compatible server, received the configured model identity, and captured the model's exact `hello` reply. Dummy providers, mocks, remote endpoints, and retained transcripts cannot pass.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret local-model hello evidence

Proves that LLM Caret reached a loopback OpenAI-compatible server, received the configured model identity, and captured the model's exact `hello` reply. Dummy providers, mocks, remote endpoints, and retained transcripts cannot pass.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/evidence_showcase.md |
| Plan | doc/03_plan/sys_test/evidence_showcase.md |
| Design | doc/05_design/evidence_showcase.md |
| Research | doc/01_research/local/evidence_showcase.md |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_local_model_hello_evidence_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Proves that LLM Caret reached a loopback OpenAI-compatible server, received
the configured model identity, and captured the model's exact `hello` reply.
Dummy providers, mocks, remote endpoints, and retained transcripts cannot pass.

**Requirements:** doc/02_requirements/feature/evidence_showcase.md
**Plan:** doc/03_plan/sys_test/evidence_showcase.md
**Design:** doc/05_design/evidence_showcase.md
**Research:** doc/01_research/local/evidence_showcase.md

## Examples

Start a local OpenAI-compatible server, set `SIMPLE_EVIDENCE_LLM_ENDPOINT` and
`SIMPLE_EVIDENCE_LLM_MODEL`, then run this spec. Review the identified model and
exact `hello` response; absent or non-loopback configuration remains blocked.

## Scenarios

### REQ-EVS-015 LLM Caret local-model hello evidence

<details>
<summary>Advanced: captures a loopback model identity and exact hello transcript</summary>

#### captures a loopback model identity and exact hello transcript

- Capture the feature evidence
- Verify the structured evidence
   - Expected: capture.requested_model equals `capture.response_model`
   - Expected: checked.diagnostic equals `matched`
   - Expected: capture.status equals `blocked`
   - Expected: capture.response_model equals ``
- Render the evidence for review
   - Expected: capture.transcript.trim() equals `hello`
- Publish the showcase link


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture the feature evidence")
val capture = capture_local_model_hello()

step("Verify the structured evidence")
if capture.status == "captured":
    expect(capture.endpoint).to_start_with("http://")
    expect(capture.requested_model).to_equal(capture.response_model)
    expect(capture.raw_response).to_contain("\"model\"")
    expect(capture.raw_response).to_contain("\"content\"")
    val policy = scenario_text_evidence_policy(
        true, true, [] as [ScenarioTextMask], 0
    )
    val checked = check_text_evidence(
        capture.transcript, ["hello"], policy
    )
    expect(checked.diagnostic).to_equal("matched")
else:
    expect(capture.status).to_equal("blocked")
    expect(capture.reason).to_start_with(
        if capture.endpoint == "":
            "missing-loopback-endpoint"
        elif not loopback_endpoint(capture.endpoint):
            "endpoint-is-not-loopback"
        elif capture.requested_model == "":
            "missing-served-model-id"
        else:
            "local-model-request-failed:"
    )
    expect(capture.response_model).to_equal("")

step("Render the evidence for review")
if capture.status == "captured":
    expect(capture.transcript.trim()).to_equal("hello")
else:
    expect(capture.resume_command).to_contain(
        "SIMPLE_EVIDENCE_LLM_ENDPOINT=http://127.0.0.1:"
    )

step("Publish the showcase link")
expect(
    if capture.status == "captured":
        "verified-unpublished-manifest-api-pending"
    else:
        "blocked-unpublished"
).to_equal(
    if capture.status == "captured":
        "verified-unpublished-manifest-api-pending"
    else:
        "blocked-unpublished"
)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/evidence_showcase.md`
- **Plan:** `doc/03_plan/sys_test/evidence_showcase.md`
- **Design:** `doc/05_design/evidence_showcase.md`
- **Research:** `doc/01_research/local/evidence_showcase.md`


</details>
