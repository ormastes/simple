# System Test Plan: LLM Runtime vLLM/Torch Interface

Date: 2026-06-25

## Candidate Specs

- `test/03_system/app/llm_runtime/feature/vllm_torch_readiness_spec.spl`
- generated manual:
  `doc/06_spec/03_system/app/llm_runtime/feature/vllm_torch_readiness_spec.md`

## Scenarios

1. Static manifest readiness:
   - Given a manifest with a base model and endpoint
   - When the probe runs in static mode
   - Then the JSONL event remains internal-marker-free and reports `blocked` while
     Torch/svLLM owner readiness is still placeholder-backed
2. Optional chat template absence:
   - Given no chat template
   - Then output uses option-like absence and does not expose the runtime's
     internal absence marker
3. Static LoRA adapter:
   - Given one adapter mapping
   - Then the event records adapter readiness/count without exposing adapter
     paths
4. Dynamic LoRA blocked by default:
   - Given runtime adapter loading is requested
   - Then the event status is `blocked` unless trusted mode is explicit
5. Dashboard readback:
   - Given probe JSONL
   - Then the dashboard diagnostics panel renders status/reason without the
     runtime's internal absence marker
6. Security readback:
   - Given probe metadata with sensitive-looking values
   - Then runtime manifest fields do not render credentials, API-key-like
     labels, or local model/adapter paths by default
7. Runtime blocker readback:
   - Given Torch/SFFI or svLLM loader readiness reports placeholder behavior
   - Then the bridge reports `blocked`
8. Static serve-plan metadata:
   - Given a manifest with a base model, endpoint, and optional static LoRA
     adapters
   - Then the serve-plan event records sanitized command metadata without
     starting vLLM, probing HTTP, or exposing adapter/model paths
9. Malformed serve-plan input:
   - Given malformed adapter entries or an invalid endpoint
   - Then the plan reports explicit `invalid_adapter_entry` or
     `invalid_endpoint` reasons without the runtime's internal absence marker

## Verification Notes

Use mocked files/endpoints for the first slice. Live vLLM/GPU evidence belongs
to a later NFR option unless the user selects it now.

If live vLLM serving is selected, add contract scenarios for `/v1/models`,
`/v1/chat/completions`, base-vs-adapter routing, auth rejection, and unsupported
parameter handling.
