# Parser Framework Specification

## Scenarios

### parser framework baseline

#### keeps scalar oracle determinism across repeated CPU-reference parses

1. Parse `"ab 12 cd"` twice with `PARSE_MODE_CPU_REFERENCE`.
2. Compare `result.receipt.deterministic_hash`.
   - Expected: both hashes are equal.
3. Compare `result.receipt.item_count_out`.
   - Expected: both counts are equal.

#### demotes unimplemented accelerated mode and keeps deterministic equality to CPU oracle

1. Parse `"ab 12 cd"` with `PARSE_MODE_CPU_REFERENCE` (oracle baseline).
2. Parse `"ab 12 cd"` with `PARSE_MODE_HYBRID_VECTOR_GPU`.
3. Expect demotion evidence and hash parity:
   - `receipt.candidate_backend == "hybrid_vector_gpu"`
   - `receipt.backend == "cpu_reference"`
   - `receipt.fallback_count == 1`
   - `receipt.deterministic_hash == baseline.receipt.deterministic_hash`

#### fails closed for malformed lex programs

1. Construct a malformed lex table (invalid transition dimensions).
2. Parse `"ab"` with the malformed dialect.
3. Expect rejection:
   - `receipt.fallback_reason == "parse_lex_program_malformed"`
   - `ok == false`

#### routes through parse_runtime as a Result-typed execution entrypoint

1. Create a runtime from the framework dialect.
2. Run CPU-reference parse via `runtime_parse_request(runtime, request)` and compare with `parse_run(dialect, request)`:
   - `parse_results_equal(wrapped, base) == true`
   - `parse_result_fingerprint(wrapped) == parse_result_fingerprint(base)`

#### surfaces missing and unknown parse mode as explicit runtime errors

1. Create a runtime from the framework dialect.
2. Call `runtime_parse_request(runtime, framework_request("ab", ""))`.
   - Expect an error string equal to `"parse_request_missing_mode"`.
3. Call `runtime_parse_request(runtime, framework_request("ab", "wave-6-mirage"))`.
   - Expect an error string equal to `"parse_request_unknown_mode: wave-6-mirage:reject_unknown_mode"`.

#### honors output masking without changing parse metadata

1. Build a request with `PARSE_OUTPUT_DIAGNOSTICS` only.
2. Parse `"ab 12 cd"` with CPU-reference.
3. Expect:
   - `ok == true`
   - `parse_token_arena_len(result.tokens) == 0`
   - `parse_diagnostic_arena_len(result.diagnostics) == 0`
   - `item_count_in == 5`
   - `item_count_out == 0`

#### keeps tag allocations off unless demand is enabled

1. Start with an empty tag-demand action sink.
2. Emit a tag with `PARSE_TAG_DEMAND_OFF` and again with `PARSE_TAG_DEMAND_ALL`.
3. Expect:
   - OFF path emits `0`
   - ALL path emits `1`

## Source

- Source: `test/03_system/app/compiler/feature/parser_framework_spec.spl`
- Updated: 2026-08-01
- Status: Active
