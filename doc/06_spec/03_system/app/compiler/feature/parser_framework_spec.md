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

## Source

- Source: `test/03_system/app/compiler/feature/parser_framework_spec.spl`
- Updated: 2026-08-01
- Status: Active
