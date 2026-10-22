# ISA registry frozen contract

Status: authored, tests first, runtime UNRUN. Contract version: simple.isa.registry.v1. Existing requirement: REQ-MC-009; D0; research §7.1–7.2. No new requirement IDs.

## Production interfaces

All text fields use `text`; counts use `i64`; lists use `[T]`.

- `IsaAuthority(isa, spec_version, snapshot_sha256: text, operation_ids: [text])`.
- `IsaLimits(max_source_bytes, max_depth, max_operations, max_text_bytes, max_list_items: i64)`; all positive. Test defaults: 1048576, 64, 4096, 4096, 64.
- `IsaOperation(id, spec_version, semantic_op, element, shape: text, required_features: [text], lowering, encoder, decoder, fallback: text, verification: [text], reason: text)`.
- `IsaRegistry(schema, isa, spec_version, source_sha256: text, operations: [IsaOperation])`.
- `RegistryError(code: text, path: text)`; path is a stable location, not an exception dump.
- `VerificationObligation(operation_id: text, evidence_kind: text)`.
- `app.isa_registry.parser.parse_registry(source: text, authority: IsaAuthority, limits: IsaLimits) -> Result<IsaRegistry, RegistryError>`.
- `app.isa_registry.parser.validate_registry(registry: IsaRegistry, authority: IsaAuthority, limits: IsaLimits) -> Result<IsaRegistry, RegistryError>`.
- `app.isa_registry.generator.coverage_table(registry: IsaRegistry, authority: IsaAuthority, limits: IsaLimits) -> Result<text, RegistryError>`.
- `app.isa_registry.generator.verification_obligations(registry: IsaRegistry, authority: IsaAuthority, limits: IsaLimits) -> Result<[VerificationObligation], RegistryError>`.

Generators revalidate typed inputs; callers cannot bypass membership or lowering validation by constructing a struct. Validation does not mutate input. Source-byte/depth limits apply during decoding; typed entrypoints enforce all structural/text/list/row limits and authority limits (there is no fictional source byte length).

## Closed SDN grammar

One `(isa_registry schema: "simple.isa.registry.v1" isa: "..." spec_version: "..." source_sha256: "..." operations: [(isa_operation ...)])` record and EOF. Fields may appear in any order; commas separate array elements; whitespace separates record fields. Scalars are quoted text only. Arrays are explicitly bracketed, never coerced. Supported string escapes: quote, backslash, n, r, t; reject invalid escapes, unescaped controls, unterminated strings and trailing input. Depth counts root record as 1, operations array as 2, operation record as 3 and nested list as 4. No comments, aliases, implicit values or extension keys in v1.

Envelope fields are exactly schema, isa, spec_version, source_sha256, operations. Operation fields are exactly all IsaOperation fields above; reason is required but may be empty except for unsupported/unverified. Required features and verification are sets represented as arrays: duplicate entries reject; empty lists are allowed and do not imply evidence. All fields are mandatory. IDs and set entries are nonempty ASCII identifiers using letters, digits, dot, underscore, colon or hyphen. Other text fields are nonempty except encoder, decoder and reason. Digests are exactly 64 lowercase hexadecimal characters. Operation spec_version equals envelope revision. Limits include authority identity text/IDs and all operation text/list entries. Authority IDs are unique and nonempty, and their count must fit max_operations.

Lowering enum is exactly native, synthesized, library, llvm, unsupported, unverified. Fallback is exactly forbidden. No encoder/decoder name proves existence or evidence.

## Refusals

Stable codes: invalid_limits, source_limit, depth_limit, text_limit, list_limit, operation_limit, syntax, duplicate_field, unknown_field, missing_field, field_type, schema_version, invalid_text, invalid_digest, invalid_lowering, fallback_forbidden, reason_required, duplicate_list_item, authority_empty, authority_duplicate, authority_mismatch, duplicate_operation, operation_version, universe_mismatch. Malformed text fails before semantic validation. Tests mutate one property at a time except byte/depth capacity tests; resource refusals happen before consuming over-limit storage. Precise path diagnostics are required but first-error ordering among unrelated semantic violations is not contractual.

## Deterministic output

Coverage TSV UTF-8, LF, final LF: header `operation_id\tlowering\treason\tverification\n`; sorted rows contain those four columns. Verification IDs sort lexically and join with comma. Escape backslash, tab, CR and LF in textual columns as backslash sequences. No extra summary/percentage. Empty reason and verification are empty cells. Comparison is bytewise ASCII for identifiers. Sorting is independent of source/authority/list order. Obligation array sorts by operation ID then evidence kind and contains exactly the unique pairs declared in verification, including unsupported/unverified rows. Missing evidence is visible, never fabricated.

## Frozen test/manual names

Fixtures: `fixture_authority`, `fixture_limits`, `operation_source`, `registry_source`. Checkers: `check_parse_error`, `check_coverage`, `check_obligations`. All call production APIs and fail on unexpected Result variants; none substitute a parser or generator. Manual steps: Load the pinned fixture authority; Parse the registry; Inspect declared coverage; Inspect required verification obligations; Reject invalid registry input. Source owner: implement_isa_registry_tdd. Design/spec owner: astra_isa_registry_design_tests. No UI; no new runner.

## Review amendment 1

Array trailing commas are syntax errors for both scalar-list and operation-list readers. Public APIs and accepted v1 grammar are unchanged. Additional strict scanner, exact-capacity and typed-mutation scenarios extend the acceptance suite to 32. Diagnostic paths must validate identifier bounds before concatenating caller-provided IDs. Byte-limit and allocation-cost evidence still requires qualified runtime instrumentation.
