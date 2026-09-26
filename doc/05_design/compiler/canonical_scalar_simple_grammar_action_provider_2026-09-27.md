<!-- codex-design -->
# Canonical scalar Simple grammar/action provider

**Status:** implementation design; provider unavailable until the gates below pass.
**Authorities:** `doc/02_requirements/feature/parser_framework.md` REQ-001..003 and REQ-008; `doc/02_requirements/nfr/parser_framework.md` NFR-001..003 and NFR-006..007; `doc/02_requirements/feature/environment_optimized_dynamic_libraries.md` REQ-008..009; `doc/02_requirements/feature/simple_platform_unification.md` REQ-003..004. This addendum resolves the older cutover text in `doc/05_design/parser_framework.md` against the later requirement to retain an independent legacy oracle.

## Current boundary

`src/compiler/10.frontend/core/frontend.spl` admits only `LegacyReference` and reports `canonical_scalar_simple_grammar_action_engine_unavailable`. Its four retained differential cases cover reset-valid, reset-invalid, append-valid, and isolated-invalid behavior. The shared `parse_run_cpu_reference` executes a lexical DFA and emits tokens/diagnostics; `ParseDialect` carries `grammar_program` and `action_program` as `u32` identifiers. Those IDs are not executable grammar or action programs. The open parser equality lane may strengthen lexical comparison, but lexical equality cannot satisfy AST/HIR admission.

The current recursive-descent frontend remains callable through `core_frontend_parse_legacy_reference` as an independent reference and fallback. The candidate may not call `parse_module`, `parse_module_file`, or any legacy rule/action body. Differential runs execute each implementation in an isolated frontend session, snapshot its output, and compare stable semantics; the production hot path executes one admitted provider.

## Ownership and interface plan

| Owner | Planned surface | Obligation |
|---|---|---|
| `std.common.structural.parse` | Versioned `ParseGrammarProgramV1`, `ParseActionProgramV1`, `ParseDialectProgramV1` value records and validators | Hold bounded rule/action tables, entry rules, schema and dialect identities; reject unknown opcode/version, invalid offsets, cycles without progress, and count overflow before execution. Keep the existing lexical-only `ParseDialect` ABI valid until a versioned adapter is qualified. |
| `std.nogc_async_mut.structural.parse` | `parse_run_canonical_scalar_v1(dialect, request)` | Interpret the validated program against snapshot-owned bytes and lexical tokens, reserve exact source-ordered output ranges, then commit nodes/actions/diagnostics through one sink. No compiler AST import, per-token provider lookup, shell-out, or hidden GPU state. |
| `compiler.frontend.structural_adapter` | `simple_dialect_program_v1`, `simple_canonical_ast_bridge_v1` | Extract Simple rule/action meaning from the existing handwritten parser into typed tables; map generic action events to the existing AST/HIR schema, including interpolation and placeholder transforms. This is the only compiler-specific producer of Simple program data. |
| `compiler.frontend.core` | Existing `ParserProviderV1` admission/session seam | Pin provider, grammar/action/schema and source generations per session. Reject the candidate before mutating parser state until exact parity evidence is admitted. Keep `LegacyReference` as default and independent oracle. |
| Test owner | `ParserSemanticSnapshotV1` normalized comparator | Capture ordered tokens, regions, action events, AST/HIR projection, byte spans/source mappings, diagnostics, invalidation and deterministic hash from both isolated executions. Exclude allocator IDs, timing and backend labels from equality. |

These names define the handoff boundary; their record layout and opcode numbers remain private until a focused validator and differential corpus prove them. `FrontendFacetV1` stays the coarse provider boundary. A new `ParseDialectProgramV1` must not silently reinterpret the existing opaque `u32` fields or publish a V1 wire ABI before the dynload ABI review.

## Execution and cutover sequence

1. **Freeze the oracle.** Capture current accepted/malformed Simple behavior with independent process-scoped snapshots. Pin the source revision and output schema. Changes to the oracle after this point require a new baseline receipt, rather than silently redefining parity.
2. **Inventory grammar and actions.** Trace every existing parser rule, token kind, recovery branch, interpolation/placeholder transform, span conversion and diagnostic emission. Each rule/action gets one stable table entry or an explicit unsupported reason. No handwritten subset may be promoted as the full Simple dialect.
3. **Build and validate programs.** Generate bounded typed grammar/action tables from that inventory. Validate all offset/count arithmetic before allocation, reject unknown instructions, and prove progress for repeats/recovery. Keep table construction outside the parse hot path; cache per immutable dialect/schema generation.
4. **Execute scalar semantics.** Feed the same snapshot and declared lexical token stream to the candidate grammar interpreter. Count, scan, reserve and emit into disjoint source-ordered ranges. Emit compiler-neutral action events; the Simple bridge materializes the existing AST/HIR shape without calling the oracle.
5. **Compare in isolation.** Run the frozen oracle and candidate on every retained case under separate frontend state. Compare the normalized result fields listed above, including error order and append/isolation transitions. A mismatch yields a field/case-specific receipt and leaves candidate admission false.
6. **Admit explicit sessions.** Only a complete passing Simple corpus plus NFR-003 and memory evidence may change `parser_provider_v1_admit`. Pin the admitted grammar/action/schema and source generations. Default remains legacy until the selected rollout stage; keep the oracle available after default promotion for differential verification and rollback.

## Required differential corpus

The four cases already in `parser_provider_v1_canonical_scalar_required_cases` are the first smoke set, not a promotion corpus. Add valid and malformed declarations, nested expressions/types, generic close tokens, Unicode identifiers and malformed UTF, indentation/dedent continuation, strings/escapes/interpolation, custom blocks, preprocessing, recovery after multiple errors, multi-file append, repeated reset and isolated parse after an error. Include source edits that change an earlier lexical state and downstream region; compare incremental output with a clean full parse before claiming invalidation parity. Every declared dialect is qualified separately; Simple parity cannot admit SDN or sosh.

For each case compare ordered tokens, regions, action/HIR projection, source mappings, diagnostics, invalidation, and semantic hash. A case with unsupported action semantics is a failed admission row, not a scalar fallback that counts as candidate execution. The candidate receipt must say whether legacy or canonical code actually executed.

## Verification and budgets

- Extend `test/01_unit/compiler/frontend/parser_provider_v1_spec.spl` with a positive candidate admission test only after the production engine exists. The existing negative prerequisite and refusal tests remain until then. Use `test/03_system/app/compiler/feature/environment_optimized_dynamic_libraries_spec.spl` REQ-008/009 as the system flow; its fail-fast helpers remain red until a real production owner replaces them.
- Run a source-matched pure-Simple interpreter/native differential matrix, then compiler, lib, MCP and LSP checks required by the repository rules. Seed-only execution and source presence do not qualify the provider.
- NFR-001 requires exact semantic equality. NFR-002 requires at most 50% of retained pre-change multifile peak parser RSS with no retained stage growth. NFR-003 limits median scalar slowdown to 10%. Retain binary/source/fixture identities, p50/p95, maximum RSS and allocation counts. No new per-request full-tree scan, file reread, subprocess or environment probe enters the hot path.
- SIMD, GPU, generated sibling and automatic selection remain closed until this scalar result is independently qualified. Candidate unavailability, malformed programs, stale generations and missing parity receipts fail before any frontend state mutation.

## Design reconciliation

The July parser design's Wave 1b instruction to delete old rule bodies conflicts with the later selected platform and dynload requirements for an independent legacy oracle. The production grammar becomes single-source after admission; the frozen handwritten implementation remains in a reference-only boundary. This preserves an independent correctness check without running two grammars in the production hot path.
