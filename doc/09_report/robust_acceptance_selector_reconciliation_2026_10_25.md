# Robust acceptance selector reconciliation — 2026-10-25

## Scope and authority

This is a source/selector reconciliation at `release_phase3`
`9929e6f62a0676450047d08385b431492cbd2db2`, not an execution report.
The owning matrix is [`doc/03_plan/plan.md`](../03_plan/plan.md), section
“Eighty-two-scope matrix”. Its historical 378-entry external manifest and
GEN2 pins are not rewritten. All 82 scope verdicts remain UNRUN.

The inspected plan blob `e856384ebcbccca62dea181c9efa7b30bc4759b9` was also
present on remote `release/1.0.0` at
`a065e4c45f82ccc5aeb8bba3cd60097bd24b95f5` during this audit. Equal plan
blobs do not establish equal implementation or test blobs across branches.

## Inventory and method

The current matrix originally named 261 unique backtick-delimited test paths
ending in `.spl`: 211 tracked paths and 50 absent paths at the inspected
source. This is different from the 378 manifest entries across 77 scopes;
a single path can serve multiple rows, and the manifest includes selectors
not reproduced by this Markdown extraction.

A bounded `rg --files test` basename/path search found 34 potential relocated
paths. Reading imports, active scenario bodies and assertions admitted 30
old selectors to 29 current files. Two old compiler-Span aliases intentionally
converge on one production Span spec. Four apparent relocations were rejected
as production acceptance substitutes. Filename and owner-symbol searches found
no equivalent for the other 16 missing selectors. Existing similarly named
source-model tests do not discharge specific CFG/loop/source-authority cases.

The current matrix now names 231 unique paths: 211 present and 20 marked
OPEN. It retains existing insufficient candidates with explicit limitations;
211 is a presence count, not a count of valid or passing acceptance specs.
No tests, builds, compiler, proof checker or generator were run.

## Accepted selector mappings

Each Git blob below pins the inspected target at the frozen source. The
scenario text identifies the bounded behavior available there; it does not
claim the containing feature is complete. Paths remain relative to the repo.

| Old selector | Current selector | Target blob | Inspected scenario / scope limit |
|---|---|---|---|
| `test/unit/app/compiler_schema/compiler_schema_extract_spec.spl` | `test/01_unit/app/compiler_schema/compiler_schema_extract_spec.spl` | `771724790f34a6cdcd36a0402c0690eca84ff43e` | extracts every variant of the fixture enum; names variants without their payload |
| `test/unit/app/compiler_schema/compiler_schema_grammar_spec.spl` | `test/01_unit/app/compiler_schema/compiler_schema_grammar_spec.spl` | `729b87670a83ceb0e43032d7cbdc47a321ee2199` | extracts only parse_* entry points; records the declaring file relative to the repo root, with its line |
| `test/unit/compiler/transition/coverage_state_spec.spl` | `test/01_unit/compiler/transition/coverage_state_spec.spl` | `13b95162b038c1dd42c5c6804cca578407a46472` | round-trips each of the four states through its SDN tag; has no Missing state — the tag is rejected like any other unknown |
| `test/unit/compiler/transition/hir_type_to_mir_type_coverage_spec.spl` | `test/01_unit/compiler/transition/hir_type_to_mir_type_coverage_spec.spl` | `b2ff4abb24d5d862a7ec0118597aa0bdd30a435c` | loads without a single parse error; declares all 27 HirTypeKind variants — Missing is empty |
| `test/unit/compiler/transition/mir_inst_to_llvm_coverage_spec.spl` | `test/01_unit/compiler/transition/mir_inst_to_llvm_coverage_spec.spl` | `d3e726ced68ec9dee8cee357f928295f46295421` | loads without a single parse error; declares all 126 MirInstKind variants — Missing is empty |
| `test/unit/compiler/transition/transition_table_validator_spec.spl` | `test/01_unit/compiler/transition/transition_table_validator_spec.spl` | `1519964343406fdb0d06dd534757ae25fc913b00` | keeps every repeated transition block; parses each row's state from its own fields |
| `test/unit/compiler/frontend/enum_extension/enum_extension_grammar_spec.spl` | `test/01_unit/compiler/frontend/enum_extension/enum_extension_grammar_spec.spl` | `244b51a155175d68358840f5deb2a8f7016b56f3` | leaves a closed enum's region flags false; sets complete_open for a trailing empty 'complete:' section |
| `test/unit/app/any_audit/any_audit_classify_spec.spl` | `test/01_unit/app/any_audit/any_audit_classify_spec.spl` | `1345c53907101d0e1b5d99f903365b9230115c38` | blanks a double-quoted span so a string cannot report an Any; drops an unquoted trailing comment |
| `test/unit/compiler/common/assurance/unsafe_capabilities_spec.spl` | `test/01_unit/compiler/common/assurance/unsafe_capabilities_spec.spl` | `8b23e0b7cb95f5ef9f11ff983a6dc9f0c58c9134` | carries type_erasure as a real member of the table; round-trips every capability through its canonical spelling |
| `test/unit/compiler/semantics/any_escape/unsafe_block_capabilities_spec.spl` | `test/01_unit/compiler/semantics/any_escape/unsafe_block_capabilities_spec.spl` | `c86cdc80167c1ada29d464a6887880fa40d375fd` | keeps ordinary unsafe and danger calls after contextual rollback; diagnoses missing commas in recognized unsafe headers and then recovers |
| `test/unit/runtime/runtime_value_test.spl` | `test/01_unit/runtime/runtime_value_test.spl` | `fbb81cf27de89ca3919427efbd97b3f0726193b2` | preserves integer local parameter return and render boundaries; distinguishes false true and integer zero through Any |
| `test/unit/compiler/mono/mono_template_pruning_spec.spl` | `test/01_unit/compiler/mono/mono_template_pruning_spec.spl` | `d7b46060174b6654afe79102237c747b879d7903` | removes the template that has a specialization; still emits the specialization |
| `test/unit/compiler/mono/mono_cache_efficiency_spec.spl` | `test/01_unit/compiler/mono/mono_cache_efficiency_spec.spl` | `37e734958503fb81884bae2aa77aad1ea3d94868` | restores actual saved metadata counts and the persisted oldest key; counts duplicate keys once and reconstructs oldest after the last duplicate wins |
| `test/unit/compiler/loader/completeness_seal/completeness_seal_spec.spl` | `test/01_unit/compiler/loader/completeness_seal/completeness_seal_spec.spl` | `7b035c5da47a80286deec702770ffe9262e46620` | reads the §13.2 extension shape and the §16.4 module shape from one file; resolves every §13.2 operation to its declared handler |
| `test/unit/compiler/loader/completeness_seal/source_manifest_spec.spl` | `test/01_unit/compiler/loader/completeness_seal/source_manifest_spec.spl` | `1b410dad7f672e4c06a9c1bc187d183e7f31ddd2` | leaves a closed enum's HIR flags false and reports no open enum; carries complete:/dyn: sections onto HirEnum |
| `test/unit/compiler/loader/completeness_seal/loader_admission_spec.spl` | `test/01_unit/compiler/loader/completeness_seal/loader_admission_spec.spl` | `85abed29ff1e46d94c2c81da6a28495349016487` | admits a clean candidate against the frozen seal; publishes the admitted module as generation 1 |
| `test/unit/app/lsp/definition_spec.spl` | `test/01_unit/app/lsp/definition_spec.spl` | `68701f9f10e25f39562eb3d6cfc79462e1066c32` | returns the actual declaration location for a selected function call |
| `test/unit/app/lsp/hover_handler_spec.spl` | `test/01_unit/app/lsp/hover_handler_spec.spl` | `0cfaf44c9c01a76f345c2788472b3159493ec141` | returns markdown content derived from the real source declaration |
| `test/unit/app/lsp/server_query_integration_spec.spl` | `test/01_unit/app/lsp/server_query_integration_spec.spl` | `65a1d03b657ee3128f91a338b29c73ff7171b05f` | keeps definition and references attached to the selected local symbol |
| `test/unit/app/lsp/compiler_query_api_spec.spl` | `test/01_unit/app/lsp/compiler_query_api_spec.spl` | `4e66d7276e221ff324ba56a7cb30bf69143ae06d` | answers definition, hover, and references for a parsed source symbol; resolves a selected shadow binding and excludes non-reference text |
| `test/unit/compiler/backend/neon_emit_spec.spl` | `test/01_unit/compiler/backend/neon_emit_spec.spl` | `6afcab83f9fcf9f05a2e76fdc4335d62cc05230c` | FADD V0.4S V0.4S V0.4S emits 4 bytes; FADD V0.4S V0.4S V0.4S byte0 is 0x00 |
| `test/unit/compiler/backend/sve2_emit_spec.spl` | `test/01_unit/compiler/backend/sve2_emit_spec.spl` | `300f58032aa52903e1fabeee84ced55bf543b7b9` | ADD Z0.S Z0.S Z0.S emits 4 bytes; ADD Z0.S Z0.S Z0.S byte0 is 0x00 |
| `test/unit/compiler/backend/rvv_int_emit_spec.spl` | `test/01_unit/compiler/backend/rvv_int_emit_spec.spl` | `2e2eb575af8ea709f32f6033992b0fc21b2d3494` | emit_vadd_vv vd=0 vs2=0 vs1=0 — zero-register canonical; emit_vadd_vv vd=1 vs2=2 vs1=3 — non-zero registers |
| `test/unit/compiler/borrow/borrow_check_spec.spl` | `test/01_unit/compiler/borrow/borrow_check_spec.spl` | `b8df54e1eaba08a455b0e428667e69a8e9249d5d` | detects use-after-move at the same program point; detects use-after-move at a LATER program point |
| `test/unit/lib/nogc_async_mut/async_host_spec.spl` | `test/01_unit/lib/nogc_async_mut/async_host_spec.spl` | `64f41d1cbc50f941feec1b0d6550c4a5abf28596` | should define host future states and completion APIs; should define promise pair completion and failure APIs. Source-surface assertions only; no async mutex/queue execution. |
| `test/unit/lib/engine/resource_handle_spec.spl` | `test/01_unit/lib/engine/resource_handle_spec.spl` | `a4a505245869b3ffc6d3c3c5dfcb7f1c11e75060` | inserts and retrieves a value; returns nil for invalid index |
| `test/unit/.../span_spec.spl` | `test/01_unit/compiler_shared/diagnostics/span_spec.spl` | `75b37151d59af7767aa5575a2aeeece6c20d5738` | constructs a nonempty span with truthful stored and computed lengths; constructs an empty location without inventing an extent. DS1 diagnostic Span requirement disambiguates this elided path from ByteSpan. |
| `test/unit/compiler_shared/diagnostics/span_spec.spl` | `test/01_unit/compiler_shared/diagnostics/span_spec.spl` | `75b37151d59af7767aa5575a2aeeece6c20d5738` | constructs a nonempty span with truthful stored and computed lengths; constructs an empty location without inventing an extent |
| `test/unit/lib/log_lite_ring_spec.spl` | `test/01_unit/lib/log_lite_ring_spec.spl` | `4e201cf6ddd994c3536d62fff23c69a13cbb1850` | AC-5: LogRecord is exactly 40 bytes; AC-5: field offsets match Phase-3 §C lock |
| `test/unit/compiler/common/assurance/evidence_receipt_spec.spl` | `test/01_unit/compiler/common/assurance/evidence_receipt_spec.spl` | `37294ab4e07be23ab091b442b6299c81d81b87c7` | round-trips through its canonical text form; hashes identically for identical content and differently for any change |

## OPEN: absent tracked counterparts

These are missing acceptance selectors, not a declaration that all associated
implementation is absent. Recovering a donor requires a source/requirement
comparison and tests before it can join the current selector set. Existing
narrower specs in the same rows are preserved.

| Missing selector | Affected scope IDs | Remaining acceptance boundary |
|---|---|---|
| `test/02_integration/compiler/semantic_api_enum_payload_spec.spl` | PUBLIC-SEMANTIC-GRAPH | Post-resolution recursive public API checking through enum payloads and extern boundaries. |
| `test/01_unit/compiler/mir/verification_source_artifact_authority_v1_spec.spl` | FORMAL-C1-ARTIFACT-AUTHORITY | Actual compiler artifact/source authority binding and rejection of mismatched provenance. |
| `test/01_unit/compiler/codegen/mir_switch_signedness_v1_spec.spl` | FORMAL-RESOLVED-CONTINUATIONS, FORMAL-PHYSICAL-ACCOUNTING, C4-HIR-CFG | The named switch/loop/CFG proof transport and production-to-model behavior; existing generic source_model tests are not substitutes. |
| `test/01_unit/compiler/mir/loop_resource_account_v1_spec.spl` | FORMAL-RESOLVED-CONTINUATIONS, FORMAL-PHYSICAL-ACCOUNTING, C4-HIR-CFG | The named switch/loop/CFG proof transport and production-to-model behavior; existing generic source_model tests are not substitutes. |
| `test/01_unit/compiler/mir/loop_semantic_codec_v1_spec.spl` | FORMAL-RESOLVED-CONTINUATIONS, FORMAL-PHYSICAL-ACCOUNTING, C4-HIR-CFG | The named switch/loop/CFG proof transport and production-to-model behavior; existing generic source_model tests are not substitutes. |
| `test/01_unit/compiler/mir/loop_semantic_wire_v1_spec.spl` | FORMAL-RESOLVED-CONTINUATIONS, FORMAL-PHYSICAL-ACCOUNTING, C4-HIR-CFG | The named switch/loop/CFG proof transport and production-to-model behavior; existing generic source_model tests are not substitutes. |
| `test/01_unit/compiler/verify/lean_loop_graph_v1_spec.spl` | FORMAL-RESOLVED-CONTINUATIONS, FORMAL-PHYSICAL-ACCOUNTING, C4-HIR-CFG | The named switch/loop/CFG proof transport and production-to-model behavior; existing generic source_model tests are not substitutes. |
| `test/01_unit/compiler/verify/source_model_aggregate_producer_v1_spec.spl` | FORMAL-RESOLVED-CONTINUATIONS, FORMAL-PHYSICAL-ACCOUNTING, C4-HIR-CFG | The named switch/loop/CFG proof transport and production-to-model behavior; existing generic source_model tests are not substitutes. |
| `test/01_unit/compiler/verify/source_model_pure_acyclic_cfg_v1_spec.spl` | FORMAL-RESOLVED-CONTINUATIONS, FORMAL-PHYSICAL-ACCOUNTING, C4-HIR-CFG | The named switch/loop/CFG proof transport and production-to-model behavior; existing generic source_model tests are not substitutes. |
| `test/01_unit/compiler/verify/source_model_scalar_switch_v1_spec.spl` | FORMAL-RESOLVED-CONTINUATIONS, FORMAL-PHYSICAL-ACCOUNTING, C4-HIR-CFG | The named switch/loop/CFG proof transport and production-to-model behavior; existing generic source_model tests are not substitutes. |
| `test/01_unit/compiler/verify/source_model_structured_loop_v1_spec.spl` | FORMAL-RESOLVED-CONTINUATIONS, FORMAL-PHYSICAL-ACCOUNTING, C4-HIR-CFG | The named switch/loop/CFG proof transport and production-to-model behavior; existing generic source_model tests are not substitutes. |
| `test/03_system/compiler/lean_pure_acyclic_cfg_v1_spec.spl` | FORMAL-RESOLVED-CONTINUATIONS, FORMAL-PHYSICAL-ACCOUNTING, C4-HIR-CFG | The named switch/loop/CFG proof transport and production-to-model behavior; existing generic source_model tests are not substitutes. |
| `test/03_system/compiler/lean_pure_cfg_graph_v1_spec.spl` | FORMAL-RESOLVED-CONTINUATIONS, FORMAL-PHYSICAL-ACCOUNTING, C4-HIR-CFG | The named switch/loop/CFG proof transport and production-to-model behavior; existing generic source_model tests are not substitutes. |
| `test/03_system/compiler/lean_pure_scalar_switch_v1_spec.spl` | FORMAL-RESOLVED-CONTINUATIONS, FORMAL-PHYSICAL-ACCOUNTING, C4-HIR-CFG | The named switch/loop/CFG proof transport and production-to-model behavior; existing generic source_model tests are not substitutes. |
| `test/03_system/app/reference_fls/feature/reference_fls_spec.spl` | ISA-REFERENCE-SHARDS | Pinned official-reference ingestion, complete shard coverage, and real CLI/consumer assertions. |
| `test/03_system/app/reference_fls/feature/reference_fls_official_spec.spl` | ISA-REFERENCE-SHARDS | Pinned official-reference ingestion, complete shard coverage, and real CLI/consumer assertions. |

## OPEN: same-name files with insufficient acceptance

These four old selectors are retained as OPEN in the matrix. Existing current
paths are annotated rather than promoted to runnable production acceptance.
The real borrow checker and MIR-span tests already mapped in their rows retain
their narrower scope.

| Old selector | Located candidate | Why it cannot close the requirement |
|---|---|---|
| `test/unit/app/mcp_unit/mcp_lsp_rename_spec.spl` | `test/01_unit/app/mcp_unit/mcp_lsp_rename_spec.spl` | The relocated file checks local strings and keyword lists; no production rename or atomic source/Markdown rewrite is exercised. |
| `test/unit/compiler/semantics/borrow_check_spec.spl` | `test/01_unit/compiler/semantics/borrow_check_spec.spl` | The only active scenario asserts that a pending-reason string is nonempty; the borrow cases are commented out. |
| `test/unit/lib/nogc_async_mut/async_host_mt_spec.spl` | `test/01_unit/lib/nogc_async_mut/async_host_mt_spec.spl` | The only active scenario asserts that a pending-reason string is nonempty; the queue/worker scenarios are commented out. |
| `test/unit/app/debug/remote/dwarf_spec.spl` | `test/01_unit/app/debug/remote/dwarf_spec.spl` | The file defines local SourceLocation/DwarfInfo simulations; it does not invoke production DWARF emission or inspect a generated binary. |

## Concrete next acceptance work

1. **DOC-MARKDOWN-LSP / B5:** replace the local-string rename oracle with an
   actual production rename invocation over source and Markdown, asserting
   atomic edits, redirects, ambiguity refusal and invalidation. The relocated
   `test/01_unit/app/lsp/compiler_query_api_spec.spl` proves current definition,
   hover and references calls, but does not prove rename.
2. **ASYNC-MUTEX / REQ-MC-006:** replace the active pending-reason test with
   actual async-host queue/lock operations, including failed acquisition,
   cancellation/unwind cleanup and no use after unlock. Existing source-surface
   and synchronous `with_lock_guard_spec.spl` cases are retained; they do not
   establish this async behavior.
3. **DEBUG-DWARF-SPANS / DS3 and DS5:** invoke production debug emission and
   inspect the generated executable in each selected debug mode, verifying
   source spans in an actual DWARF consumer. The local DwarfInfo simulation
   cannot replace this gate; `mir_span_thread_spec.spl` remains a narrower
   MIR propagation oracle.

These are independently authorable acceptance gaps. Their implementation
counterparts must be inspected before assigning product-code changes; this
reconciliation does not label them uncoded.

## Validation and handoff

Documentation validation checks the exact 30 replacements, all 29 target blobs,
82 preserved scope verdicts, 20 explicit OPEN missing selectors, and the
unchanged historical portion after the current matrix. The new headings clarify
historical versus current denominators. Whitespace and owned-file checks apply.
Root owns independent review, PR composition and landing; runtime qualification
uses the existing modern SSpec runner once its compiler/runner gates pass.
