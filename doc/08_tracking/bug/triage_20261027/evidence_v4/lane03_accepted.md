# V4 lane 03 accepted evidence

Accepted classifications in V4: 160. Assessment target: `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`.

- 157 accepted records are inherited field-for-field from V3; their detailed evidence is preserved in [V3 lane 03 evidence](../evidence_v3/lane03_accepted.md).

- 3 additional accepted records are detailed below.

## interpreter_return_boundary_never_merges_shared_collections_2026-08-17 — Shared root cause: the interpreter merges shared collections on the ARGUMENT boundary only, never on the RETURN boundary

- Source receipt: `first_half_final_triage`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:1179-1218,1551-1571; doc/08_tracking/bug/interpreter_return_boundary_never_merges_shared_collections_2026-08-17.md:8-100; doc/08_tracking/bug/interpreter_binding_class_typed_field_snapshots_instead_of_aliasing_2026-08-10.md:368-373; research_v2_09.csv#interpreter_return_boundary_never_merges_shared_collections_2026-08-17; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/interpreter/self_field_assign_spec.spl:27-31,62-67,131-150; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:1179-1218,1551-1571
```
- Review rationale: The concrete fixture does not return its mutated collection: write_struct_dict_holder mutates the argument self.values and returns DictWriteResult.Success with no payload. Its comparison helper takes a class, while the failing helper takes a struct. Thus the claimed controlled experiment changes receiver value/reference identity as well as returning a result; it cannot establish that containers crossing a return boundary are the common root. The existing merge operates on Object arguments, while the separate class-binding evidence explicitly differentiates value arrays/structs from reference classes. Accept uncertainty about this universal root-cause record after investigating the actual fixture; preserve the historical failures and require a declared container-sharing contract and matched class/struct controls before selecting return-wide merging.
- Review corrections: The report causal inference is unsupported by its own concrete fixture. No invalid label and no structural return-merging proposal; classification uncertainty is now based on the actual confounded experiment.

## interpreter_unresolved_enum_import_fails_open_symbolic_match_2026-08-18 — Interpreter: unresolved enum import fails open — variant access and match work symbolically

- Source receipt: `first_half_final_triage`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: src/compiler_rust/compiler/src/interpreter/expr/calls.rs:891-982; src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs:1863,2482; doc/08_tracking/bug/interpreter_unresolved_enum_import_fails_open_symbolic_match_2026-08-18.md:7-43; research_v2_09.csv#interpreter_unresolved_enum_import_fails_open_symbolic_match_2026-08-18; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter/expr/literals.rs:300-432; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter/expr/calls.rs:526-594,891-985
```
- Review rationale: The original ByteOrderX program and historical seed warning/output are specific evidence of a real fail-open. Target identifier evaluation constructs EnumType only for registered enums and otherwise reaches undefined-variable error; field access first permits special Option handling and unqualified function/class lookup, then evaluates the receiver and validates enum/variant identity. No unconditional unknown-capitalized-enum symbolic constructor was found on this inspected route. That is a source/artifact evolution limit, not proof the original observation was false. The historical import-created binding/producer is not recovered, so no current fixed claim or generic hard-error patch is admitted. Accept valid/unknown/current-untested with the original seed digest/import-binding trace remaining necessary for diagnosis.
- Review corrections: Reject the inference that the remaining import WARN alone demonstrates the original symbolic bypass. Accept conservative historical validity without asserting present reproduction or a causally known patch.

## llm_caret_unit_specs_rotted_2026_10_19 — llm_caret unit specs fail at source: 4 parse errors (unterminated docstring, stray indent) and claude_cli_spec calls undefined _Q/_escape_json

- Source receipt: `first_half_final_triage`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bug_db.sdn#llm_caret_unit_specs_rotted_2026_10_19; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bug_db.sdn:19; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/llm_caret/claude_cli_spec.spl:193-203; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/llm_caret/openai_api_spec.spl:1-30; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/llm_caret/claude_api_spec.spl:1-25; reviews/research_v2_12.md#llm_caret_unit_specs_rotted_2026_10_19; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/llm_caret/openai_api_spec.spl:1-248; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/llm_caret/claude_api_spec.spl:1-217; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/llm_caret/retry_spec.spl:26-68; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/llm_caret/claude_full/ink/terminal_querier_spec.spl:38-70; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/llm_caret/claude_cli_spec.spl:7-24,193-203
```
- Review rationale: Whole-file delimiter scans find exactly one triple-quote occurrence in each API spec, the opening on line 2; no closing delimiter exists. Retry has an indented it block immediately after a top-level use at line 34 with no containing describe. Terminal querier mixes nested call-style it(fn...) into an existing scenario; the claimed RParen parser rejection is not requalified here. Claude CLI now imports Q/escape_json and its inspected mock helper uses them, although duplicate imports/constants and inline production-name definitions remain. Therefore the aggregate fixed_pending proposal is contradicted by concrete surviving source damage. Validity is established without claiming every diagnostic has the same root; full repair strategy remains unknown because parser admission and all duplicated helper/body contracts were not qualified.
- Review corrections: API quote balance and retry orphan indentation are directly established, rather than inferred from opening excerpts. Q/escape_json correction is partial and cannot establish five-file repair.
