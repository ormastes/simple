# V4 lane 06 accepted evidence

Accepted classifications in V4: 153. Assessment target: `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`.

- 12 accepted records are inherited field-for-field from V3; their detailed evidence is preserved in [V3 lane 06 evidence](../evidence_v3/lane06_accepted.md).

- 141 additional accepted records are detailed below.

## pure_simple_ctype_perf_gap_2026-05-18 — Pure-Simple ctype predicates run 0.07x-0.46x of C under Cranelift with no inlining

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/pure_simple_ctype_perf_gap_2026-05-18.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/instr/calls.rs:533; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/mir_inline.rs:5; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/common_backend.rs:2170; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/05_perf/ctype/run_ctype_benchmarks.shs:109
```
- Review rationale: Read original measurements and substantive latest inline/static-LUT corrections: current issue is residual loop/branch and static-array correctness, not simply no inlining. Target ctype inline lowering emits range comparisons, bitwise union and selects; common backend invokes small-function inliner, which considers actual candidate call names. Benchmark requires checksum equality before ratios and optional 0.50 floor enforcement. No current performance ratio inferred from source and no library LUT proposed. Remaining gap: Comparable pinned native/C checksum-throughput receipts and static-global array diagnosis remain absent; not every historical iteration reread.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## pure_simple_hir_untyped_return_tuple_2026-07-31 — Cache-free pure-Simple execution of a dynamic frontend-to-HIR path crashes on an untyped

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/pure_simple_hir_untyped_return_tuple_2026-07-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/function_lowering.spl:227; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/function_lowering.spl:279; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/35.semantics/resolve.spl:372
```
- Review rationale: Complete report retracts untyped-return cause and later Ptr-constructor diagnosis; final trace shows GPU metadata false/empty so ordinary Array reached Vulkan. Target lower_function derives GPU primitives from attributes/function fields; lower_function_with_gpu_metadata only selects Vulkan parameter conversion when normalized target equals vulkan, otherwise ordinary conversion. Resolve copy preserves three GPU fields. This supports the reported ownership seam but does not locate current first loss or sustain title diagnosis. Static-only pass after coordinator clarification; no restart of exhausted runtime cycles. Remaining gap: Trace name-map population/transport and actual module caller before selecting root remedy. Multiple prior three-cycle turns exhaust retry allowance; no unchanged verifier rerun authorized.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. Preserved uncertain validity: report retracts title cause and constructor diagnosis. Coordinator allowed bounded static reading only after exhausted historical retries; no execution.

## pure_simple_native_cache_closure_wide_scope_key_2026_10_20 — Pure-Simple native-build object cache keys the whole source closure: one edited file recompiles every module

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/pure_simple_native_cache_closure_wide_scope_key_2026_10_20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_aot_native_output.spl:963; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/cache/native_source_interface_index.spl:41; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/driver/native_module_cache_key_granularity_spec.spl:45
```
- Review rationale: Complete report distinguishes already-stable scope from per-module witness misses and path-alias residual. Current frozen lookup requires aligned inventory lengths, exactly one module-name hit and exactly one physical-path occurrence; otherwise empty tuple. Immediate callers use retained phase-1 identity owner. Canonical interface index adds absolute alias but invalidates conflicting source facts. Thus two module names for one path intentionally remain uncacheable to avoid wrong-object reuse. Unit world uses canonical paths and real dependency-fact owner, but no native hit-rate receipt. Remaining gap: Review BuildCache module/path composite ownership and migration before relaxing alias refusal; validate native no-edit/body/interface changes with admitted ABI identity.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## pure_simple_provider_host_runtime_capsule_link_required_2026-08-14 — Pure Simple provider host proof needs an admitted runtime capsule; --export-dynamic on

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/pure_simple_provider_host_runtime_capsule_link_required_2026-08-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/smf/provider_loader.spl:263
```
- Review rationale: Full report admits only archive/exact ABI-symbol production, rejects monolithic export-dynamic workaround. Current dynamic admission checks path policy, artifact digest, opens library, rechecks digest stability, then verifies query symbol is process-callable before creating session. That is provider admission, not a complete host runtime capsule/dependency manifest. Bounded provider-gate search did not locate an authoritative integration-link owner; no full execution or known remedy inferred from loader facade. Remaining gap: Locate admitted capsule producer and exact dependency/link manifest integration gate; validate required exports without guessing archives or weakening unresolved-symbol checks.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## pure_sql_reopen_checkpointed_file_stack_overflow_2026-08-25 — Pure-Simple SQL: re-opening an already-checkpointed file stack-overflows — 2026-08-25

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/pure_sql_reopen_checkpointed_file_stack_overflow_2026-08-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl:319; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl:1390; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl:1529
```
- Review rationale: Complete report narrows historical Rust-seed overflow to NOT NULL/persisted schema distinction; nullable control reopened successfully. Current open_deferred calls open, which calls _load_from_disk on existing file. Loader now validates v1/v2/v3 envelope, length/hash, canonical record escapes and structured v3 schema; table/schema records use deserialization and count checks. This substantially evolved restore route does not establish a current NOT NULL recursive cause or prove the historical crash fixed. Remaining gap: Preserve exact historical persisted bytes/schema and trace constraint deserialization/CREATE existing-table path with NOT NULL and nullable controls; current qualification absent.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## puresql_native_mir_failures_2026_10_25 — pure_sql native MIR failures worked around at 9 sites

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/puresql_native_mir_failures_2026-10-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:2243; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/native_trait_conversion.spl:62; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1580; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/02_integration/lib/database/pure_sql_native_mir_regression_spec.spl:24
```
- Review rationale: Full report separates three causes. Target note_container_elem_type excludes positively known enum owner from array record owner; ancestor 3d97632a715 diff adds qualified/unambiguous-enum predicate while preserving record layouts. Method push calls this helper, supporting concrete cause-1 correction. Trait conversion has identity fast paths for matching local HIR and declared container read but still derives concrete owner otherwise; Some payload/field behavior remains unqualified. Integration regression asserts real rowid, replace and LIKE results, not native compiler liveness. Whole report remains open with unknown combined remedy. Remaining gap: Qualify cause-1 enum and struct-array negative controls on rebuilt compiler; independently resolve Some/trait-field owner and flow-narrowed text causes. Historical commit 3d97632a715 inspected on target ancestry.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## query-native-array-tail-range-20261016 — native-range-lowering

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/query_native_array_tail_range_2026_10_16.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/cli/_QueryVisibility/query_commands.spl:666; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/cli/_QueryVisibility/symbol_resolution.spl:15; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:3380; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/function_lowering.spl:1614
```
- Review rationale: Complete report qualifies scoped query workaround only. Target peer_path_tail guards element counts before scalar query_join_slash_tail_v1; helper inserts separator by index position so empty segments/trailing separators survive. Owner-domain resolver also calls it. Current index lowering attempts text range then fatally rejects unsupported array range; generic lower_range runtime-call construction does not override index rejection. Thus native array-tail support is still distinct from working query helper. Remaining gap: Qualify original array-range grammar with actual admitted producer before retiring recovery annotations; helper control PASS at earlier source is not current reproduction.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## query-native-trim-end-dot-20261016 — native-method-resolution

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/query_native_trim_end_dot_2026_10_16.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/cli/_QueryVisibility/symbol_resolution.spl:27; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/cli/_QueryVisibility/symbol_resolution.spl:150; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3829
```
- Review rationale: Complete report distinguishes literal dot-suffix removal from whitespace trim. Actual brace/star import callers retain trim then invoke scalar dot helper; ends_with dot ensures nonempty before substring, preserving internal dots. Current native text-special dispatch includes trim_end but default arity is zero and comment specifies whitespace trimming; reported trim_end(".") has one argument and cannot use that arm. Therefore name presence is not evidence this overload resolved; workaround is still meaningful. Remaining gap: Trace remaining overload resolution and intended literal-suffix contract, qualify real imported module with repeated/interior dots. No root engine remedy or current execution claimed.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## query_lint_unused_nested_scope_2026-08-24 — Query lint UNUSED001 nested-function scope

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/query_lint_unused_nested_scope_2026-08-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/cli/query_lint.spl:452-570
```
- Review rationale: Report identifies nested callable contamination. _check_unused_vars_text advances to function_end+1, while _emit_unused_in_function counts every descendant line and declaration in one table; the indentation boundary only separates siblings. This supports the defect. A scope-owner repair needs capture/shadowing fixtures; its minimal contract and current execution remain unknown.
- Review corrections: queue: inspection_level report_reviewed -> source_reviewed; low research: structural_change yes -> unknown, recommended_action fix_candidate -> keep_open. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## quic_h3_transport_tls_blocker_2026-08-20 — QUIC/HTTP-3 transport blocker (2026-08-20)

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/quic_h3_transport_tls_blocker_2026-08-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/quic/quic_provider.spl:25-54; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/quic/quic_connection.spl:63-114; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/io/quic/quic_connection.spl:9-30
```
- Review rationale: Report retains authenticated TLS/key-installation prerequisites after zero-handle hardening. Current provider returns Unavailable; connection facade now returns terminal closed objects and rejects all I/O, superseding the older conditional native-call description. These protections preserve the real missing transport prerequisite. Concrete TLS owner and authenticated-wire qualification remain absent from this investigation; no known root remedy claimed.
- Review corrections: queue: inspection_level report_reviewed -> source_reviewed; low research: structural_change yes -> unknown. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## readme_arrow_match_arm_syntax_does_not_parse_2026-09-19 — BUG: README documents `| Pattern -> expr` match arms as "preferred", and the parser rejects them

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/readme_arrow_match_arm_syntax_does_not_parse_2026-09-19.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:README.md:442; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser_stmts.spl:2059-2351
```
- Review rationale: The report gives historical case/arrow controls and expressly leaves language intent unresolved. README still advertises preferred arrow syntax; shared statement/expression match parsing routes through parse_match_arms_common. Inspected entry and arm handling support a documentation/parser gap, but the exact rejection and intended grammar require qualification; no automatic README deletion or root fix endorsed.
- Review corrections: queue: validity uncertain -> valid, inspection_level report_reviewed -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## readonly_struct_receiver_copy_registry_exhaustion_2026-08-12 — Read-only struct receiver copies exhaust the receiver registry

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/readonly_struct_receiver_copy_registry_exhaustion_2026-08-12.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/function_lowering.spl:525-554,636-678; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/lexer.spl:607
```
- Review rationale: Full report records registry exhaustion and reverted escape/lifetime shortcuts. Current lowering copies ordinary Named structs but bypasses copying for me, mutable, class, and strict short parameters. Thus legacy allocation risk remains while strict behavior differs. The old CoreLexer.peek artifact has not been correlated with current lexer ownership/build mode, and the dormant copy-scope API does not prove integrated cleanup. Current incident applicability and remedy remain unknown.
- Review corrections: queue: validity valid -> uncertain, inspection_level report_reviewed -> source_reviewed; low research: validity valid -> uncertain, structural_change yes -> unknown, recommended_action fix_candidate -> keep_open. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## recoverable_unwind_backend_abi_missing_2026-08-25 — Recoverable unwind backend ABI is incomplete

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/recoverable_unwind_backend_abi_missing_2026-08-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/native/native_macho.spl:22-43
```
- Review rationale: The report explicitly narrows support to POSIX ELF and leaves composite tags, llvm-lib/C++, RV32 and non-ELF unqualified. Mach-O entrypoints actually call reject_macho_recoverable_unwind before selection, rejecting Throw, Resume and unwind-bearing CallTerminator. This confirms a deliberate remaining backend limitation, not invalidity. Other selector and cross-backend execution claims were not independently qualified; no complete solution is known.
- Review corrections: queue: inspection_level report_reviewed -> source_reviewed; low research: validity uncertain -> valid, inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## redeploy_out_simple_stage2_stale_missing_landed_fix_markers_2026-08-10 — build/redeploy_out/simple_stage2 lacks marker strings for two already-landed fixes

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/redeploy_out_simple_stage2_stale_missing_landed_fix_markers_2026-08-10.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-compiler-provenance.shs:61-77,150-175
```
- Review rationale: Report records exact missing marker observations for old redeploy_out artifact and a distinct historically passing release binary. Current gate still includes that artifact, distinguishes real commit markers from pre-existing ones, and increments failures for missing markers on Simple-symbol-bearing binaries. This preserves the intended provenance invariant. Current admitted artifact identity/contents are unavailable; no present nonreproduction or permission to weaken the gate follows.
- Review corrections: queue: inspection_level report_reviewed -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## redis_tagged_text_runtime_abi_2026_10_11 — Redis tagged text and listener contracts block startup

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/redis_tagged_text_runtime_abi_2026_10_11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/text_extern_abi.spl:263-270; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1184-1212,8384-8465; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:18726-18740; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/mir/redis_tagged_text_extern_spec.spl:4-25; ancestry 19d98c49928
```
- Review rationale: Report separates strict tagged-text mismatches and bind-without-listen from IoError owner corruption. Registry now names the exact three arguments; box_text_abi_args builds length-preserving rt_string_new values and direct pointer bridging excludes boxed positions. C bind now calls listen(128), closing fd on failure. Registry controls preserve environment and foreign boundaries. These are concrete local source repairs; hosted listener/native-byte fixtures and platforms remain unexecuted, and RESP startup is not admitted.
- Review corrections: queue: solution unknown -> known, structural_change unknown -> no, inspection_level report_reviewed -> source_reviewed, recommended_action keep_open -> fixed_pending_verification. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## rel_health_rber_and_corrected_events_blind_to_ladder_recoveries_2026-09-01 — rel_health RBER / corrected_events are blind to every read-retry-ladder recovery

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rel_health_rber_and_corrected_events_blind_to_ladder_recoveries_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simpleos_nvme_fw/fw/fil.spl:252-281; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simpleos_nvme_fw/fw/ftl.spl:243-247; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simpleos_nvme_fw/fw/rel_health.spl:86-95
```
- Review rationale: Report distinguishes final sense correction from actual ladder recovery. Both success exits still return obs.corrected after retry replaces obs; FTL forwards res.corrected unchanged and health only increments events when corrected>=1. Thus retry depth can record recovery while correction counters lose earlier senses. Worst-versus-first accounting is still an owner policy choice, so no selected root remedy/structural claim is asserted.
- Review corrections: queue: inspection_level report_reviewed -> source_reviewed; low research: structural_change no -> unknown, recommended_action fix_candidate -> keep_open. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## relative_use_with_brace_member_list_fails_to_parse_2026-08-17 — Bug: `use .relative.path.{Name}` fails to parse — the seed cannot parse its own compiler source

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/relative_use_with_brace_member_list_fails_to_parse_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/parser_impl/core.rs:545-562,815-816; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/stmt_parsing/module_system.rs:231-256; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser_use_path.spl:32-120
```
- Review rationale: Report isolated the relative-plus-brace combination but its proposed relative parser diagnosis was explicitly hypothetical. Current Rust statement dispatch restricts Use-as-identifier to assignment, allowing relative use to reach parse_use; pure-Simple path parsing handles leading dots then breaks on the brace and parses the member list. These counter the old unsupported-path premise, but the entire seed body/control tests and repair history were not qualified. Keep historical defect open with uncertain target applicability; low-pass known/fixed-pending proposal is not admitted.
- Review corrections: queue: validity valid -> uncertain, inspection_level report_reviewed -> source_reviewed; low research: validity valid -> uncertain, solution known -> unknown, structural_change no -> unknown, recommended_action fixed_pending_verification -> keep_open. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## release_stage1_native_build_worker_sigsegv_2026_10_20 — release.yml stage1 native-build worker SIGSEGVs before producing a binary (linux HIR worker, windows immediate); test runner falls back to the bootstrap-only seed (@workaround)

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/release_stage1_native_build_worker_sigsegv_2026-10-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:.github/workflows/release.yml:945-990; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/release_stage1_native_build_worker_sigsegv_2026-10-20.md
```
- Review rationale: Full report separates Linux HIR-worker SIGSEGV from Windows MSYSTEM crash later replaced by an unresolved runtime symbol. Current workflow attempts stage1, falls back to bootstrap-only seed when producer/output is absent, and labels the fallback producer. This is still a workaround, not compiler repair/admission. Linux source-bound core/backtrace and Windows symbol-provider qualification are missing; root cause and structural remedy remain unknown.
- Review corrections: queue: inspection_level report_reviewed -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## renderdoc_electron_html_gate_spec_daemon_timeout_2026-06-28 — renderdoc_electron_html_gate_spec.spl times out under the SPipe test daemon though the

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/renderdoc_electron_html_gate_spec_daemon_timeout_2026-06-28.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/check/renderdoc_electron_html_gate_spec.spl:46-150; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/daemon_backlog.spl:32
```
- Review rationale: Report contrasts historical daemon timeout with a fast direct gate and later Windows spawn failure, explicitly not verification. Current spec invokes shell gates through rt_process_run and checks typed evidence, including actual controlled pass/non-pass cases. This is more than an empty oracle but cannot establish a timeout cause. The exact active daemon profile, child budget and source-bound daemon-versus-direct receipt remain missing; splitting spec is not a proven remedy.
- Review corrections: queue: inspection_level report_reviewed -> source_reviewed; low research: inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## renderdoc_seed_sigbus_cross_module_call_2026-09-13 — Seed SIGBUS (rc 138) on a cross-module call in the renderdoc tooling — 2026-09-13

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/renderdoc_seed_sigbus_cross_module_call_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-renderdoc-web-diff.shs:123-136
```
- Review rationale: Full macOS report narrows rc138 to an additional cross-module call but does not distinguish JIT compilation from buffered runtime crash. Current liveness gate runs the differ, discards its exit classification and equates missing verdict with likely absent run command. That misleading diagnostic remains supported. Actual cross-module ABI/crash cause needs retained producer and debugger receipt; single-module inlining is only a workaround, so solution/structure remain unknown.
- Review corrections: queue: inspection_level report_reviewed -> source_reviewed; low research: validity uncertain -> valid, inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## resolve_methods_never_runs_on_real_compile_path_2026-09-01 — `resolve_methods` never runs on the real compile path

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/resolve_methods_never_runs_on_real_compile_path_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_hir_pipeline_lowering.spl:1743-1800; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_hir_pipeline_passes.spl:168-181; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/35.semantics/resolve_strategies.spl:30-46; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/35.semantics/resolve.spl:871
```
- Review rationale: The report requires both pass scheduling and receiver type transport. Direct resolve_methods call remains in sources<=0 branch, while resolve_methods_impl has only its definition in scoped driver search. Resolver still errors on nil receiver type, but current resolve_expr constructs resolved_has_type/resolved_type, so the historical universal no-type claim cannot simply be repeated. New sharded HIR path and inferred receiver transport need whole-route trace; conservative uncertainty avoids claiming a one-line fix or current universal failure.
- Review corrections: queue: validity valid -> uncertain, inspection_level report_reviewed -> source_reviewed; low research: inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## resource_borrow_pinning_not_enforced_2026-08-07 — borrow_graph.record_move checks only moved_now, never borrows_of, so borrow pinning

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/resource_borrow_pinning_not_enforced_2026-08-07.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/55.borrow/borrow_check/borrow_graph.spl:652-775; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/55.borrow/borrow_check/nll.spl:573,588; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/resource/resource_borrow_pinning_spec.spl:64-87
```
- Review rationale: Current record_move alone still checks moved_now, but a separate check_consumes_after_propagation consults active borrows and emits Cannot consume borrowed value, with nll statement and terminator calls after propagation. Thus report-wide absence of move-versus-borrow enforcement is stale. Named fixture still declares no locals and only counts errors, so cannot prove SFFI lifetime enforcement. Whole-pipeline nll admission, foreign blocking duration and discriminating diagnostic qualification remain uncertain; do not prescribe already-present borrow checks as missing.
- Review corrections: queue: validity valid -> uncertain, inspection_level report_reviewed -> source_reviewed; low research: inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## resource_decl_and_sffi_attribute_not_parsed_2026-08-07 — resource_sffi_pilot_spec stays RED for a structural reason after WP-A landed the

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/resource_decl_and_sffi_attribute_not_parsed_2026-08-07.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:288-384,725,1377; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:945-973
```
- Review rationale: Report includes contradicting later triage, but substantive WP-A update says pure parser landed while seed-read pilot remained red. Current parse_resource_decl validates pending sffi/prefix, registers the name, serializes and resets metadata; module bridge now calls resource_registry_declare before dropping the marker. Thus neither unparsed keyword nor no downstream metadata is current. Pilot execution and generated adapter/lifetime completeness remain unqualified; no whole-record repair claim.
- Review corrections: queue: validity valid -> uncertain, inspection_level report_reviewed -> source_reviewed; low research: inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## result_bool_array_unwrap_payload_rejected_2026-10-05 — Native Result unwrap rejects boolean and array payloads

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/result_bool_array_unwrap_payload_rejected_2026-10-05.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:949-985,1042-1124; ancestry diff 252ab345a5f
```
- Review rationale: Report specifically requests direct no-default Bool/Array unwrap. Current helper admits exactly those cases, uses enum_payload_value after tag selection, remembers HIR type and array/runtime metadata, and aborts on wrong variant. Ancestry diff adds Bool admission and array ownership markers at the existing helper. This is a bounded source remedy, not proof of native alias semantics; positive, wrong-variant and both-backend fixtures remain unexecuted.
- Review corrections: queue: solution unknown -> known, structural_change unknown -> no, inspection_level report_reviewed -> source_reviewed, recommended_action keep_open -> fixed_pending_verification. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## result_bound_text_payload_lost_in_stage2_native_codegen_2026-09-13 — `case Ok(message):` loses a text payload under Stage-2 native codegen

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/result_bound_text_payload_lost_in_stage2_native_codegen_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_aot_native_output.spl:4408-4445; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1061-1086
```
- Review rationale: Report retains syscall evidence that 37 bytes were read but Result-bound text appeared empty. Current driver still checks runtime file size and re-reads via _sffi_file_read_text when Ok payload length is nonpositive, reporting payload lost when both reads fail. This is explicitly a symptom workaround; unwrap text decoding is a different path from pattern binding and cannot be credited as this incident root repair. A reduced exact-stage pattern-extraction ABI case remains needed.
- Review corrections: queue: inspection_level report_reviewed -> source_reviewed; low research: validity uncertain -> valid, inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## result_err_missing_native_projection_2026_10_12 — Result.err missing native typed error projection

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/result_err_missing_native_projection_2026_10_12.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2363-2398; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/builtin_method_extras.spl:1077-1159; ancestry diff 138315b3863
```
- Review rationale: Current dispatch admits zero-arg err only through proven Result routing; combinator selects E and discriminant 1, preserves source_owner, wraps active payload in Some and opposite variant in None, and remembers Optional<E>. Inspected ancestry diff changes the actual projection owner from ok_hir to source_hir. Concrete local repair is present. Historical producer success does not qualify this composed nominal-record/source_owner target; exact negative/eval-once/backend tests remain unexecuted.
- Review corrections: queue: solution unknown -> known, structural_change unknown -> no, inspection_level report_reviewed -> source_reviewed, recommended_action keep_open -> fixed_pending_verification. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## result_err_record_owner_erased_2026_10_11 — Imported Result Err record field loses provider ownership

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/result_err_record_owner_erased_2026_10_11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/result_err_record_owner.spl:145-235; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/builtin_method_extras.spl:1013-1059
```
- Review rationale: Report proves wrong IoError field offset but explicitly does not decode the actual failing metadata branch. Current owner registry tracks exact callable owners, propagates or invalidates aliases/joins, requires unique physical plus semantic layout, and materializes structs only from matching current declarations while classes keep handles. These are substantive repair mechanisms used by Result projection. Prescan lifetime, all pattern-extraction callers, conflicting-layout fixture and actual incident attribution remain unqualified; avoid a whole-record known/fixed assertion.
- Review corrections: queue: validity valid -> uncertain, inspection_level report_reviewed -> source_reviewed; low research: inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## result_err_unwrap_unsupported_payload_2026-10-24 — result err unwrap unsupported payload (workaround registered)

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/result_err_unwrap_unsupported_payload_2026-10-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/builtin_method_extras.spl:970-1038; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend_plugin/loader.spl:40-47; ancestry diff 0eae1801be4
```
- Review rationale: Report distinguishes enum payload rejection from loader match workaround. Current builtin_result_payload_mir admits only registered enum owner handles and builtin_result_payload marks them runtime values, exactly the ancestry diff. Existing Result.err E/tag routing reaches those owners. Loader still uses tagged match workaround, which is not admission. The bounded enum-owner repair is present; rebuilt producer and errunwrap native fixture remain untested.
- Review corrections: queue: solution unknown -> known, structural_change unknown -> no, inspection_level report_reviewed -> source_reviewed, recommended_action keep_open -> fixed_pending_verification; low research: validity uncertain -> valid, solution unknown -> known, structural_change unknown -> no, inspection_level metadata_only -> source_reviewed, recommended_action keep_open -> fixed_pending_verification. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## result_struct_payload_pushed_into_struct_array_crashes_2026-10-25 — result struct payload pushed into struct array crashes (workaround registered)

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/result_struct_payload_pushed_into_struct_array_crashes_2026-10-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1931-1975; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/cache/cold_hir_semantic_seed_v1.spl:300-311; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/cache/driver_hir_archive_cold_boundary_v1.spl:205-216; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/codegen/native_result_struct_payload_push_spec.spl:14-37
```
- Review rationale: Report retains matched/unwrapped payload failures versus constructor controls and identifies integer-boxing before array push. Both production receipt producers still reconstruct records from fields. Current box_runtime_value_local_is_record recognizes registered layout/HIR record identity but that predicate alone does not prove provenance reaches it for this Result shape. Spec exercises matched and unwrapped values but historical interpreter green is not native evidence. Root guard applicability remains unproven; keep open unknown.
- Review corrections: queue: inspection_level report_reviewed -> source_reviewed; low research: validity uncertain -> valid, inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## result_tuple_unwrap_payload_2026_10_11 — Result tuple unwrap rejects the ranking pair payload

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/result_tuple_unwrap_payload_2026_10_11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:968-975,1072-1074; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/result_tuple_payload.spl:217-228,380-392; ancestry 3a1a2abc4a5
```
- Review rationale: Report requires restoring exact raw native tuple layout rather than rt_tuple_get or numeric i64-to-Tuple cast. Current no-default unwrap admits validated tuple fields and calls recover_result_tuple_payload, which casts to pointer-to-tuple then copies into a fresh typed local. This matches the original repair mechanism. Current field admission is broader than the report and helper is shared with newer Optional paths; full accepted-shape/history/backend audit and ranking closure qualification remain missing, so no blanket known solution asserted.
- Review corrections: queue: inspection_level report_reviewed -> source_reviewed; low research: validity uncertain -> valid, inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## resume_stage3_silent_exit_on_source_drift_2026-09-02 — `resume-stage3-from-admitted.sh` exits SILENTLY (rc=1, zero output) when sources drift

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fix_candidate`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/resume_stage3_silent_exit_on_source_drift_2026-09-02.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/resume-stage3-from-admitted.sh:650-676,1295-1302; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh:959
```
- Review rationale: The historical obsolete/missing-path header is false at this target: bootstrap caller still execs the .sh owner. Source/git/tool preflight comparisons now print specific stderr reasons and exit 1, but post-build source/git/tool comparisons remain bare cmp -s under fail-fast execution. The report explicitly included that second comparison family. Known local remedy is attach named failure diagnostics to remaining comparisons without changing checks or admission; entire record is not fixed.
- Review corrections: queue: validity uncertain -> valid, solution unknown -> known, structural_change unknown -> no, inspection_level report_reviewed -> source_reviewed, recommended_action keep_open -> fix_candidate; low research: validity uncertain -> valid, solution unknown -> known, structural_change unknown -> no, inspection_level metadata_only -> source_reviewed, recommended_action keep_open -> fix_candidate. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## return_type_result_mismatch_class_audit_2026-08-08 — Non-Result declared return types whose bodies return Ok()/Err() remain in owned src after partial fix

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/return_type_result_mismatch_class_audit_2026-08-08.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/validation.spl:418-451; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/src/dl/config_loader.spl:22-52,313
```
- Review rationale: Full audit already excludes validation docstrings and retains a smaller compiler-wide family. Current require/require_all bodies return Optional/array correctly; Err examples are inside documentation. Config loader declares Result and propagates actual Ok/Err. These settle named false positives/partial repairs, not the remaining compiler population. Scratch classifier is not retained here and current exact residual set is unestablished; keep the aggregate uncertain, never close as invalid from the misleading file metadata.
- Review corrections: queue: validity valid -> uncertain, inspection_level report_reviewed -> source_reviewed; low research: inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## rfind_sentinel_vs_optional_contract_split_2026-08-18 — rfind: sentinel (-1) vs Optional contract split across stdlib call sites

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rfind_sentinel_vs_optional_contract_split_2026-08-18.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/path.spl:17-46; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/fs/path.spl:71-110; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3923-3974; ancestry 2ec8e8af7fb
```
- Review rationale: Report distinguishes a real caller contract split from receiver erasure. Current dirname and extension now use negative-sentinel checks, matching fs.Path and MIR rt_string_rfind i64 dispatch; MIR also remembers raw Int HIR type. Named defect is repaired in source, but the report covers roughly six optional-shaped callers and shared find/index_of API policy. That wider set and current interpreter contract were not exhaustively qualified, so whole-record target status/solution remain uncertain rather than fixed from one caller.
- Review corrections: queue: validity valid -> uncertain, inspection_level report_reviewed -> source_reviewed; low research: inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## riscv32_cmo_uses_riscv64_only_provider_2026-08-26 — RV32 cache maintenance imports RV64-only SFFI providers

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv32_cmo_uses_riscv64_only_provider_2026-08-26.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/arch/riscv32/hal_cache.spl:8,115-144; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl:38-81; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/arch/riscv64/boot/freestanding_runtime.c:57-60; ancestry 7f0cef9d1f3
```
- Review rationale: Current RV32 production cache functions call shared CMO wrappers, casting addresses to u64. Those wrappers explicitly invoke rt_riscv64_* unsafe externs, and inspected concrete RV64 provider emits the instructions with 64-bit operands. Scoped RV32 provider search found no matching leaf. Unsafe annotation does not supply the missing target ABI. An XLEN-correct provider/selection and capability admission remain required, but concrete root implementation and structural scope are not established.
- Review corrections: queue: inspection_level report_reviewed -> source_reviewed; low research: validity uncertain -> valid, inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## riscv64_arch_unit_specs_fail_interpreter_2026-06-06 — RV64 arch unit specs (boot/interrupt/trap_frame/trap_model) fail under interpreter mode

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv64_arch_unit_specs_fail_interpreter_2026-06-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/os/kernel/arch/riscv64_boot_spec.spl:33-72; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/arch/riscv64/boot_info.spl:28-48,164-177; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/os/kernel/arch/riscv64_trap_model_spec.spl:45-49; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/arch/riscv64/trap_model.spl:124-145; ancestry ae55a746719
```
- Review rationale: Report gives distinct historical boot/interrupt/trap-model interpreter failures without claiming QEMU. Current boot spec now uses separated boot_info metadata owner and adds DTB controls; boot accessors read retained globals. Timer test still exercises classify_rv64_trap, whose owner masks the interrupt bit and selects TimerInterrupt for the timer code. These concrete intended semantics do not explain or disprove historical interpreter errors; complete interrupt bridge and exact current runner receipts are unavailable. Keep uncertain, unknown remedy.
- Review corrections: queue: inspection_level report_reviewed -> source_reviewed; low research: inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## riscv64_freestanding_bool_in_collection_always_true_2026-09-01 — riscv64 freestanding: a `bool` read out of a tuple or array is ALWAYS `true`

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv64_freestanding_bool_in_collection_always_true_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c:1132-1136; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/common/boot/freestanding_value_registry_impl.h:112-119; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-baremetal-tagged-bool-decode.shs:83-91,156-166; ancestry 88aac2ffe286e111f929a72f5532b9d74ed0b9a1
```
- Review rationale: Read the full correction chain: final diagnosis retracts boxed-closure codegen attribution and identifies linked MIR UnboxInt runtime definition missing tagged-bool arms. Both target runtime definitions independently map 11 to 1 and 19 to 0; the per-definition guard includes a bad-duplicate control. This is the concrete local repair. Historical in-guest parser progress supports past repair only; exact current link winner/backend/guest execution remain untested. No claim that missing-main or the whole row is fixed.
- Review corrections: queue: solution unknown -> known, structural_change unknown -> no, inspection_level report_reviewed -> source_reviewed, recommended_action keep_open -> fixed_pending_verification; low research: validity uncertain -> valid, solution unknown -> known, structural_change unknown -> no, inspection_level metadata_only -> source_reviewed, recommended_action keep_open -> fixed_pending_verification. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## riscv64_freestanding_len_eq_zero_guard_never_fires_2026-09-01 — riscv64 freestanding: `x.len() == 0` is FALSE on a collection whose `.len()` is 0

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv64_freestanding_len_eq_zero_guard_never_fires_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/instr/helpers.rs:50-174; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/instr/methods.rs:88; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:2039; ancestry 88aac2ffe286e111f929a72f5532b9d74ed0b9a1
```
- Review rationale: Final report measures dict len=-1, then correct len=1 after tag-11 admission, explicitly refuting the earlier missing-main hypothesis. Current inline length owner admits tag 11 only when baremetal, routes it to offset-8 load, keeps SplDict offset16 separate, and callers pass ctx.baremetal/fam_arrays. This is a bounded source remedy for the actual dictionary sentinel defect. Exact current RV64 build/guest and target-flag receipts remain untested; missing main is independent and not repaired by this classification.
- Review corrections: queue: solution unknown -> known, structural_change unknown -> no, inspection_level report_reviewed -> source_reviewed, recommended_action keep_open -> fixed_pending_verification; low research: validity uncertain -> valid, solution unknown -> known, structural_change unknown -> no, inspection_level metadata_only -> source_reviewed, recommended_action keep_open -> fixed_pending_verification. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## riscv64_freestanding_me_method_invocation_traps_2026-08-31 — riscv64 freestanding: invoking a `me` method on a class instance traps

- Source receipt: `adjudication_v2_17`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv64_freestanding_me_method_invocation_traps_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/mcp/dispatch.spl:69-108; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/riscv64/toolchain_components_entry.spl:105-132; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/function_lowering.spl:525-554,636-675; ancestry ae55a746719
```
- Review rationale: Full report distinguishes a read-only me find trap from register mutation and explicitly lacks an emitted receiver-ABI diagnosis. Current registry find still reads entries, register concatenates, and guest entry retains the discriminating find-before-register probe. Pure-Simple lowering exempts me/class receivers from struct copying, but that is not proof about the historical seed Cranelift freestanding call ABI. Exact linked receiver argument/entry disassembly and reduced no-field me case remain needed; unknown remedy and structural scope.
- Review corrections: queue: inspection_level report_reviewed -> source_reviewed; low research: validity uncertain -> valid, inspection_level metadata_only -> source_reviewed. Independent rationale above supersedes unsupported raw conclusions; all historical execution remains untested at target.

## riscv64_freestanding_runtime_text_len_and_loop_concat_2026-08-31 — riscv64 freestanding runtime: `text.len()` wrong and in-loop string accumulation loses content (2026-08-31)

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv64_freestanding_runtime_text_len_and_loop_concat_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c:1428
```
- Review rationale: The report update separates the repaired two-argument tagged-string builder ABI from chars-element accumulation ending after one iteration and the surviving MCP trap. Current push decodes a HEAP_STRING handle, copies its bytes, updates length, and returns the builder; this supports that bounded repair but does not explain the iterator/call-boundary residuals. Remaining gap: Need target guest iterator and closure traces; no blanket rt_len tagging or fixed claim.
- Review corrections: queue inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## riscv64_freestanding_text_neq_empty_literal_true_for_zero_length_2026-09-01 — riscv64 freestanding: `text != ""` is TRUE for a zero-length text

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv64_freestanding_text_neq_empty_literal_true_for_zero_length_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/_Ast/module_state.spl:427
```
- Review rationale: The complete report records zero length with a true != empty comparison but also a correct same-image replica, leaving coalesce/literal pooling/comparison causal ambiguity. Current module_decl_at uses env_get_nullable, coalesces empty, and tests length before parsing; the array fallback is repaired, not the engine comparison. Remaining gap: Need original-context literal/comparison lowering and guest raw-value controls.
- Review corrections: research validity: valid -> uncertain; queue inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## riscv64_freestanding_toplevel_decl_walk_names_both_functions_add_2026-09-01 — riscv64 freestanding: the top-level declaration walk yields the SAME function twice

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv64_freestanding_toplevel_decl_walk_names_both_functions_add_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/_Ast/module_state.spl:413; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-decl-index-lookup-not-empty-text-compare.shs:66
```
- Review rationale: Report resolution identifies a missing env entry incorrectly taking the env-first branch, not duplicate slot storage. module_get_decls calls module_decl_at per index; the target length guard preserves the slot fallback. The source guard scans that decision and has a must-fail old-condition fixture. Later ZeroKind is explicitly a different blocker. Remaining gap: Qualify original multi-declaration guest on an identified target artifact; history search reaches transplant 88aac2ffe28, so historical aff24739a15 is not independently admitted as target ancestry.
- Review corrections: queue solution: unknown -> known; queue structural_change: unknown -> no; queue inspection_level: report_reviewed -> source_reviewed; queue recommended_action: keep_open -> fixed_pending_verification; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## riscv64_in_guest_interp_resets_on_cross_function_call_2026-09-01 — riscv64 in-guest: the guest RESETS while executing a cross-function call

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv64_in_guest_interp_resets_on_cross_function_call_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c:1932; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/interpreter_calls.spl:182; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-rv64-unwrap-or-trap-unwraps.shs:180
```
- Review rationale: Report corrects apparent reset to a load fault from a returned Some wrapper. The current caller unwraps resolved HirFunction before call_hir_function; the RV64 owner returns payload for ordinal or hashed Some and traps None. Guard cases compare payload identity and include the old wrapper-return body. This is a causal local repair, separate from later invalid-plus failure. Remaining gap: Current image/link identity and guest run remain unverified; target history -S reaches transplant 88aac2ffe28 rather than proving cited b655e343cdb ancestry.
- Review corrections: queue solution: unknown -> known; queue structural_change: unknown -> no; queue inspection_level: report_reviewed -> source_reviewed; queue recommended_action: keep_open -> fixed_pending_verification; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## riscv64_in_guest_interpreter_blocked_on_baremetal_runtime_2026-08-31 — riscv64 in-guest Simple interpreter blocked on 43 missing baremetal `rt_*` symbols

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv64_in_guest_interpreter_blocked_on_baremetal_runtime_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/os/build-simpleos-riscv64-interpreter-kernel.shs:90; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c:1875
```
- Review rationale: The report explicitly records all 43 symbols plus spl_wffi_call_i64 ported and real links advancing to lexer/payload defects. Current build_row roots the row entry, requires interpreter symbols, ELF text and embedded nonce; real unwrap and WFFI definitions exist. This does not establish the full current 44-symbol closure, so no present link-success assertion is accepted. Remaining gap: Reconcile retained symbol inventory against the exact current linker closure and ELF; no build assigned.
- Review corrections: research solution: known -> unknown; research structural_change: no -> unknown; queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; research recommended_action: fixed_pending_verification -> keep_open; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## riscv64_in_guest_mir_lower_type_zero_kind_on_main_2026-09-01 — riscv64 in-guest: MIR lowering rejects `main` with a raw-0 HirType kind

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv64_in_guest_mir_lower_type_zero_kind_on_main_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1599
```
- Review rationale: The report retracts implicit-return and enum-hash hypotheses and localizes absent-optional extraction in match_result_mir_type. Current code checks extracted nil and invalid kind before lower_type and preserves the existing i64 absence fallback; emit_switch_dispatch uses this helper for its result temp. This repairs the reported site, not the broader optional codegen defect. Remaining gap: Qualify the original RV64 main body; report's later callee-resolution failure is not evidence against this repair.
- Review corrections: queue solution: unknown -> known; queue structural_change: unknown -> no; queue inspection_level: report_reviewed -> source_reviewed; queue recommended_action: keep_open -> fixed_pending_verification; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## riscv_gate_evidence_seed_attributed_bin_release_clobbered_2026-07-27 — Every RISC-V gate result is attributed to bin/release/<triple>/simple which is a Rust seed, not self-hosted

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv_gate_evidence_seed_attributed_bin_release_clobbered_2026-07-27.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-riscv-hardware-gates.shs:72
```
- Review rationale: The report tracks deployed seed attribution across several gates, not simply missing banner detection. Current hardware-gate classifier explicitly recognizes the seed warning but otherwise treats any nonempty successful version output as self-hosted. It improves labeling without proving deployment provenance or all other gate results. Remaining gap: Need admitted deployed binary identity and exact rerun receipts; do not accept the small-model implication that all unknown identities are rejected.
- Review corrections: research validity: valid -> uncertain; research solution: known -> unknown; research structural_change: no -> unknown; queue inspection_level: report_reviewed -> source_reviewed; research recommended_action: fixed_pending_verification -> keep_open; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction. Lower proposal overstates fail-closed unknown identity: nonempty successful output without seed banner is classified self-hosted.

## riscv_gen2_qualification_receipt_authority_2026-08-12 — RISC-V Gen2 Qualification Receipt Is Not an Adversarial Provenance Boundary

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv_gen2_qualification_receipt_authority_2026-08-12.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test/riscv_gen2_qualification_receipt.spl:565; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test/riscv_gen2_qualification_receipt.spl:624; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test/riscv_gen2_qualification_receipt.spl:710
```
- Review rationale: Full report distinguishes controlled-run hash evidence from hostile-filesystem authority. Current composer checks then reopens manifest paths; _g2_copy_bound does file_exists then pathname copy then no-follow/hash, while publication separately creates/checks run directories. These operations do not pin source and destination descriptors across the transaction. Reported authority gap remains supported despite provenance and coverage checks. Remaining gap: A reviewed snapshot/attestation contract spans runtime and composer ownership; exact root implementation and hostile-filesystem qualification remain unknown. History includes af957b18516 hardening, not proof of atomicity.
- Review corrections: queue structural_change: unknown -> yes; queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## riscv_gen2_raw_artifact_writer_provenance_2026-08-12 — vhdl_render/write_production_artifacts are still exported and will pair valid provenance with arbitrary VHDL

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv_gen2_raw_artifact_writer_provenance_2026-08-12.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_vhdl_artifacts.spl:855
```
- Review rationale: The full correction distinguishes the removed Gen2-specific exported bypass from still-public generic helpers. Current writer rejects reserved routes in either manifest or VHDL before removal/write. That is a real public-path repair; the report also tracks unenforced private receipt construction, which this source guard does not resolve. Remaining gap: Trace current compiler visibility/constructor enforcement and negative compile evidence before claiming authority closure.
- Review corrections: queue validity: uncertain -> valid; research solution: known -> unknown; queue inspection_level: report_reviewed -> source_reviewed; research recommended_action: fixed_pending_verification -> keep_open; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## riscv_gen2_stateful_retire_lineage_contract_2026-08-12 — Gen2 parcel frontend cannot reject a pre-reset stale retirement without an architectural retirement producer

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv_gen2_stateful_retire_lineage_contract_2026-08-12.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/hwir/stateful_frontend.spl:112; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/hwir/retirement_composition.spl:164
```
- Review rationale: Current frontend requires matching lineage, parcel, canonical instruction and length; terminal lineage faults before increment. Unlike the old report's no-composition statement, current composition validates exact reset/dispatch/receipt wiring and shared configuration. This is meaningful later contract work, but a schema is not proof of a sole architectural retirement producer or reset-safe emitted execution. Remaining gap: Inspect producer integration, emitted composition and exact-once/reset evidence; target history f6a2414276e and 83a8e879706 identify later composition work.
- Review corrections: queue validity: valid -> uncertain; research validity: valid -> uncertain; research structural_change: yes -> unknown; queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## riscv_qemu_lanes_boot_bare_kernel_without_opensbi_2026-08-09 — RISC-V QEMU scenario lanes still push -kernel instead of an OpenSBI firmware proxy

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fix_candidate`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv_qemu_lanes_boot_bare_kernel_without_opensbi_2026-08-09.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/_QemuRunner/scenario_exec.spl:496; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/_QemuRunner/scenario_disks.spl:176; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/os/qemu_runner_spec.spl:553; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/_QemuRunner/scenario_catalog.spl:203; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/_QemuRunner/scenario_exec.spl:397
```
- Review rationale: Full report's failing operation is build_scenario_command. Current builder still appends kernel and scenario.qemu_extra without reading target.qemu_bios, although filesystem target now says default. Spec requires -bios for both RV64 and RV32. Remedy is to propagate firmware selection through the actual scenario builder while preserving the OpenSBI payload handoff. The public command wrapper calls this builder directly; _scenario_from_target copies qemu_extra but discards qemu_bios. The newer sealed-run route consults firmware separately and does not repair this public builder. Remaining gap: Qualify both public command assembly and boot for each RV lane; do not conflate newer sealed dispatch with the legacy builder.
- Review corrections: queue solution: unknown -> known; queue structural_change: unknown -> no; queue inspection_level: report_reviewed -> source_reviewed; queue recommended_action: keep_open -> fix_candidate; research recommended_action: keep_open -> fix_candidate; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## riscv_scalar_product_vhdl_else_parse_2026-08-12 — Seed parser rejects the RISC-V scalar-product VHDL renderer at `else:`

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv_scalar_product_vhdl_else_parse_2026-08-12.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/riscv_scalar_product_to_vhdl.spl:130
```
- Review rationale: The complete report lacks a token location and says the explicit LSU rewrite did not clear the seed parse failure. Current renderer retains that statement-level LSU path, plus conditional provider expressions and later inline if forms. Target history includes a7c39dc8f5d seed-grammar edits, but neither source appearance nor its title identifies the originally failing Else. Remaining gap: Need located diagnostic and exact producer/grammar fixture; no current parse or formal-spec outcome inferred.
- Review corrections: research validity: valid -> uncertain; queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## riscv_sidecar_contract_antiseed_guard_ineffective_2026-07-27 — RISC-V sidecar-contract anti-seed guard is ineffective against a seed-clobbered `bin/release`

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/riscv_sidecar_contract_antiseed_guard_ineffective_2026-07-27.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-riscv-fpga-sidecar-contract.shs:9; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-riscv-fpga-sidecar-contract.shs:127
```
- Review rationale: Report's path-only classifier missed a seed deployed under bin/release. Current classifier additionally captures version stdout/stderr, rejects seed/Rust/debug banners and failed/empty probes; the main path invokes it before evidence work. Hermetic fixtures include the non-seed-path seed banner. This directly repairs the stated bypass. Remaining gap: Run classifier fixtures and exact selected binary qualification separately; source repair does not make all historical seed evidence self-hosted.
- Review corrections: queue solution: unknown -> known; queue structural_change: unknown -> no; queue inspection_level: report_reviewed -> source_reviewed; queue recommended_action: keep_open -> fixed_pending_verification; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## robust_lint_lane_scan_latency_2026-08-21 — Robust lint lane scan exceeds bounded verification time

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/robust_lint_lane_scan_latency_2026-08-21.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/io/cli_lint_commands.spl:200; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/io/cli_lint_commands.spl:234
```
- Review rationale: Report records directory lint exceeding 120 seconds without phase timings. Current command deduplicates via dicts, discovers each target, creates one command-scoped Linter and policy, reads each source once and passes it to run_lint_source_with_linter_policy. Repeated linter construction is therefore not a demonstrated current cause; no timing proves current latency or identifies residual parser costs. Remaining gap: Need phase timing/warm latency/RSS for the original robust directory; retain unknown root remedy rather than rubber-stamping generic caching advice.
- Review corrections: queue validity: valid -> uncertain; research validity: valid -> uncertain; queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## rt_browser_renderer_externs_missing_in_rust_seed_2026-08-19 — `rt_browser_renderer_*` externs unimplemented in the Rust seed interpreter

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rt_browser_renderer_externs_missing_in_rust_seed_2026-08-19.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/process_ops.spl:1518; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_process.c:2134
```
- Review rationale: Full report names unknown extern in Rust seed. Current Simple facade directly calls rt_browser_renderer_spawn_sandboxed; Linux C owner constructs argv and invokes piped spawn with sandbox=true, whereas non-Linux branch returns -1. Exact-target search of compiler_rust still finds no family registration. This supports the seed capability gap, not a claim that every native platform works. Remaining gap: Implementing seed support requires sandbox-preserving marshaling/registration review; native execution is an alternate lane, not a root fix. Correct stale research C anchor, which now lands on Windows fallback.
- Review corrections: queue validity: uncertain -> valid; queue inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction. Research runtime_process.c:1176 now names Windows fallback; Linux implementation is :2134.

## rt_call_site_ratchet_regression_2026-09-05 — `rt_*` call-site ratchet regression in two stdlib domain trees

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rt_call_site_ratchet_regression_2026-09-05.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/plan_acceptance/perf_checklists_spec.spl:107; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/plan_acceptance/perf_checklists_spec.spl:174
```
- Review rationale: Full report's oracle counts rt_ substrings rather than parsed calls and silently skips absent rows. Current spec still gates 7974/358 only when path exists. Exact-target static search finds 10371/377 matching lines under those two trees, including comments/declarations; it supports investigating growth but is not an exact oracle replay or attribution of unauthorized calls. Remaining gap: Need owner-aware delta and original-baseline provenance; preserve baseline and diagnose scope rather than mechanically raising counts.
- Review corrections: queue validity: valid -> uncertain; research validity: valid -> uncertain; queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## rt_dual_ratchet_scan_scope_omits_native_all_2026-09-06 — `check-rt-dual-implementation-ratchet.shs` does not scan `src/compiler_rust/native_all`

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rt_dual_ratchet_scan_scope_omits_native_all_2026-09-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-rt-dual-implementation-ratchet.shs:183; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/native_all/src/mem_snapshot_provider.rs:194; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/native_all/src/lib.rs:19
```
- Review rationale: Report distinguishes runtime population policy from adding every driver hook. Current extractor still scans only runtime/src; actual no_mangle rt_phase_profile_record remains in native_all, encodes run identity/time/message and appends it, with lib.rs reexport. Thus it remains outside the Rust scan despite being a live provider. Existing C extractor fixes do not resolve this scope contract. Remaining gap: Choose reviewed out-of-scope category or widen with per-symbol admissions; stale 363 anchor corrected to 194. No blind baseline regeneration.
- Review corrections: research solution: known -> unknown; queue inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction. Provider anchor moved from :363 to :194; current body inspected, not inferred from old line.

## rt_enum_discriminant_returns_garbage_constant_native_lane_2026-08-17 — Native lane: `rt_enum_discriminant` returns the constant 1337030607 for every receiver shape

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rt_enum_discriminant_returns_garbage_constant_native_lane_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/objects.rs:396; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:4421
```
- Review rationale: Full report retracts small-ordinal assumption and concedes three probes may all be NamedVar. Runtime discriminant returns the stored enum field or -1 for non-enum, not an ordinal-validity check. Current lowering no longer uses the negative-discriminant guard: owner-name and conservative unique-static fallback drive recovery. That repairs one caller hazard without proving the alleged every-variant constant. Remaining gap: Need two provably distinct receiver variants plus emitted call/value inspection; do not classify original report invalid or assume runtime corruption.
- Review corrections: queue validity: valid -> uncertain; research validity: valid -> uncertain; queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## rt_file_read_bytes_declared_with_six_return_types_2026-08-09 — rt_file_read_bytes extern is redeclared repo-wide with four mutually incompatible return types

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rt_file_read_bytes_declared_with_six_return_types_2026-08-09.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:17018; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/sfm/container.spl:15; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/telnet_serial_bridge.spl:31; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/extern/rt_file_read_bytes_single_extern_signature_spec.spl:72
```
- Review rationale: Report's authoritative C provider still builds byte-width storage via rt_byte_array_new_len and returns zero on failure. Current SFM container and telnet retain [i64]? declarations; SFM indexes raw i64 values then masks/casts to bytes. file_ops has since moved to external_file ownership, so its old declaration is stale. A complete fix must coordinate representation and caller contracts across owners. Remaining gap: Need full surviving declaration/caller set and Optional behavior across engines; no declaration-only convergence or current guard PASS claimed.
- Review corrections: queue structural_change: unknown -> yes; research structural_change: unknown -> yes; queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## rt_gate_never_existed_on_origin_hook_requires_it_2026-08-18 — The rt_ gate has never existed on origin/main, yet the push hook requires it

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rt_gate_never_existed_on_origin_hook_requires_it_2026-08-18.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-no-direct-rt.shs:7; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/no_direct_rt_allowlist.txt:1; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/no_direct_rt_baseline.txt:1; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-push-must-pass.shs:867
```
- Review rationale: Full report requested committing the absent guard, allowlist and baseline together. All are tracked at the target; the guard supports revision-bound scanning and push dispatcher passes pushed ref plus base while preserving src scope. Baseline is currently 6290, not the historical local 12668. This supplies the missing clean-checkout inputs and invocation. Remaining gap: Clean-clone hook execution remains untested; historical absence is not invalidated by restoration, and current counts are not a gate PASS.
- Review corrections: queue solution: unknown -> known; queue structural_change: unknown -> no; queue inspection_level: report_reviewed -> source_reviewed; queue recommended_action: keep_open -> fixed_pending_verification; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## rt_heap_ref_wellformed_lost_in_stale_snapshot_clobber_2026-08-31 — `rt_heap_ref_wellformed` was landed, then lost to the 08-26 stale-snapshot clobber — docs survived, code did not

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rt_heap_ref_wellformed_lost_in_stale_snapshot_clobber_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:11355; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_hir_pipeline_lowering.spl:1042; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_hir_pipeline_lowering.spl:1719; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/runtime/heap_ref_wellformed_probe_spec.spl:36
```
- Review rationale: Full report concerns removed formation hardening, explicitly not the underlying zero-payload cause. Current C probe masks tag bits and rejects zero-page addresses without claiming liveness; both streaming and retained HIR entry callers invoke it before dereferencing. Current regression source asserts provider registration and zero-page/valid-pointer cases. -S history shows restoration through target ancestor 88aac2ffe28 after 4edef8fab8e removal. Remaining gap: Actual Stage2 no-crash qualification is absent; old hir_entry_payload_formation_guard_spec path is missing and must not be cited as a current test. Do not restore whole historical files.
- Review corrections: queue solution: unknown -> known; research solution: unknown -> known; queue structural_change: unknown -> no; research structural_change: unknown -> no; queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; queue recommended_action: keep_open -> fixed_pending_verification; research recommended_action: keep_open -> fixed_pending_verification; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## rt_io_file_family_interpreter_fixed_native_still_stubbed_2026-08-05 — `rt_io_file_*`: interpreter gap fixed this session; native/JIT still returns the RT_KEEP stub pending a runtime redeploy

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rt_io_file_family_interpreter_fixed_native_still_stubbed_2026-08-05.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/instr/calls.rs:3219; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:2348; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/sffi/file_io/io_file.rs:93
```
- Review rationale: Read later report correction: real symbols already existed in deployed archive while JIT still made zero target-path syscalls; RT_KEEP was an allowlist, not a stub factory. Current codegen explicitly expands path arguments for open/exists/delete and declares ptr/len/mode ABI, addressing a later documented representation cause. Provider also carries newer two-argument open twins for a separate mixed-argument mispass. This evidence contradicts a simple stale-archive remedy but does not qualify the whole family. Remaining gap: Need actual JIT resolver/call lowering and original FileHandle disk-roundtrip on an identified producer; inspect open twins registration separately. Correct research assertion that archive staleness explains the surviving JIT failure.
- Review corrections: queue validity: valid -> uncertain; research validity: valid -> uncertain; queue inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction. Archive-staleness explanation is contradicted by the full 2026-08-08 report correction; RT_KEEP is not a stub factory.

## rt_str_hash_rust_seed_djb2_divergence_2026-09-01 — Rust seed's `rt_str_hash`/`rt_hash_text` is djb2, not FNV-1a — third lane divergence

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rt_str_hash_rust_seed_djb2_divergence_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/collections.rs:6229; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:11964; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/simple_core/core_string.spl:1244
```
- Review rationale: Full report's djb2 provider has changed: Rust hashes bytes using FNV-1a basis 14695981039346656037 and prime 1099511628211, and rt_str_hash delegates to it. Current hosted C and pure-Simple providers use the same bytewise xor/multiply algorithm and signed-equivalent basis. The targeted algorithm mismatch is repaired in source; inventory d805 and target owner bytes are equal. Remaining gap: Cross-lane known-answer/runtime verification and persisted cache compatibility are untested; no broad assertion that persisted consumers are harmless. Target -S history reaches 88aac2ffe28.
- Review corrections: queue validity: uncertain -> valid; queue solution: unknown -> known; queue structural_change: unknown -> no; queue inspection_level: report_reviewed -> source_reviewed; queue recommended_action: keep_open -> fixed_pending_verification; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## rt_time_now_nanos_has_two_different_epochs_2026-08-09 — `rt_time_now_nanos` has two different epochs in two implementations

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rt_time_now_nanos_has_two_different_epochs_2026-08-09.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rt_time_now_nanos_interpreter_uses_wall_clock_epoch_2026-08-09.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/time.rs:344; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_time.c:91
```
- Review rationale: Read duplicate and complete primary correction. Interpreter now uses shared OnceLock Instant.elapsed, removing Unix-wall-clock behavior. Current POSIX C implementation returns raw CLOCK_MONOTONIC seconds/nanos without subtracting the first call. Both are monotonic but their epochs still differ; the primary's FIXED label and matching-clock comment are not proof of cross-engine absolute equality. Remaining gap: Clarify duration-only versus absolute epoch contract and test permitted cross-lane comparisons. Duplicate status is not invalidity; do not inherit the primary closure without resolving baseline mismatch.
- Review corrections: research validity: valid -> uncertain; queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction. Duplicate/primary FIXED bookkeeping is not adopted: first-call Instant epoch and raw CLOCK_MONOTONIC epoch differ.

## rt_vulkan_single_lane_symbols_block_all_pushes_2026-09-05 — Four new single-lane `rt_vulkan_*` symbols block every push

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rt_vulkan_single_lane_symbols_block_all_pushes_2026-09-05.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:425; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:10298; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/rt_dual_implementation_baseline.txt:23
```
- Review rationale: Report calls all four missing rows Vulkan but names only copy_u32_slots/readback_u32_checksum. Target baseline history identifies actual four as phase_profile_record, to_int_dynamic and those two Vulkan symbols. Current C copy validates lengths/representation and copies slots; checksum has a documented weak unavailable -1 fallback. These are real later changes, not proof of live GPU equivalence or the entire gate result. Remaining gap: Reconcile the four exact rows and admitted link profiles. Distinguish source census parity from featured Vulkan behavior; do not refresh baseline to force admission.
- Review corrections: queue validity: valid -> uncertain; research validity: valid -> uncertain; queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## rtl_mdsoc_phase5_modules_never_created_2026-08-04 — vhdl_emit_{fp,simd,cache,hart}_stub.spl were never created; 68 rtl-mdsoc system examples red

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rtl_mdsoc_phase5_modules_never_created_2026-08-04.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/compiler/rtl_mdsoc_plugin_stubs_spec.spl:81; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/compiler/rtl_mdsoc_capsule_boundary_spec.spl:121; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/vhdl/mod.spl:5; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/hardware/fpga_linux/fpga_linux_data.spl:80
```
- Review rationale: Read report and current acceptance predicates. VHDL ownership now forwards into plugins.backend_vhdl; specs likewise expect four plug-in stub files there. Exact-target reads find all four absent, while module exports expose concrete builders/templates instead. FPGA split is now present, so the historical aggregate 68-red claim cannot be carried forward unchanged. Stub marker/TODO predicates do not establish hardware functionality. Remaining gap: Owner must reconcile remaining SA-4 acceptance contract with migrated backend and functional artifacts; no current 68-example result or generic implement-feature root solution claimed.
- Review corrections: research structural_change: yes -> unknown; queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## rtl_mdsoc_reorg_fpga_linux_split_never_executed_2026-08-04 — fpga_linux split never executed: orchestrator/data/manifest modules absent, 94 examples red per tree

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rtl_mdsoc_reorg_fpga_linux_split_never_executed_2026-08-04.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/hardware/fpga_linux/riscv_fpga_linux.spl:1; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/hardware/fpga_linux/fpga_linux_orchestrator.spl:157; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/hardware/fpga_linux/fpga_linux_data.spl:80; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/hardware/fpga_linux/fpga_linux_manifest.spl:469; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/compiler/fpga_linux_split_spec.spl:5
```
- Review rationale: The named SA-3 split now exists: 13-line facade reexports orchestrator/data/manifest; orchestrator calls data write_rtl_sources and manifest serialization, and spec paths now target src/lib. This is implementation ownership, not mere marker presence. Manifest explicitly emits contract-not-ready provenance, and the broader report also tracks missing SA-4 and behavioral evidence. No blanket 94-example closure follows. Remaining gap: Qualify API preservation, capsule budgets and full acceptance matrix; preserve explicit non-product RTL status. Inventory and target facade are identical, so low research missed already-present split.
- Review corrections: research structural_change: yes -> unknown; queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction. Previous missing-capsules claim is stale: exact-target facade and three real owners already exist.

## run_path_extern_text_corruption_causes_false_gpu_skip_2026-08-20 — `bin/simple run` corrupts extern-returned `text`, turning a working 3-device Vulkan host into a silent `skip:` that specs record as a PASS

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/run_path_extern_text_corruption_causes_false_gpu_skip_2026-08-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu_lane/vulkan_lane_session.spl:116; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl:1064; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/instr/calls.rs:3064; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/02_integration/gpu_lane/vulkan_lane_session_spec.spl:71; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu_lane/lane_probe_verdict.spl:106
```
- Review rationale: Report proves historical cross-function text corruption separately from capability reporting. Current facade still returns rt_vulkan_device_type and probe compares text; codegen classifies that extern as C-string-returning, but table membership alone does not prove boxing/call ownership. Spec now emits an explicit skipped marker and requires host-aware verdict skip; helper returns fail when independent host evidence says a device exists. This is substantive reporting mitigation, not ABI qualification. Remaining gap: Need emitted return boxing and original inline/parameter/concat controls on identified Vulkan producer; host heuristics and current skipped accounting remain unexecuted.
- Review corrections: queue validity: valid -> uncertain; queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## runner_callback_field_owner_2026_10_11 — Callback field dispatch and indirect return owner loss

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/runner_callback_field_owner_2026_10_11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/io/env_access_host.spl:60; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/function_field_call.spl:30; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:5293; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/fixtures/compiler/callback_field_explicit_call/main.spl:54
```
- Review rationale: Full report distinguishes narrow ARM fixture from failing actual C36 consumers. Current env host still uses original adapter.field() syntax and reads returned record fields. Current MIR method fallback now resolves declared layout, calls try_lower_function_field_call, validates signature ownership, captures callable before args, emits indirect call and remembers return HIR/record owner. This is a plausible integrated repair beyond fixture workarounds; fixture still uses explicit forms and owner wrappers. Remaining gap: Need admitted producer testing original dot calls and aggregate returns in actual env/process consumers. Current owner bytes equal inventory; no runtime extension of old ARM PASS or RV object-only evidence.
- Review corrections: queue validity: valid -> uncertain; queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## runner_inprocess_spec_lexing_has_no_fault_boundary_2026-09-13 — The test runner lexes spec sources in its OWN process, with no fault boundary

- Source receipt: `adjudication_v2_18`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/runner_inprocess_spec_lexing_has_no_fault_boundary_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:171; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:616; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:949
```
- Review rationale: Full report's isolation concern survives: normal interpreter route sets parent execution mode and preprocesses before launching; native route also invokes preprocess_spipe_file before compilation, which calls simple_code_lines/string_continuation in-process. Fork path exists separately, so it does not establish universal isolation. A process abort in this parent-owned phase remains outside child result handling. Remaining gap: Moving all preprocessing behind a child boundary requires ownership/protocol changes and complete discovered-versus-reported accounting; precise integration remedy remains unreviewed. No crashing fixture executed.
- Review corrections: queue validity: uncertain -> valid; research solution: known -> unknown; queue structural_change: unknown -> yes; queue inspection_level: report_reviewed -> source_reviewed; research inspection_level: report_reviewed -> source_reviewed; independently supported by the report/current-owner analysis in rationale; historical execution is not current reproduction.

## runtime_byte_text_utf8_invariant_2026_10_12 — Byte-to-text decoder constructs invalid UTF-8 RuntimeString

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/runtime_byte_text_utf8_invariant_2026_10_12.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs:2111-2155,3264-3334
```
- Review rationale: The complete report and rt_bytes_to_text show both successful representations normalized with String::from_utf8_lossy after genuine receiver validation; adjacent tests build real packed/boxed arrays and validate UTF-8 safely before string operations. This is a bounded repair of the historical invariant violation, not a claim about arbitrary raw constructors. Remaining gap: Run the named Rust unit tests and matching native archive/ABI qualification; source presence is not execution.
- Review corrections: Frozen queue solution: unknown -> known. Frozen queue structural_change: unknown -> no. Frozen queue inspection_level: report_reviewed -> source_reviewed. Frozen queue recommended_action: keep_open -> fixed_pending_verification. Reasons and current-source limits: The complete report and rt_bytes_to_text show both successful representations normalized with String::from_utf8_lossy after genuine receiver validation; adjacent tests build real packed/boxed arrays and validate UTF-8 safely before string operations. This is a bounded repair of the historical invariant violation, not a claim about arbitrary raw constructors.

## runtime_from_int_still_truncates_61bit_2026-08-17 — `RuntimeValue::from_int` still truncates to 61 bits at HEAD — the fix landed, was reverted, and only its readers and specs came back

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/runtime_from_int_still_truncates_61bit_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/core.rs:237-332; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/llvm/emitter.rs:2009-2036; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/mir_interpreter.rs:772-785; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/cranelift_emitter.rs:755
```
- Review rationale: The latest report explicitly leaves LLVM and MIR open. Current from_int_scoped allocates HeapInt outside the 61-bit range and as_int reads it; Cranelift delegates to rt_value_int, but LLVM emit_box_int still emits a left shift by three and MIR emit_box_int/unbox_int still shift directly. Therefore the runtime repair is not whole-record closure; wide-box allocation failure also retains lossy fallback. Remaining gap: End-to-end per-engine wide roundtrips, complete LLVM producer audit and MIR representation remedy remain unqualified.
- Review corrections: Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal validity: uncertain -> valid. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: The latest report explicitly leaves LLVM and MIR open. Current from_int_scoped allocates HeapInt outside the 61-bit range and as_int reads it; Cranelift delegates to rt_value_int, but LLVM emit_box_int still emits a left shift by three and MIR emit_box_int/unbox_int still shift directly. Therefore the runtime repair is not whole-record closure; wide-box allocation failure also retains lossy fallback.

## rust_authority_fingerprint_overprunes_tracked_target_directories_2026-08-15 — Rust authority fingerprint over-prunes tracked `target` directories

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fix_candidate`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rust_authority_fingerprint_overprunes_tracked_target_directories_2026-08-15.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/lib/bootstrap-stage3/authority.shs:6178-6204; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/lib/bootstrap-stage3/manifest-write.shs:246; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/lib/bootstrap-stage3/manifest-verify.shs:1643
```
- Review rationale: Fingerprint collection still prunes every directory named target before hashing compiler paths. Manifest writing and verification call this owner, so a nested tracked target directory remains omitted. Anchoring generated-output pruning to the canonical Cargo output root fixes the specific mistaken predicate within existing fingerprint contracts. Remaining gap: Nested tracked-target mutation and canonical generated-target exclusion need a discriminating sentinel fixture; no fingerprint execution performed.
- Review corrections: Frozen queue solution: unknown -> known. Frozen queue structural_change: unknown -> no. Frozen queue inspection_level: report_reviewed -> source_reviewed. Frozen queue recommended_action: keep_open -> fix_candidate. Reasons and current-source limits: Fingerprint collection still prunes every directory named target before hashing compiler paths. Manifest writing and verification call this owner, so a nested tracked target directory remains omitted. Anchoring generated-output pruning to the canonical Cargo output root fixes the specific mistaken predicate within existing fingerprint contracts.

## rust_memory_provider_rustfmt_drift_blocks_scoped_sffi_lint_2026-08-26 — Rust memory provider formatting drift blocks scoped SFFI lint

- Source receipt: `adjudication_v2_19`; inspection `report_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rust_memory_provider_rustfmt_drift_blocks_scoped_sffi_lint_2026-08-26.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/memory.rs:1660-1695
```
- Review rationale: The complete report concerns historical whole-file rustfmt drift and explicitly separates it from MMIO semantics. Current shared memory provider contains checked address conversion and volatile read/write functions; its history continues to add unrelated allocation/registry owners. These facts do not determine today's formatter result or establish that the requested mechanical change is still needed. Remaining gap: An authorized exact rustfmt check and formatting-only diff review are required; neither was executed.
- Review corrections: Frozen queue validity: valid -> uncertain. Lower V2 proposal validity: valid -> uncertain. Lower V2 proposal solution: known -> unknown. Lower V2 proposal structural_change: no -> unknown. Lower V2 proposal recommended_action: fix_candidate -> keep_open. Reasons and current-source limits: The complete report concerns historical whole-file rustfmt drift and explicitly separates it from MMIO semantics. Current shared memory provider contains checked address conversion and volatile read/write functions; its history continues to add unrelated allocation/registry owners. These facts do not determine today's formatter result or establish that the requested mechanical change is still needed.

## rust_mmio_unit_test_blocked_by_runtime_export_drift_2026-08-26 — Rust MMIO unit test blocked by unrelated runtime export drift

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rust_mmio_unit_test_blocked_by_runtime_export_drift_2026-08-26.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/sffi/sync.rs:88; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/mod.rs:332,943-970; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/net_udp.rs:615-626; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/memory.rs:1660-1695
```
- Review rationale: The full report records a compiler-test build failure before MMIO execution. Current spin-loop implementation/export and UDP bind implementation/value reexports exist; TLS reexports are gated by runtime-tls. This materially weakens a blanket present-day missing-export claim, but does not establish the entire original four-error feature combination builds. MMIO address checking remains distinct from this prerequisite. Remaining gap: Recover original complete E0432 diagnostic and feature set, reconcile all TLS families, then execute the exact named MMIO unit test without disabling features.
- Review corrections: Frozen queue validity: valid -> uncertain. Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: The full report records a compiler-test build failure before MMIO execution. Current spin-loop implementation/export and UDP bind implementation/value reexports exist; TLS reexports are gated by runtime-tls. This materially weakens a blanket present-day missing-export claim, but does not establish the entire original four-error feature combination builds. MMIO address checking remains distinct from this prerequisite.

## rust_seed_parser_behind_main_grammar_blocks_simple_test_2026-09-05 — The Rust seed's parser is behind main's grammar, so `simple test` cannot run on this host

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rust_seed_parser_behind_main_grammar_blocks_simple_test_2026-09-05.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/parser_impl/attributes.rs:14-34,290-305; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/parser_impl/core.rs:1126-1193
```
- Review rationale: Read both original grammar failures and later correction that per-spec run also failed. Current parser explicitly recognizes always_inline as metadata and consumes known attributes through is_at_known_attribute; condition blocks reconcile multiline continuation dedents. These are relevant changed capabilities, but do not prove every reported inline assignment/unsafe attribute case works or that a full Stage4 CLI is deployed on the original host. Remaining gap: Source-bound Stage4 deployment receipt and original grammar/attribute fixtures on the named host remain missing; no stdlib workaround or seed admission proposed.
- Review corrections: Frozen queue validity: valid -> uncertain. Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: Read both original grammar failures and later correction that per-spec run also failed. Current parser explicitly recognizes always_inline as metadata and consumes known attributes through is_at_known_attribute; condition blocks reconcile multiline continuation dedents. These are relevant changed capabilities, but do not prove every reported inline assignment/unsafe attribute case works or that a full Stage4 CLI is deployed on the original host.

## rust_seed_run_help_treated_as_source_filename_2026-09-09 — Rust seed run --help is treated as a source filename instead of subcommand help

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rust_seed_run_help_treated_as_source_filename_2026-09-09.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/main.rs:470-477,1104-1108,1350-1359
```
- Review rationale: Historical Linux/Windows source-open failure is concrete. Current handle_run_wrapper now intercepts exactly run --help/-h and returns zero before handle_run; COMMAND_TABLE selects that Rust handler. Table dispatch also has a pure-Simple app path, so this source repair alone is not proof of all active dispatch/deployment routes. Remaining gap: Inspect complete dispatch selection and the introducing diff, then verify help output/zero exit/no source open on a pinned seed binary. Conservative whole-record solution remains unknown.
- Review corrections: Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal validity: uncertain -> valid. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: Historical Linux/Windows source-open failure is concrete. Current handle_run_wrapper now intercepts exactly run --help/-h and returns zero before handle_run; COMMAND_TABLE selects that Rust handler. Table dispatch also has a pure-Simple app path, so this source repair alone is not proof of all active dispatch/deployment routes.

## rv32_exec_core_no_external_debug_ports_2026-07-22 — rv32_exec_core lacks a halt port and SBA-into-fetch for external JTAG hart debug

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rv32_exec_core_no_external_debug_ports_2026-07-22.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/fpga_riscv/rtl/rv32_exec_core.vhd:12-34,89-94; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/hardware/debug/hart_core_glue.vhd:149-170,250-262
```
- Review rationale: Core port declaration has only clock/reset, observation outputs and additive readback selection; no halt or external instruction write input. Wrapper really gates clk via falling-edge latched core_run and instantiates the core with that clock; register bridge returns full readback but cannot write the register file. The report's closed readback gap is distinct from the open shared fetch/SBA ownership contract. Remaining gap: A coherent external instruction-write/fetch interface and halt integration require design and hardware qualification; wrapper simulation evidence does not prove loaded-program execution.
- Review corrections: Frozen queue structural_change: unknown -> yes. Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal solution: known -> unknown. Reasons and current-source limits: Core port declaration has only clock/reset, observation outputs and additive readback selection; no halt or external instruction write input. Wrapper really gates clk via falling-edge latched core_run and instantiates the core with that clock; register bridge returns full readback but cannot write the register file. The report's closed readback gap is distinct from the open shared fetch/SBA ownership contract.

## rv64_compliance_spec_missing_core_ext_pkg_modules_2026-07-20 — rv64_compliance_spec imports hardware.rv64gc.core.rv64_execute, which does not exist

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rv64_compliance_spec_missing_core_ext_pkg_modules_2026-07-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/02_integration/hardware/rv64gc/rv64_compliance_spec.spl:18-85; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/hardware/rv64gc/mod.spl:1; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/hardware/rv64gc/top/rv64_machine.spl:1-30
```
- Review rationale: The current compliance spec still calls ALU/muldiv/atomic APIs through the reported core/ext/pkg imports. Current rv64gc module exports only top; its complete Rv64Machine implementation is a platform/handoff record with no execution API. A generic import rename to that owner cannot satisfy the actual assertions. Remaining gap: Choose and substantiate intended RV64 model contract versus spec migration; no implementation-level remedy or execution proven.
- Review corrections: Frozen queue inspection_level: report_reviewed -> source_reviewed. Reasons and current-source limits: The current compliance spec still calls ALU/muldiv/atomic APIs through the reported core/ext/pkg imports. Current rv64gc module exports only top; its complete Rv64Machine implementation is a platform/handoff record with no execution API. A generic import rename to that owner cannot satisfy the actual assertions.

## rv64_ed25519_alpha_pure_sha512_timeout_2026-06-12 — RV64 SSH alpha: pure-Simple Ed25519 signature does not match the runtime/C backend

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rv64_ed25519_alpha_pure_sha512_timeout_2026-06-12.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/ssh_session_kex.spl:640-666; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rv64_ed25519_alpha_pure_sha512_timeout_2026-06-12.md:176-219,521-635
```
- Review rationale: Full report progression includes focused Ed25519 success, subsequent X25519 fixes, then June 14 live SHA512/Ed25519 mismatch and September unresolved qualification. Current SSH caller passes identical copied seed/public/hash to runtime and pure signing and disconnects on unequal output. Thus the protection is real and original timeout closure cannot close the later signature mismatch. Remaining gap: Pinned live RV64 signature/hash bytes and exact native lowering diagnosis remain missing. Do not bypass alpha comparison.
- Review corrections: Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal validity: uncertain -> valid. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: Full report progression includes focused Ed25519 success, subsequent X25519 fixes, then June 14 live SHA512/Ed25519 mismatch and September unresolved qualification. Current SSH caller passes identical copied seed/public/hash to runtime and pure signing and disconnects on unequal output. Thus the protection is real and original timeout closure cannot close the later signature mismatch.

## rv64_memory_ops_spec_missing_rv64ram_2026-07-20 — rv64_memory_ops_spec imports hardware.rv64gc.mem.rv64_ram.Rv64Ram, never implemented

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rv64_memory_ops_spec_missing_rv64ram_2026-07-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/hardware/rv64gc/rv64_memory_ops_spec.spl:51-110; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/hardware/rv64gc_rtl/lsu.spl:22-75; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/hardware/rv64gc/top/rv64_machine.spl:1-30
```
- Review rationale: The relocated test still requires Rv64Ram.create/read/write with little-endian and neighbor-preservation assertions. The current nearby LSU computes store signal records and sign/zero-extends supplied read data; it neither owns byte-addressable storage nor implements this object API. Scoped owner/export search does not reveal the required RAM class. Remaining gap: Architecture decision and actual RAM owner or deliberate equivalent spec migration remain required, not a mechanical import rewrite.
- Review corrections: Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal validity: uncertain -> valid. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: The relocated test still requires Rv64Ram.create/read/write with little-endian and neighbor-preservation assertions. The current nearby LSU computes store signal records and sign/zero-extends supplied read data; it neither owns byte-addressable storage nor implements this object API. Scoped owner/export search does not reveal the required RAM class.

## rv64_smoke_tb_dangling_soc_top_rv64_entity_2026-07-21 — rv64 smoke testbench instantiates dangling entity `soc_top_rv64`

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rv64_smoke_tb_dangling_soc_top_rv64_entity_2026-07-21.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/fpga_riscv/rtl/tb_rv64_wb_soc_smoke.vhd:22-37; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/fpga_riscv/rtl/soc_top_rv64.vhd:19-34
```
- Review rationale: Historical missing-entity premise is no longer literally current: soc_top_rv64 now exists. However the smoke testbench still maps clk/rst while that board entity exposes only uart_tx/uart_rx and explicitly requires vendor primitives; comments direct simulation to soc_top_rv64_sim. A same-name entity therefore does not repair this artifact-set contract. Remaining gap: Review generator/provenance artifact set and intended simulation wrapper before selecting a remedy; actual elaboration not run.
- Review corrections: Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal validity: uncertain -> valid. Reasons and current-source limits: Historical missing-entity premise is no longer literally current: soc_top_rv64 now exists. However the smoke testbench still maps clk/rst while that board entity exposes only uart_tx/uart_rx and explicitly requires vendor primitives; comments direct simulation to soc_top_rv64_sim. A same-name entity therefore does not repair this artifact-set contract.

## rv64_web_gate_arm64_import_leak_and_storage_2026-06-15 — RV64 HTTP+NVFS gate gets zero GET-200: arm64 import leaks into the link, storage unavailab

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rv64_web_gate_arm64_import_leak_and_storage_2026-06-15.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/arch_adapt/arm64_sandbox_paging.spl:9; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/arch/arm64/sandbox_pte_bits.spl:13; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/security/sandbox_boot_apply.spl:133-148; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/qemu/qemu_rv64_http_test.shs:96-117
```
- Review rationale: Read all report corrections: ARM import split, subsequent runtime/storage link failures, stale-prebuilt uncertainty and later LLVM-only gate claim. Current arch adapter imports CPU-free sandbox_pte_bits, while raw-section reader still calls rt_bytes_from_raw/rt_bytes_to_text. The current gate accepts llvm OR cranelift and rejects seed provenance, so its old foundational LLVM-only description is stale. These partial changes do not settle HTTP/NVFS readiness. Remaining gap: Current-source RV64 closure and complete storage-provider symbol/link audit plus actual GET-200/NVFS receipt remain needed.
- Review corrections: Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: Read all report corrections: ARM import split, subsequent runtime/storage link failures, stale-prebuilt uncertainty and later LLVM-only gate claim. Current arch adapter imports CPU-free sandbox_pte_bits, while raw-section reader still calls rt_bytes_from_raw/rt_bytes_to_text. The current gate accepts llvm OR cranelift and rejects seed provenance, so its old foundational LLVM-only description is stale. These partial changes do not settle HTTP/NVFS readiness.

## rv64_wm_inline_asm_blocks_arch_mixed_and_operands_unsubstituted_2026-09-01 — riscv64 WM closure: `simple_asm_blocks.c` mixes x86 asm in and drops operand names

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rv64_wm_inline_asm_blocks_arch_mixed_and_operands_unsubstituted_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/stmt_parsing/asm.rs:457-490; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/inline_asm_emit.rs:120-157; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rv64_wm_inline_asm_blocks_arch_mixed_and_operands_unsubstituted_2026-09-01.md:114-184
```
- Review rationale: The report explicitly resolves assembler errors but leaves block-form operand constraints as a separate defect. Current parser preserves placeholder braces and emitter rejects known foreign architecture blocks while detecting unresolved braces/$N for omission. That supports a partial source remedy for malformed assembly, not working operand execution or a proven whole WM build. Remaining gap: Trace emission call site and exact regression diff/tests before accepting fixed-pending for original assembler scope; current assembler execution remains untested.
- Review corrections: Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal solution: known -> unknown. Lower V2 proposal structural_change: no -> unknown. Lower V2 proposal recommended_action: fixed_pending_verification -> keep_open. Reasons and current-source limits: The report explicitly resolves assembler errors but leaves block-form operand constraints as a separate defect. Current parser preserves placeholder braces and emitter rejects known foreign architecture blocks while detecting unresolved braces/$N for omission. That supports a partial source remedy for malformed assembly, not working operand execution or a proven whole WM build.

## rv64gc_core64_step_removed_dangling_export_2026-07-21 — core64_step is defined nowhere in rv64gc_rtl yet spec files still import and call it

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/rv64gc_core64_step_removed_dangling_export_2026-07-21.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/hardware/rv64gc_rtl/core.spl:771-806; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl:44,431-450
```
- Review rationale: Report's unresolved core64_step callers still exist, but a real core64_step implementation now exists: it expands the bus instruction, invokes combinational datapath, commits PC/RVFI and conditional register writeback. The integration test imports it directly and calls it, contradicting stale test comments that it is undefined. Presence is relevant repair evidence, but its direct-step no-trap contract differs from the protected clocked pipeline. Remaining gap: Review complete shim-introducing diff, legacy bus semantics and direct-call regressions before whole-record fixed classification.
- Review corrections: Frozen queue inspection_level: report_reviewed -> source_reviewed. Direct core-module import is distinct from package reexport; stale missing-function comments do not prove this present body is unreachable. Reasons and current-source limits: Report's unresolved core64_step callers still exist, but a real core64_step implementation now exists: it expands the bus instruction, invokes combinational datapath, commits PC/RVFI and conditional register writeback. The integration test imports it directly and calls it, contradicting stale test comments that it is undefined. Presence is relevant repair evidence, but its direct-step no-trap contract differs from the protected clocked pipeline.

## s68_cranelift_interpcall_boxed_result_generic_return_gap_2026-07-18 — Seed cranelift InterpCall returns wrong Object/Enum(Option) values in composite returns

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/s68_cranelift_interpcall_boxed_result_generic_return_gap_2026-07-18.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/compilability.rs:204-223; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/instr/core.rs:945-984
```
- Review rationale: The current InterpCall emitter still branches on boxed_result/name/scalar type, but return_type_keeps_boxed now includes arrays and generic Option/Result, contrary to the report's old blanket future-extension claim. Current comments describe marshaling arrays into real runtime arrays, so the proposed universal handle-unwrapping remedy would be unsafe to assume. Dict/user-struct behavior still needs a specific bridge trace. Remaining gap: Trace runtime_bridge marshaling and a concrete nonliteral fallback producer/consumer for Dict/Object/Enum; pinned backend fixture required.
- Review corrections: Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: The current InterpCall emitter still branches on boxed_result/name/scalar type, but return_type_keeps_boxed now includes arrays and generic Option/Result, contrary to the report's old blanket future-extension claim. Current comments describe marshaling arrays into real runtime arrays, so the proposed universal handle-unwrapping remedy would be unsafe to assume. Dict/user-struct behavior still needs a specific bridge trace.

## safety_checker_case_some_never_matches_checks_skipped_2026-08-31 — Safety checker's `case Some` arms never match — E1047 and transfer checks are silently skipped

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/safety_checker_case_some_never_matches_checks_skipped_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/35.semantics/safety_checker.spl:174-218; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/35.semantics/safety_checker_expr.spl:186,203
```
- Review rationale: The present parameter lookup returns the bare SafetyParamTrack or nil, and both binding/index assignment consumers match Some before appending E1047. This confirms the report's exact producer/consumer representation shape survives. Whether this target's lowering automatically accommodates nullable Some patterns needs a semantic oracle; source shape alone is insufficient to assert diagnostics never fire. Remaining gap: Inspect current nullable pattern-lowering contract and assert exact E1047/iterator/transfer diagnostics on independent fixtures before changing readers across the compiler.
- Review corrections: Frozen queue validity: valid -> uncertain. Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: The present parameter lookup returns the bare SafetyParamTrack or nil, and both binding/index assignment consumers match Some before appending E1047. This confirms the report's exact producer/consumer representation shape survives. Whether this target's lowering automatically accommodates nullable Some patterns needs a semantic oracle; source shape alone is insufficient to assert diagnostics never fire.

## sci_launcher_policy_projection_owner_api_missing_2026-08-14 — SCI launcher rejects whole images: no owner API for path-scoped caps and file associations

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sci_launcher_policy_projection_owner_api_missing_2026-08-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/services/launcher/launcher_composition.spl:75-110; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/services/launcher/launcher_registry.spl:448-454
```
- Review rationale: SCI composition validation still rejects any nonempty capability/association fields with the two exact projection diagnostics before unregistering prior entries. The registry's current association owner hard-codes editor/image-viewer extensions. Thus fail-closed refusal preserves a real missing scoped-authority and association-index contract, which requires coordinated owner/API work, not relaxing admission. Remaining gap: Versioned manifest scope propagation, atomic registry replacement and injected-failure rollback contracts/tests still need design and review.
- Review corrections: Frozen queue structural_change: unknown -> yes. Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal validity: uncertain -> valid. Lower V2 proposal structural_change: unknown -> yes. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: SCI composition validation still rejects any nonempty capability/association fields with the two exact projection diagnostics before unregistering prior entries. The registry's current association owner hard-codes editor/image-viewer extensions. Thus fail-closed refusal preserves a real missing scoped-authority and association-index contract, which requires coordinated owner/API work, not relaxing admission.

## scram_sha1_examples_exceed_interpreter_10m_op_budget_2026-08-04 — SCRAM-SHA-1 RFC 5802 spec exceeds the interpreter's 10M-operation budget once PBKDF2 runs

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/scram_sha1_examples_exceed_interpreter_10m_op_budget_2026-08-04.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_state.rs:322-333,656-673; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/cli/init.rs:159-176; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/crypto/pbkdf2.spl:1164-1175; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/crypto/scram_sha1.spl:33; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/os/crypto/scram_sha1_rfc5802_spec.spl:235-259
```
- Review rationale: Current SCRAM caller forwards iterations to pbkdf2_sha1_bytes and the RFC fixture still uses 4096; PBKDF2 loops over real HMAC block work. The interpreter counter retains a 10M value but enablement defaults differ by debug_assertions, and initialization permits explicit overrides. Historical six-example output was explicitly truncated, not a full PASS. A budget change alone does not establish current vector correctness/performance. Remaining gap: Exact build/config operation counting and complete RFC vector run required; algorithm iterations and infinite-loop protections must remain intact.
- Review corrections: Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal validity: uncertain -> valid. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: Current SCRAM caller forwards iterations to pbkdf2_sha1_bytes and the RFC fixture still uses 4096; PBKDF2 loops over real HMAC block work. The interpreter counter retains a 10M value but enablement defaults differ by debug_assertions, and initialization permits explicit overrides. Historical six-example output was explicitly truncated, not a full PASS. A budget change alone does not establish current vector correctness/performance.

## screenshot_sffi_api_declared_but_never_implemented_2026-08-04 — No rt_screenshot_* implementation exists in the C runtime, so native/baremetal links canno

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/screenshot_sffi_api_declared_but_never_implemented_2026-08-04.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/mod.rs:307-343; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/screenshot_sffi.rs:79-161; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/screenshot_sffi.rs:95-108
```
- Review rationale: Read contradictory old absence claims and August correction. Current interpreter extern table now registers screenshot control/context/capture names, and adapters call the actual Rust runtime with argument conversion and NUL rejection. Native enable/disable changes atomic state. Therefore both blanket absent-runtime and absent-registration claims are stale, but actual terminal capture, output storage and full spec behavior were not qualified. Remaining gap: Review capture implementation/registration introducing diff and all eleven behavior assertions, then execute supported engine capture tests; do not infer capture success from registration.
- Review corrections: Frozen queue validity: uncertain -> valid. Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal solution: known -> unknown. Lower V2 proposal structural_change: no -> unknown. Lower V2 proposal recommended_action: fixed_pending_verification -> keep_open. Reasons and current-source limits: Read contradictory old absence claims and August correction. Current interpreter extern table now registers screenshot control/context/capture names, and adapters call the actual Rust runtime with argument conversion and NUL rejection. Native enable/disable changes atomic state. Therefore both blanket absent-runtime and absent-registration claims are stale, but actual terminal capture, output storage and full spec behavior were not qualified.

## scripts_reorg_left_34_test_specs_on_pre_reorg_paths_2026-08-04 — The `scripts/` reorg updated product source but left 34 test specs on pre-reorg paths — and the specs that "verify the script exists" were vacuous enough not to notice (2026-08-04)

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/scripts_reorg_left_34_test_specs_on_pre_reorg_paths_2026-08-04.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/hardware/riscv64_fpga/preflight_spec.spl:35-76; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/hardware/riscv64_fpga/jtag_unbind_spec.spl:39-84
```
- Review rationale: The full report describes both stale paths and false-green assertions. Current cited FPGA preflight and JTAG tests now read relocated script paths and use real file_exists/file_read checks, so those example vacuities are repaired. This is specific source evidence, not proof that all 34 original files and genuinely stale RV64 content expectations have been reconciled. Remaining gap: Enumerate remaining mapping-table consumers across all original tiers and distinguish stale content assertions from stale paths; whole-record closure unproven.
- Review corrections: Frozen queue validity: uncertain -> valid. Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal validity: uncertain -> valid. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: The full report describes both stale paths and false-green assertions. Current cited FPGA preflight and JTAG tests now read relocated script paths and use real file_exists/file_read checks, so those example vacuities are repaired. This is specific source evidence, not proof that all 34 original files and genuinely stale RV64 content expectations have been reconciled.

## scv_chunk_publication_concurrent_reader_2026-10-05 — SCV final chunk names become visible before complete publication

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/scv_chunk_publication_concurrent_reader_2026-10-05.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/scv/compile_snapshot.spl:383-425; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_secure_staging.c:223-265; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/04_smoke/native_scv_chunk_publication.spl:46-81
```
- Review rationale: Current chunk writer exclusively claims a private stage, writes bytes, validates its digest and publishes through noreplace; losing writers validate the complete winner and clean only their stage. Runtime owner uses MoveFileEx without replacement, renameat2 no-replace or link/unlink. The ancestry diff replaces final-path create with private staging. This is a causal bounded repair of early visibility, while original syscall causality remains unproven. Remaining gap: Execute deterministic interleaving/corrupt-winner/cleanup fixture on both pinned backends and measure cold/warm latency and process-tree RSS.
- Review corrections: Frozen queue solution: unknown -> known. Frozen queue structural_change: unknown -> no. Frozen queue inspection_level: report_reviewed -> source_reviewed. Frozen queue recommended_action: keep_open -> fixed_pending_verification. Lower V2 proposal validity: uncertain -> valid. Lower V2 proposal solution: unknown -> known. Lower V2 proposal structural_change: unknown -> no. Lower V2 proposal recommended_action: keep_open -> fixed_pending_verification. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: Current chunk writer exclusively claims a private stage, writes bytes, validates its digest and publishes through noreplace; losing writers validate the complete winner and clean only their stage. Runtime owner uses MoveFileEx without replacement, renameat2 no-replace or link/unlink. The ancestry diff replaces final-path create with private staging. This is a causal bounded repair of early visibility, while original syscall causality remains unproven.

## scv_distributed_textual_db_missing_production_boundaries_2026-09-13 — SCV distributed textual DB production boundaries are missing

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/scv_distributed_textual_db_missing_production_boundaries_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/03_plan/agent_tasks/simple_distributed_textual_databases.md:8-23; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/scv/metadata_db.spl:110-151,189-197; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/scv/network_remote.spl:334-347; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/scv/db/local_apply.spl:10-16; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/scv/db/commands.spl:42-72
```
- Review rationale: Report's blanket design-only state is superseded by the selected plan's October 25 correction. Current metadata_db still has row-count next_key and single-insert copy, but now offers bounded insert_batch; app/scv/db commands decode bounded inputs and call settlement queue/paged owners, and local_apply validates reserved entity kinds before a transition. Thus old metadata/network stubs are not the whole current production design. Plan still explicitly leaves jj/SJ orchestration, migration and integrated performance/remote acceptance open. Remaining gap: Inspect joined production transition/transport/retention ownership against requirements and designated-remote two-clone evidence; no broad missing-feature or completion assertion supported.
- Review corrections: Frozen queue validity: valid -> uncertain. Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: Report's blanket design-only state is superseded by the selected plan's October 25 correction. Current metadata_db still has row-count next_key and single-insert copy, but now offers bounded insert_batch; app/scv/db commands decode bounded inputs and call settlement queue/paged owners, and local_apply validates reserved entity kinds before a transition. Thus old metadata/network stubs are not the whole current production design. Plan still explicitly leaves jj/SJ orchestration, migration and integrated performance/remote acceptance open.

## scv_gzip_compress_dominates_pack_write_2026-08-26 — `gzip_compress` dominates every SCV pack write (110s for a 16 KB payload)

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/scv_gzip_compress_dominates_pack_write_2026-08-26.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/scv/pack.spl:84-94; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/compress/gzip.spl:18-24; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/compression/gzip/lz77.spl:65-148; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/scv_gzip_compress_dominates_pack_write_2026-08-26.md:189-303
```
- Review rationale: Read complete report including completed 50-cycle soak and corrected Huffman attribution. Current SCV pack calls common gzip which calls lz77_compress; its real head/prev walk is bounded by max_search/window, inserts skipped match positions and emits greedy matches. This supports removal of the reported linear-window hot path; it does not establish current realistic pack timing, byte identity or whole-soak scaling. The reverted concat experiment must not be reintroduced as a presumed fix. Remaining gap: Review exact introducing hash-chain/Huffman diffs and regression behavior, then perform source-bound realistic pack byte-correctness/performance qualification before fixed-pending admission.
- Review corrections: Frozen queue validity: uncertain -> valid. Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal validity: uncertain -> valid. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: Read complete report including completed 50-cycle soak and corrected Huffman attribution. Current SCV pack calls common gzip which calls lz77_compress; its real head/prev walk is bounded by max_search/window, inserts skipped match positions and emits greedy matches. This supports removal of the reported linear-window hot path; it does not establish current realistic pack timing, byte identity or whole-soak scaling. The reverted concat experiment must not be reintroduced as a presumed fix.

## scv_merge_commit_parents_separator_inconsistent_2026-08-26 — SCV: merge-commit `parents:` separator inconsistent across readers (2026-08-26)

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/scv_merge_commit_parents_separator_inconsistent_2026-08-26.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/scv/store.spl:321,338-339,452-468; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/scv/maintenance.spl:276-286; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/scv/integrity_view.spl:123-140; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/scv/integrity.spl:410-426; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/scv/recover.spl:62-84
```
- Review rationale: Current commit writers space-join parents and maintenance commit reachability still comma-splits, preserving a concrete merge-parent mismatch. However three report-listed comma readers actually traverse operation objects (op_ refs), and scv_write_operation currently serializes one parent_op. They must not all be mechanically changed as commit readers. The distinction matters for legacy tolerance and recovery. Remaining gap: Specify and test commit versus operation parent codecs separately, including space-joined two-parent ancestry and historical commas before selecting whole-record correction.
- Review corrections: Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal validity: uncertain -> valid. Lower V2 unexamined placeholder replaced after independent report/source investigation. Three named comma readers process operation objects; do not apply a blanket commit-parser replacement. Reasons and current-source limits: Current commit writers space-join parents and maintenance commit reachability still comma-splits, preserving a concrete merge-parent mismatch. However three report-listed comma readers actually traverse operation objects (op_ refs), and scv_write_operation currently serializes one parent_op. They must not all be mechanically changed as commit readers. The distinction matters for legacy tolerance and recovery.

## scv_structural_merge_drops_one_side_edit_conflict_data_2026-08-27 — scv structural 3-way merge falls back to conflict-data and drops one side's edit

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/scv_structural_merge_drops_one_side_edit_conflict_data_2026-08-27.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/scv/merge.spl:239-265,454-486; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/02_integration/app/scv_structural_match_spec.spl:116-137
```
- Review rationale: Current merge still tries structural, syntax, line and region rungs then returns left_line with conflict-data. It now also writes conflict-v2 payload containing base/left/right references, so total loss of repository-side conflict evidence should not be assumed; the worktree result can still be one-sided. Original disjoint fallback fixture still asserts merged=ONE|two|THREE. Which rung fails for each original fixture is not established by source review. Remaining gap: Trace anchor matching and all three original fixtures through conflict serialization/export before proposing a root fix; preserve correct disjoint-edit oracles.
- Review corrections: Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal validity: uncertain -> valid. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: Current merge still tries structural, syntax, line and region rungs then returns left_line with conflict-data. It now also writes conflict-v2 payload containing base/left/right references, so total loss of repository-side conflict evidence should not be assumed; the worktree result can still be one-sided. Original disjoint fallback fixture still asserts merged=ONE|two|THREE. Which rung fails for each original fixture is not established by source review.

## sdoctest_use_accumulation_exceeds_5s_block_timeout_2026-08-18 — SDoctest block timeout: `use`-line accumulation makes late blocks in an import-heavy doc unrunnable

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sdoctest_use_accumulation_exceeds_5s_block_timeout_2026-08-18.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/sdoctest/extractor.spl:239-267; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/sdoctest/runner.spl:184-200; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/sdoctest/config.spl:29,49,292
```
- Review rationale: extract_reusable_lines still collects every use/import line; build_file_preambles joins all previous reusable blocks and appends the current block without deduplication or section reset. Default timeout remains 5000ms. This directly supports accumulation mechanism, but not a measured current threshold or the sufficiency of deduplication under varied host load. Remaining gap: Measure a fixed sequential import-heavy fixture with exact executing binary and complete per-block timing; preserve valid documentation and sharing semantics.
- Review corrections: Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal validity: uncertain -> valid. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: extract_reusable_lines still collects every use/import line; build_file_preambles joins all previous reusable blocks and appends the current block without deduplication or section reset. Default timeout remains 5000ms. This directly supports accumulation mechanism, but not a measured current threshold or the sufficiency of deduplication under varied host load.

## secure_memory_interpreter_raw_pointer_aliasing_2026-08-24 — Secure-memory interpreter raw-pointer aliasing

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/secure_memory_interpreter_raw_pointer_aliasing_2026-08-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/crypto/secure_memory.spl:58-99; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/memory.rs:1806-1815,1978-1985,2108-2114
```
- Review rationale: secure_zero_u8_range validates bounds, obtains rt_array_data_ptr_text then performs volatile byte writes/readback. Interpreter alias forwards to rt_array_data_ptr, which derives as_ptr from shared ByteArray/FrozenByteArray without exclusive storage or caller-place writeback; volatile write only casts the integer address. Thus address validity/barrier registration does not resolve the ownership contract or prove caller-visible wiping. Remaining gap: A caller-place-aware mutable byte operation with exclusive ownership and differential zeroization/allocation evidence remains required; escaped raw aliases are not a remedy.
- Review corrections: Frozen queue structural_change: unknown -> yes. Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal validity: uncertain -> valid. Lower V2 proposal structural_change: unknown -> yes. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: secure_zero_u8_range validates bounds, obtains rt_array_data_ptr_text then performs volatile byte writes/readback. Interpreter alias forwards to rt_array_data_ptr, which derives as_ptr from shared ByteArray/FrozenByteArray without exclusive storage or caller-place writeback; volatile write only casts the integer address. Thus address validity/barrier registration does not resolve the ownership contract or prove caller-visible wiping.

## seed_accepts_bodyless_if_native_build_rejects_2026-08-22 — Seed accepts a bodyless `if` block that native-build rejects (front-end divergence)

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_accepts_bodyless_if_native_build_rejects_2026-08-22.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/parser_impl/core.rs:1158-1185,1199-1248; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/parser_helpers.rs:202-205
```
- Review rationale: Current parser has the report's proposed allow_empty_body distinction: condition blocks pass false; shared/match inline-or-block path retains true. Only the latter can return an empty block at Dedent/Eof, and same-column statement-start flat bodies remain accepted. Thus a relevant source repair exists, contrary to 'not landed'; complete conditional/control regression coverage and parity remain unqualified. Remaining gap: Inspect introducing diff and parser tests for all conditional/match/flat-body controls, then qualify both front ends; no global no-regression claim from the historical scan.
- Review corrections: Frozen queue validity: uncertain -> valid. Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal validity: uncertain -> valid. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: Current parser has the report's proposed allow_empty_body distinction: condition blocks pass false; shared/match inline-or-block path retains true. Only the latter can return an empty block at Dedent/Eof, and same-column statement-start flat bodies remain accepted. Thus a relevant source repair exists, contrary to 'not landed'; complete conditional/control regression coverage and parity remain unqualified.

## seed_array_local_alias_cow_bypass_2026-07-17 — Seed (Rust interpreter): arrays alias on local-bind despite Arc/COW design

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_array_local_alias_cow_bypass_2026-07-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter/node_exec.rs:1535-1606; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/runner.rs:116-135; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/exec_core.rs:218-231,980-1035
```
- Review rationale: Report explicitly leaves root attribution unresolved. Current AST index mutation still guards unique Arc storage then falls back to clone plus Arc::make_mut. Driver exec_core defaults to JIT, can prefer interpreter by source, and can demote JIT failures, so bin/simple run alone does not identify the executor. This supports retaining uncertainty rather than changing COW based on an unpinned historical runner. Remaining gap: Obtain exact original/current engine receipt and trace env binding, method mutation and writeback for the alias fixtures; no root remedy inferred from already-COW-aware code.
- Review corrections: Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: Report explicitly leaves root attribution unresolved. Current AST index mutation still guards unique Arc storage then falls back to clone plus Arc::make_mut. Driver exec_core defaults to JIT, can prefer interpreter by source, and can demote JIT failures, so bin/simple run alone does not identify the executor. This supports retaining uncertainty rather than changing COW based on an unpinned historical runner.

## seed_bootstrap_compile_stage_hardcoded_180s_timeout_2026-08-18 — Seed `build bootstrap` hardcodes `--timeout 180` and a non-canonical `--source` set

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_bootstrap_compile_stage_hardcoded_180s_timeout_2026-08-18.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/cli/commands/misc_commands.rs:459-484,866-927
```
- Review rationale: compile_stage still passes literal --timeout 180 and --source src/app in both seed/self-hosted branches, and handle_bootstrap invokes it for each stage. Threads now come from bootstrap_threads and seed detection forces the in-process Rust native pipeline, so the old one-thread/interpreted-worker diagnosis is not unchanged. Raising timeout or adding roots has not been shown to complete the build. Remaining gap: Canonical bootstrap owner budget/source closure comparison and phase timing/complete admitted artifact evidence are required; no deadline weakening or seed tooling substitution proposed.
- Review corrections: Frozen queue validity: uncertain -> valid. Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal validity: uncertain -> valid. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: compile_stage still passes literal --timeout 180 and --source src/app in both seed/self-hosted branches, and handle_bootstrap invokes it for each stage. Threads now come from bootstrap_threads and seed detection forces the in-process Rust native pipeline, so the old one-thread/interpreted-worker diagnosis is not unchanged. Raising timeout or adding roots has not been shown to complete the build.

## seed_build_guard_checks_only_bin_target_no_link_2026-08-17 — `check-seed-builds-push.shs` verifies only the `--bin simple` target and never links — the Rust test suite could not build at all while every guard was green

- Source receipt: `adjudication_v2_19`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_build_guard_checks_only_bin_target_no_link_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-seed-builds-push.shs:366-397,892-912,937,972-993,999-1005
```
- Review rationale: Current guard runs gating --tests type checking and a real cargo build --release --bin simple link leg; the caller tests its exit status and exits 1 on failure. Therefore the report's 'never links' follow-up is stale, even though older comments still claim no link leg. This binary-only link does not certify every test executable's linkage, feature matrix or deployed compiler source identity. Remaining gap: Review cache identity/feature coverage and source-bound deployed-binary receipts; qualify test-executable link scope separately from --tests cargo check.
- Review corrections: Frozen queue validity: uncertain -> valid. Frozen queue inspection_level: report_reviewed -> source_reviewed. Lower V2 proposal validity: uncertain -> valid. Lower V2 unexamined placeholder replaced after independent report/source investigation. Reasons and current-source limits: Current guard runs gating --tests type checking and a real cargo build --release --bin simple link leg; the caller tests its exit status and exits 1 on failure. Therefore the report's 'never links' follow-up is stale, even though older comments still claim no link leg. This binary-only link does not certify every test executable's linkage, feature matrix or deployed compiler source identity.

## seed_build_guard_never_compiles_vulkan_feature_2026-08-20 — Seed-build guard never compiles `--features vulkan`, so cfg-gated code rots unseen

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_build_guard_never_compiles_vulkan_feature_2026-08-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-seed-builds-push.shs:288-302,655-700,916-958; target-ancestry patch a4c9d0a585c2a9e94bf9436a71ac69567e5c8844
```
- Review rationale: Historical default-feature guards missed four cfg-gated Vulkan compile errors. Current guard invokes cargo check -p simple-runtime --features vulkan and fails on nonzero status; recipe-tagged digest invalidates older admission markers. The cfg fixture contrasts default success with enabled-feature duplicate-import failure. This is a concrete local remedy; executing the guard and sabotage fixture at this revision remains required.
- Review corrections: Queue validity: uncertain -> valid, based on the independently inspected report and owner behavior. Queue solution: unknown -> known, based on the independently inspected report and owner behavior. Queue structural_change: unknown -> no, based on the independently inspected report and owner behavior. Queue recommended_action: keep_open -> fixed_pending_verification, based on the independently inspected report and owner behavior.

## seed_builds_guard_selftest_commits_into_real_repo_2026-08-19 — seed-builds guard selftest commits into the REAL repo and corrupts the index

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_builds_guard_selftest_commits_into_real_repo_2026-08-19.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-seed-builds-push.shs:192-202,560-610; target-ancestry patch 3b80a0e574b4582f84784f404e6b5fc31c392deb
```
- Review rationale: The report records real fixture commits/config and index corruption in the caller repository. Current fixture init/config/add/commit all call git_in_repo, which removes GIT_DIR, GIT_WORK_TREE, GIT_INDEX_FILE and GIT_COMMON_DIR before selecting the scratch path. This directly repairs selector leakage. The inspected fixture lacks caller HEAD/index/config equality assertions, so hostile-environment isolation remains unverified.
- Review corrections: Queue validity: uncertain -> valid, based on the independently inspected report and owner behavior. Queue solution: unknown -> known, based on the independently inspected report and owner behavior. Queue structural_change: unknown -> no, based on the independently inspected report and owner behavior. Queue recommended_action: keep_open -> fixed_pending_verification, based on the independently inspected report and owner behavior.

## seed_builtin_option_name_heuristic_breaks_user_option_enum_2026-08-16 — Seed HIR lowering: the builtin-`Option` exception is keyed on a NAME, so a user-declared `enum Option` is misrouted

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_builtin_option_name_heuristic_breaks_user_option_enum_2026-08-16.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/hir/lower/expr/control.rs:730-765; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs:3115-3145
```
- Review rationale: Full report retracts observable native miscompilation: interpreter controls bypass HIR and native-build was blocked. Both HIR match owners now require genericity as well as name/variant shape, avoiding non-generic user Option but still admitting generic user Option<T>. The report explicitly retains this provenance collision and pure-Simple counterpart. Thus the research proposal overstates a complete known remedy; require native identity-aware controls for generic and non-generic user enums.
- Review corrections: Small-model proposal revised; its labels are not accepted by provenance alone. Generic user Option<T> and pure-Simple residuals preclude a complete known fix.

## seed_checked_sign_array_arc_mismatch_2026-08-22 — Rust seed checked-sign result constructs `Vec` where `Value::Array` owns `Arc<Vec>`

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_checked_sign_array_arc_mismatch_2026-08-22.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/signatures.rs:153-157,566-585; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/value.rs:3119-3122; target-ancestry patch 9ecc62bf6080e7cc1abad3afa8d2079fac6db1c1
```
- Review rationale: Historical E0308 affected both checked-sign status/payload branches. Both now invoke Value::array(Vec), whose impl Into<ArrayData> constructor wraps Arc correctly. The focused test calls successful Ed25519 and four malformed checked signers and checks status 0/1. This is a concrete constructor correction; historical Phase2 evidence does not qualify current compilation or focused test.
- Review corrections: Queue validity: uncertain -> valid, based on the independently inspected report and owner behavior. Queue solution: unknown -> known, based on the independently inspected report and owner behavior. Queue structural_change: unknown -> no, based on the independently inspected report and owner behavior. Queue recommended_action: keep_open -> fixed_pending_verification, based on the independently inspected report and owner behavior.

## seed_coalesce_stateful_operand_twice_2026_10_12 — Seed coalesce evaluates a stateful optional operand twice in ast_semantic_hash_finish

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_coalesce_stateful_operand_twice_2026_10_12.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/hir/lower/expr/control.rs:2119-2146,2228-2240; target-ancestry patch ffbb28e9bc926528376bea514c747cbda6835590
```
- Review rationale: Report distinguishes failed real hash encoder from a successful caller binding workaround. Current lower_coalesce stores expr_hir once in a private local and the condition/unwrap read that local; the result is a Block containing store plus lazy If. This repairs duplicate evaluation at the owner, independently of generated caller workaround. Side-effect-count and encoder execution without workaround remain unqualified.
- Review corrections: Queue validity: uncertain -> valid, based on the independently inspected report and owner behavior. Queue solution: unknown -> known, based on the independently inspected report and owner behavior. Queue structural_change: unknown -> no, based on the independently inspected report and owner behavior. Queue recommended_action: keep_open -> fixed_pending_verification, based on the independently inspected report and owner behavior.

## seed_constructor_static_method_no_literal_coercion_2026-07-20 — Seed constructor dispatch needs an exact runtime type: an int literal will not coerce to a

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_constructor_static_method_no_literal_coercion_2026-07-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_method/special/objects.rs:41-149,235-274
```
- Review rationale: Full report update separates run-path coercion from SSpec imported-static resolution and says a numeric patch yielded zero green specs. Current scorer still rejects unmatched types but dispatch now falls back to one distinct arity signature; this materially changes the old exact-type-only premise. Generic and trait matching have also changed. Neither this fallback nor the old coercion proposal establishes imported-class resolution or wrapper conversion correctness. Need distinct Float32 run/test controls and declaration-order overload fixture.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_emit_object_superlinear_hang_large_module_2026-07-20 — native-build --emit-object never emits IR for a 479-fn module; runs killed at 1h, 3h and 6

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_emit_object_superlinear_hang_large_module_2026-07-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:28-37; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/60.mir_opt/mir_opt/var_reassign_analysis.spl:33-75
```
- Review rationale: Full report records long pre-llc CPU-bound emission and explicitly reports continued hanging after the SSA update optimization. Current backend imports the SSA owner; count updates use indexed assignment and alias lookup uses Dict with a bounded chain. These changes remove specific suspected costs but do not identify the historically dominant loop. Require phase/per-function append traces for the original 479-function workload; no known remedy or present runtime claim follows.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_enum_variant_bare_name_last_registration_wins_2026_10_19 — Seed resolves enum variants by bare enum name (last registration wins); duplicate ByteOrder broke every native-build importing io_runtime

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_enum_variant_bare_name_last_registration_wins_2026_10_19.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_method/mod.rs:1317-1328; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs:40-55
```
- Review rationale: Report attributes ByteOrder collision to bare-name lookup and explicitly calls TextByteOrder rename a workaround. Current interpreter still consults enum_name-keyed local/block/global maps. MIR now prefers resolved enum type identity but falls back to registry.lookup(enum_name), so the two paths differ. Caller rename cannot prove root namespace repair. Need duplicate-name import-order controls and registration provenance through both paths before claiming a known complete fix.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_global_interface_cache_rebuild_latency_2026-10-05 — Seed global interface cache key rebuilds unchanged modules

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_global_interface_cache_rebuild_latency_2026-10-05.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:1250-1284,1315-1339,1996-2058,2068-2105
```
- Review rationale: Terminal historical receipt confirms 1180 rebuilds due to global layout/signatures, not cache deletion. Current key combines base hash, build fingerprint and InterfaceSliceIndex.digest_for_source; comments explicitly move observable interfaces into per-module slices while retaining layout for diagnostics. Thus the old global-key mechanism has evolved. Slice tokenization conservatively widens names, but completeness across defaults, ambiguous candidates and transitive imported layouts was not established here. Preserve the performance limitation pending dependency-mutation fixtures and attributed timings; do not remove safety inputs.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_helper_return_type_mistyped_as_tuple_2026-08-21 — Seed mis-types a `-> [text]` helper's result, breaking every downstream field access

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_helper_return_type_mistyped_as_tuple_2026-08-21.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/check/any_escape_census.spl:142-163; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/hir/lower/expr/calls.rs:235-253; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:706-727
```
- Review rationale: Report gives helper-return composition failure and says annotation merely changes the diagnostic. Current census still inlines collection. HIR call lowering now consults resolved global symbol and call_return_type follows Function.ret or named callable metadata, rather than deliberately turning [text] into Tuple. This is relevant attribution logic but does not isolate the old dynamic composition failure. Require restored collect_paths plus original downstream kind access under an identified route; inline caller is not proof of root repair.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_http_server_handle_connection_dispatch_2026-09-04 — `SimpleHttpServer` accepts a connection and then dies: `handle_connection` not found on type `dict`

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_http_server_handle_connection_dispatch_2026-09-04.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/http_server/server.spl:208-264; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/exec_core.rs:1187-1223
```
- Review rationale: Report observes a module Dict as self after first accept; atomic collision is explicitly only a lead. Current accept loop either handles configured parser on owner or passes stream/self via thread_spawn_with_args to a typed local and static handler, with static fallback on spawn failure. This avoids the original captured-receiver shape, yet does not diagnose module-flattening binding or establish network success. Need first-request control with callback receiver identity; no complete known compiler remedy is established.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_hybrid_jit_spliced_u8_array_boxed_elements_2026_10_19 — Seed hybrid JIT returns [u8] through the interpreter splice with boxed elements; indexing and bulk rt_* calls misread it

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_hybrid_jit_spliced_u8_array_boxed_elements_2026_10_19.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/runtime_bridge.rs:81-104; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/value_bridge.rs:319-325; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/exec_core.rs:1187-1223
```
- Review rationale: Report distinguishes correct iteration from wrong typed indexing/bulk conversion only on hybrid splice. Current runtime bridge still expands Value::ByteArray into byte_array_values and values_to_runtime_array; secondary bridge also uses generic ARRAY. Driver actively splices unavailable externs while retaining boxed composite returns. This supports a representation mismatch concern and historical defect, but allocator metadata and typed consumer compatibility must be traced before selecting a packed-return patch. Require splice iteration/index/bulk parity on the actual file-read fixture.
- Review corrections: Queue validity: uncertain -> valid, based on the independently inspected report and owner behavior. Small-model proposal revised; its labels are not accepted by provenance alone. See per-ID rationale for the changed source behavior and limits. Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_indexed_field_assign_complex_receiver_unisolated_2026-08-31 — New occurrence of the OPEN indexed-field-assignment limitation: FAT32 `file_generations` (2026-08-31)

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_indexed_field_assign_complex_receiver_unisolated_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter/node_exec.rs:1290-1329; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter/place.rs:69-118; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/fs_driver/fat32_file_ops.spl:64-91
```
- Review rationale: Report explicitly says three miniature self.gens forms passed while FAT32 context failed. Current FAT32 still uses self.file_generations[slot].generation; assignment owner now resolves full projection chains and place resolver handles Identifier/FieldAccess/Index recursively, so the old unconditional complex-receiver rejection has changed. This supports relevant source improvement but not resolution of the unisolated context trigger. Require original write/truncate regression with place-root tracing; no array-layout workaround is a root fix.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_interp_mut_out_param_writeback_and_u8_data_ptr_2026-08-31 — Seed interpreter: `&mut` out-param writeback loss and `[u8].data_ptr()` pointing at boxed value cells

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_interp_mut_out_param_writeback_and_u8_data_ptr_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/mod.rs:682-690; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/mod.rs:3344-3374; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_method/collections.rs:1060-1064
```
- Review rationale: Report tracks two ABI gaps, so one repair cannot close the record. Current extern caller reaches call_extern_function; its post-dispatch loop publishes BorrowMut contents back only for identifier operands, directly addressing the reported &mut handle shape. Generic array data_ptr still returns arr.as_ptr, requiring byte-handler and lifetime qualification before calling packed-byte behavior fixed. Preserve separate checked-dlopen writeback and raw packed-byte read controls; caller fallback/allocation remain workarounds.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_interpreter_segv_on_undefined_function_call_2026-09-12 — `simple run` SEGVs on a call to an undefined function (the `compile` lane diagnoses it)

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_interpreter_segv_on_undefined_function_call_2026-09-12.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/instr/calls.rs:4625-4690; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/exec_core.rs:1187-1223
```
- Review rationale: Report discriminates undefined-function segfault from clean undefined-variable/compile diagnostics on one old Windows seed. Current cross-module call code declares imports and emits calls; incompatible unresolved declarations can instead warn and synthesize nil. Driver hybrid-splices unresolved declared externs, which does not by itself cover undeclared no_such_fn. Need trace of the minimal no_such_fn through resolution/finalization and an attributed diagnostic control; restored app helpers do not establish compiler repair.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_jit_cannot_resolve_text_dot_from_char_code_2026-09-04 — Seed JIT cannot resolve `text_dot_from_char_code`, killing any `simple run` that calls slang's manifest parser

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_jit_cannot_resolve_text_dot_from_char_code_2026-09-04.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:2538-2574; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/common/src/runtime_symbols.rs:1196
```
- Review rationale: Report accurately separates interpreter tests from JIT import finalization. Current integer chr dispatch imports canonical rt_char_from_code, and provider manifest lists that name while comments intentionally exclude legacy text_dot_from_char_code. This supersedes the generic suggestion to add legacy aliases. The inspected arm is integer chr, so exact text.from_char_code/manifest-parser lowering still needs qualification; do not equate a related canonical arm with complete repair of the reported entry point.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_jit_coverage_self_hosted_compiler_2026-08-21 — Seed JIT coverage on the self-hosted compiler: the premise was wrong — there is no per-function fallback

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_jit_coverage_self_hosted_compiler_2026-08-21.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/exec_core.rs:1187-1223,1567-1616; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/jit.rs:330-372
```
- Review rationale: Read latest report updates: runtime-facing closure convention was implemented after earlier blanket bails, with ANY/BOOL/boxed-handle residuals. Current driver names partial extern hybrid splice, uses a capability-backed argv preference, and explicitly pins lint to interpreter for later parity failures. JIT admission still rejects unsupported closure boundary types/scalar-boxed handles. Thus neither initial no-hybrid premise nor historical lint speedup describes all current routes. Keep diagnostic/performance classification uncertain until exact worker/lint route receipts and residual closure fixtures are obtained; do not weaken guards.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_jit_lsu64_load_lowering_forces_interpreter_2026-07-22 — Seed JIT HIR lowering reports Unknown variable lsu64_load for a valid cross-module

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_jit_lsu64_load_lowering_forces_interpreter_2026-07-22.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/hardware/rv64gc_rtl/lsu.spl:51-65; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/hardware/rv64gc_rtl/core.spl:29,126; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/hir/lower/expr/calls.rs:235-253; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/exec_core.rs:1187-1223; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:441-529
```
- Review rationale: Current lsu64_load is a real typed sign/zero-extension function and core explicitly imports/calls it. HIR regular calls now retain resolved symbols for return attribution, but that does not establish why this particular import was absent historically. Report DTB A/B controls only bound the observed tick frontier. Need the original SoC probe with resolved import owner and actual engine receipt; export existence alone does not prove JIT or banner recovery. Current identifier owner explicitly resolves flattened callable owner and selective import aliases before bare lookup; qualifying that path on this particular fixture remains necessary.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_jit_some_constructor_corrupts_value_2026-09-13 — Seed JIT: the explicit `Some(x)` optional constructor produces a corrupt value

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_jit_some_constructor_corrupts_value_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/hir/lower/expr/calls.rs:57-95,735-741; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs:594-610
```
- Review rationale: Report explicitly restricts landed cast correction to str/text of ANY unwrap and says it cannot explain Some-versus-coercion asymmetry or equality/concat/len symptoms. Current MIR cast includes ANY-to-string conversion. Short Some construction still produces a regular constructor call typed ANY except function payloads. These are distinct seams; neither the cast fix nor typed-function exception proves text optional correctness. Preserve full five-line Some/coercion fixture and compare constructor, unwrap and equality representations.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_jit_wide_literal_match_u64_misevaluates_2026-08-28 — Seed JIT: literal-arm `match` on u64 mis-evaluates in a stdlib module (2026-08-28)

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_jit_wide_literal_match_u64_misevaluates_2026-08-28.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl:249-283; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/hir/lower/expr/control.rs:610-630; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/exec_core.rs:1567-1616
```
- Review rationale: Report says standalone wide-literal matches passed and only CSR import context/fallback mis-evaluated. Current csr_is_supported retains table scanning while native intrinsic csr_read retains literal matches. HIR literal matching lowers subject/literal and distinguishes string comparison; no evidence ties that branch to the historical imported-u64 failure. Need original module-context fixture with actual execution-route receipt and standalone control; neither table workaround nor symbol-registry changes establish root fix.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_list_comprehension_join_and_empty_native_2026_10_21 — bootstrap comprehensions lower to nil and erase join receiver

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_list_comprehension_join_and_empty_native_2026_10_21.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:349-381; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/hir/lower/expr/control.rs:3622-3635; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/hir/lower/module_lowering/function.rs:658-666
```
- Review rationale: Report retains full-namespace optional-join failure plus typed/unpolluted native empty-value controls. Current lower_expr ends in lenient Nil/ANY or Unsupported; scoped ListComprehension hits are identifier/self walkers, not lowering handlers. This supports the report mechanism: knowing child identifiers is not implementation of comprehension values. Explicit push loops preserve callers only. A real typed iteration lowering with join return attribution is required, but the complete root patch/contract was not established; retain unknown solution pending nonempty full-namespace tests.
- Review corrections: Queue validity: uncertain -> valid, based on the independently inspected report and owner behavior. Small-model proposal revised; its labels are not accepted by provenance alone. See per-ID rationale for the changed source behavior and limits. Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_method_find_on_nested_substring_call_2026-08-25 — Seed: `.find()` on a nested `substring()` result fails to resolve — 2026-08-25

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_method_find_on_nested_substring_call_2026-08-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs:146-184,1180-1198; target-ancestry patch 0161a33ed511836874d5ad023bf1bc2ea0f2d37f
```
- Review rationale: Report failure is nested temporary-text dispatch, with a bound-intermediate control. Current call_method_on_value string arm implements find/find_str/index_of, optional byte start, empty needle and missing match; substring returns text from byte slices, so chained receiver reaches the now-supported find arm. This is a local dispatch remedy, not a text-search algorithm rewrite. History identifies 0161a33ed51; current original chained fixture execution and focused alias controls remain untested.
- Review corrections: Queue validity: uncertain -> valid, based on the independently inspected report and owner behavior. Queue solution: unknown -> known, based on the independently inspected report and owner behavior. Queue structural_change: unknown -> no, based on the independently inspected report and owner behavior. Queue recommended_action: keep_open -> fixed_pending_verification, based on the independently inspected report and owner behavior. Small-model proposal revised; its labels are not accepted by provenance alone. See per-ID rationale for the changed source behavior and limits. Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_optional_query_comparison_divergence_2026-08-16 — Seed interpreter: `.?` operator yields value-or-nil, not bool; module-private `val` imports resolve inconsistently

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_optional_query_comparison_divergence_2026-08-16.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter/expr.rs:533-568; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/net/entity/request_types.spl:23-27; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter/expr/ops.rs:762-776
```
- Review rationale: Full report corrects original bool premise and distinguishes A/B/D repairs from still-open diagnostic C. Current ExistsCheck unwraps, filters nil/empty values and returns the payload itself; bool payloads remain bool, so blanket bool-comparison banning would be wrong. Resource bound is public and packed concat arms are present. This disproves the original blanket divergence premise but not the multi-part tracked diagnostic/runtime problem. Keep uncertain overall; verify source locations for failing semantics and actual chunked path separately, preserving value-or-nil contract.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_overload_score_option_bytes_misleading_unknown_static_2026-07-20 — Static-call overload scoring reports unknown static method object on class

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_overload_score_option_bytes_misleading_unknown_static_2026-07-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:1284-1300; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_method/special/objects.rs:77-149,247-272,370-383
```
- Review rationale: Historical repro depended on make_some byte return and scorer rejection. Current rt_file_read_bytes returns bare ByteArray on success/nil on failure, and constructor dispatch has unambiguous arity fallback. Thus the exact wrapper-trigger has changed. However scorer still distinguishes Array/FrozenArray/Tuple and terminal error still says unknown static method rather than rejected overload. Need typed byte constructor plus intentionally mismatched multi-candidate diagnostic controls; caller coalescing cannot prove diagnostic honesty.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_parser_accepts_match_keyword_as_identifier_2026-07-27 — Seed parser accepts `match` keyword as an identifier — divergence detonates at bootstrap Stage 4

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_parser_accepts_match_keyword_as_identifier_2026-07-27.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/stmt_parsing/var_decl.rs:47-61,123-147; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/tests/statement_tests.rs:41-53; target-ancestry patch ae55a7467197350bdf8b91c48444c167219ce8bb (restoration, not original fix attribution)
```
- Review rationale: Report later clarifies var match is sanctioned, unlike val match. Current parse_val specifically rejects TokenKind::Match with contextual error while parse_var delegates ordinary mutable binding parsing. Focused statement test asserts val rejection, var identifier/mutability and contextual class acceptance. This is a local grammar correction respecting the positive control; current cross-parser execution remains untested.
- Review corrections: Queue validity: uncertain -> valid, based on the independently inspected report and owner behavior. Queue solution: unknown -> known, based on the independently inspected report and owner behavior. Queue structural_change: unknown -> no, based on the independently inspected report and owner behavior. Queue recommended_action: keep_open -> fixed_pending_verification, based on the independently inspected report and owner behavior. Small-model proposal revised; its labels are not accepted by provenance alone. See per-ID rationale for the changed source behavior and limits. Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_per_call_env_rebuild_o_globals_regression_2026-08-21 — Seed interpreter rebuilds the whole callee env per call (O(module globals))

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_per_call_env_rebuild_o_globals_regression_2026-08-21.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/value.rs:1236-1272,2171-2187; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:174-208
```
- Review rationale: Latest report header explicitly supersedes recorded-write template mitigation with scope-chain CowEnv, while leaving wall target open. Current clone shares base/scope Arcs and copies per-frame overlay/sets; owned captured call entry attaches owner_scope instead of rebuilding globals. This substantiates mechanism improvement but not O(args) for all captures or original five-second/guard budget. Remaining cost requires original driver fixture phase timings with frame-width attribution; do not retry reverted periodic global folding or infer performance PASS from structural change.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_rebuild_10_12_breaks_instance_method_dispatch_object_receiver_2026-08-18 — Shared seed rebuilt 2026-08-18 10:12 breaks ALL instance-method dispatch — receiver types as `object`

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_rebuild_10_12_breaks_instance_method_dispatch_object_receiver_2026-08-18.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_method/mod.rs:1456-1525; target-ancestry patch df7515888955c166a20e0abd5260db2af5c6cfac
```
- Review rationale: Historical Greeter control constructed the right value but instance dispatch fell through as object. Current primary dispatcher has an explicit ClassInstance arm, obtains instance.class(), searches class/impl/global/trait methods and binds self to the same reference instance before executing. Historical diff df751588895 adds exactly this missing arm. This is a concrete local remedy; original Greeter and auth-token regression must still run on an identified current artifact, and the old shared binary build provenance remains incomplete.
- Review corrections: Queue validity: uncertain -> valid, based on the independently inspected report and owner behavior. Queue solution: unknown -> known, based on the independently inspected report and owner behavior. Queue structural_change: unknown -> no, based on the independently inspected report and owner behavior. Queue recommended_action: keep_open -> fixed_pending_verification, based on the independently inspected report and owner behavior. Small-model proposal revised; its labels are not accepted by provenance alone. See per-ID rationale for the changed source behavior and limits. Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_redeploy_breaks_test_runner_accessor_rewrite_parse_2026-08-25 — Seed redeployed 2026-08-25 05:16 UTC cannot parse `tooling/easy_fix/accessor_rewrite.spl` — `bin/simple test` and md doctests abort

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_redeploy_breaks_test_runner_accessor_rewrite_parse_2026-08-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/expressions/primary/mod.rs:15-54,193-197; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/parser_impl/core.rs:1059-1072; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/tests/unsafe_block_vs_identifier.rs; target-ancestry patch 276a399529b2d72c42e6c5d6a02b35645278bf2a
```
- Review rationale: Full report attributes unsafe iterable/header ambiguity to an unlanded overly broad bare-colon primary. Current expression arm requires validated parenthesized header; statement arm handles bare colon separately and delegates validated capability forms exactly once. Eight focused parser cases cover unsafe/danger identifiers plus bare/capability/value-bound blocks. History 276a399529b shows validator replacement. Source remedy is present; current parser/doctest execution and deployment identity remain untested, not grounds to roll back valid unsafe expressions.
- Review corrections: Queue validity: uncertain -> valid, based on the independently inspected report and owner behavior. Queue solution: unknown -> known, based on the independently inspected report and owner behavior. Queue structural_change: unknown -> no, based on the independently inspected report and owner behavior. Queue recommended_action: keep_open -> fixed_pending_verification, based on the independently inspected report and owner behavior. Small-model proposal revised; its labels are not accepted by provenance alone. See per-ID rationale for the changed source behavior and limits. Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_result_err_shorthand_closure_segv_2026-09-12 — Seed segfaults on `Result` Err + shorthand-closure projection (`.map(_.field)`)

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_result_err_shorthand_closure_segv_2026-09-12.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_helpers_option_result.rs:136-169; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:2590-2612; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/collections.rs:6830-6840; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/objects.rs:762-783; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/storage_roots/environment_owner.spl:61-77
```
- Review rationale: Report isolated Err plus shorthand projection, while standalone Ok/unwrap controls passed. Tree-walk Result map still short-circuits the other variant. Generic generated map dispatch calls rt_map, whose non-array branch calls rt_option_map; that helper only checks None and otherwise invokes the closure on enum payload and wraps Some. This is a concrete semantic seam to investigate for Result receivers, but exact generated lowering of the combined fixture has not been established. Caller still uses ? propagation workaround. Require Err/Ok generated-call trace and runtime variant parity; do not patch the correct tree-walk short circuit speculatively.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_return_bare_value_next_line_ambiguity_2026-07-31 — `return` with its value entirely on the next line fails with UnexpectedToken expected

- Source receipt: `adjudication_v2_20`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_return_bare_value_next_line_ambiguity_2026-07-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/stmt_parsing/jump.rs:15-53
```
- Review rationale: Report deliberately records a design question, not demonstrated real-source regression. Current parse_return treats newline as value=None, and parse_break likewise only parses a same-line value; this matches the reported ambiguous bare-return contract. Supporting an indented next-line value would require an explicit continuation decision and positive bare-return controls. No false-premise closure follows from a tracked design request; owner syntax decision remains the bounded next step.
- Review corrections: Previously unexamined research row independently investigated here; remaining limits are explicit.

## seed_static_method_default_param_value_wrong_2026-09-13 — Seed interpreter: static-method default parameter fills the constant 3, not the declared value

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_static_method_default_param_value_wrong_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_method/mod.rs:1668; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_method/special/objects.rs:215
```
- Review rationale: The report contrasts static defaults 0/42/100 all becoming 3 with a free-function default of 100. Current Value::Constructor dispatch calls handle_constructor_methods; that owner chooses static/no-self candidates, binds supplied arguments, evaluates each missing param.default in an empty environment, and executes with the bound map. There is no constant-3 assignment in this route. It does not prove the reported binary selected this route or that its JIT/tag boundary was correct. Remaining evidence: A binary-bound static/free-function differential with dispatch/value-tag capture is needed; changing the inspected default loop is not a supported remedy.

## seed_stdlib_resolves_build_time_repo_root_before_cwd_2026-08-24 — Seed resolves `use std.*` from its BUILD-TIME repo root before the process cwd

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_stdlib_resolves_build_time_repo_root_before_cwd_2026-08-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/module_loader.rs:582; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/module_loader.rs:2782; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/module_loader.rs:3201; Target-ancestry history: 871e40c8a28e8092c2eebcad7133d90554608a9e
```
- Review rationale: The report gives strace and same-binary A/B evidence of build-tree stdlib winning for temporary sources. Current resolve_from_stdlib_fallbacks tries runtime_root first; the actual resolver passes current_dir before CARGO_MANIFEST_DIR. The ancestry repair diff replaces the old build-root-first array and adds a two-distinguishable-worktree test asserting the runtime module wins. The focused source has no d805-to-c0 delta. This is a concrete local repair already present, beyond the doctest-location workaround. Remaining evidence: Execute the two-root control with a source-bound deployed seed; source/test inspection is not a current runtime PASS.
- Review corrections: Previously unknown/keep_open; target source and causal repair diff support known/no/fixed_pending_verification. Historical reproduction remains untested.

## seed_test_runner_unusable_on_windows_false_outer_bound_timeout_2026-09-13 — Seed `bin/simple test` cannot derive its own executable identity on Windows: `child-spawn-failure` unless `SIMPLE_BINARY` is set

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_test_runner_unusable_on_windows_false_outer_bound_timeout_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl:169; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl:194
```
- Review rationale: The full report corrects outer-timeout wording to child-spawn failure and reports SIMPLE_BINARY fixing the same Windows spec while reducing elapsed time. Current find_simple_binary prefers a validated explicit override, rejects .spl argv0, canonicalizes proc self links, then uses pid query and known candidates. Thus the obvious source-file-as-executable hazard is guarded. Windows discovery and the reported 730-second failure overhead are not established by these branches. Remaining evidence: Pin a Windows executable and collect discovered path, spawn outcome and setup phase timing; the override remains a workaround rather than proven discovery repair.

## seed_windows_path_identity_errno_discovery_2026_10_06 — keep_nonwindows_errno_directives_out_of_windows_seed_discovery

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/seed_windows_path_identity_errno_discovery_2026_10_06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/path_identity_abi.spl:2; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/_PathIdentityPosix/errno_abi.spl:1; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/cfg_strip.rs:49; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/discovery.rs:12; Target-ancestry history: c6c146f6322; cbc65b90e49
```
- Review rationale: The report scopes the historical failure to pinned seed283f preprocessing and explicitly lacks native-positive evidence. Current facade retains Windows errno=0 and imports the POSIX leaf only in @else. Current discovery delegates stripping to cfg_strip, whose implementation now delegates balanced branch selection to simple_parser::cond_compile with target OS/arch; it is no longer the reported windows-only condition matcher. This is substantive owner evolution, but it does not qualify the pinned built seed or all path-errno providers. Remaining evidence: Inspect/qualify the exact rebuilt conditional-compiler provider and execute the Windows entry-closure fixture before removing the import workaround.

## self_error_used_where_error_fatal_intended_family_2026-08-08 — MirLowering.error() sites intended as fatal stay non-fatal, so builds exit rc=0 on

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/self_error_used_where_error_fatal_intended_family_2026-08-08.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/asm_and_targets.spl:189; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/asm_and_targets.spl:262; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_pipeline_lowering.spl:222; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_pipeline_lowering.spl:301; Target-ancestry history: a814b767e3fc8e2313746e601673df449687ca76 (queue lead; target call sites independently checked)
```
- Review rationale: The report is a family sweep with several later corrections: Option.None recovery is intentionally nonfatal and several enum diagnostics were already promoted. Current asm version/assert failures call error_fatal, while the non-exhaustive asm message still calls error. The driver honors error.fatal or its legacy prefix list; that list contains no asm-nonexhaustive prefix. This confirms surviving differential diagnostic handling without treating every self.error site as a defect. Remaining evidence: A negative fixture must reach each remaining intended-fatal branch; full-family remedy and required scope remain unknown.
- Review corrections: Do not repeat the superseded blanket error-to-fatal prescription or treat the two landed asm-assert changes as family closure.

## self_hosted_font_renderer_optional_field_shape_2026-07-11 — Self-hosted resolver reports class FontRenderer has no field ttf_rasterizer though it is

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/self_hosted_font_renderer_optional_field_shape_2026-07-11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/font_owner.spl:14; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/engine.spl:378; Target-ancestry history: 2a1dc028959 (latest inspected owner history, not proof of this repair)
```
- Review rationale: The report follow-up explicitly resolves the optional-field/class-shape problem and leaves zero pixels/cache hits as a state-retention issue. Current Engine2D owns Engine2DFontOwner with a renderer list; ensure/install rebuild that owner, and _install_active_fonts performs explicit local-owner writeback. This is materially different from the reported module-global optional renderer returned across a function boundary. The current ownership code is relevant mitigation, not evidence that public pixel/cache scenarios now pass. Remaining evidence: Trace load/draw/unload through this owner and run the public pixel/cache assertions under a qualified current artifact.
- Review corrections: Historical class-shape diagnosis is superseded; current state-retention behavior is uncertain despite explicit owner/writeback changes.

## self_hosted_rc1_hir_codec_segv_native_build_2026_10_11 — Self-hosted rc.1 binary SIGSEGVs in HIR codec on any native-build of the current tree

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/self_hosted_rc1_hir_codec_segv_native_build_2026-10-11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/generated/hir_codec.spl:5176; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/generated/hir_codec.spl:6871; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/generated/hir_codec.spl:8300; Target-ancestry history: 9625bb7a158
```
- Review rationale: The actual hyphenated-date report records rc.1 hc_enc_hir_module+1460 crashing at both base and cherry-pick tip, while check succeeds. Current module/type/symbol-table encoders reject nil, illformed and unregistered nodes before reading their fields; the module encoder explicitly traverses optional symbols into hc_enc_symbol_table. This undermines any assumption that current source is simply the old unguarded encoder. The report itself leaves binary drift versus live poison unresolved, and these guards cannot establish the old artifact source identity. Remaining evidence: Obtain the producer-authenticated current binary, failing node/schema and backtrace; distinguish source repair from redeploy before choosing a remedy.
- Review corrections: Use report self_hosted_rc1_hir_codec_segv_native_build_2026-10-11.md, not a fabricated underscore-date path. Historical valid crash does not identify a current source defect.

## self_hosted_simpleos_target_native_build_crash_2026-07-11 — native-build --target x86_64-unknown-simpleos dumps core before writing any cache file or

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/self_hosted_simpleos_target_native_build_crash_2026-07-11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:15751
```
- Review rationale: The report separates the original stale two-argument rt_env_set crash from enum-call LLVM verification, llvm-lib DataLayout failure, incomplete full-CLI closure and the later provenance-qualified August crash. Current runtime_native.c defines the four-argument pointer/length rt_env_set ABI, consistent with the original caller backtrace. That supports the original relink diagnosis only; it does not explain the later crash or establish an admitted SimpleOS compiler. A single rebuild-only solution for the entire record is unsupported. Later report entries also record a focused static-ELF success and then pending sysroot/guest-tool relink; neither discharges the separately dated August crash. Remaining evidence: Compare a current artifact backtrace to the recorded rt_env_set and DataLayout signatures, then require full closure/static ELF and target smoke receipts.
- Review corrections: Do not collapse distinct blockers into the stale-runtime diagnosis or treat its source ABI consistency as full resolution.

## self_hosted_sspec_describe_colon_parser_2026-08-08 — Self-hosted parser reports unexpected token in expression: ':' at every standard SSpec

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/self_hosted_sspec_describe_colon_parser_2026-08-08.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser_stmts.spl:287; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser_stmts.spl:316; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:2251; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/lint/parse001_spec_files_spec.spl:53
```
- Review rationale: The report records describe/it colon rejection and a later hypothesis of missing generic call-block grammar. Current parser folds bare identifier plus string into a call, consumes the colon into a block/lambda argument, and module dispatch actually invokes both helpers. The parser spec directly calls parse_module_silent_checked on nested no-paren describe/it and also rejects malformed inputs. The repair uses existing call/lambda contracts. No d805-to-c0 delta exists in parser_stmts, so absence in the old deployed runtime is not absence in current source. Remaining evidence: Qualify the self-hosted parser and then execute the original Caret examples; parsing fixtures alone do not prove all assertions run.
- Review corrections: Unknown remedy is replaced by present known local grammar repair; keep the historically valid report fixed_pending_verification, never invalid.

## self_hosted_symbol_table_hirtype_garbage_at_rest_2026-08-31 — Self-hosted Stage-2 reads a garbage `HirType` from the symbol table — three reader fixes were all treating a symptom

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/self_hosted_symbol_table_hirtype_garbage_at_rest_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_symbol_table_methods.spl:530; Target-ancestry history: 5c8b71f0775
```
- Review rationale: The full report contains its own decisive correction: symbol/type tags were intact at publication and consumption, reader rewrites were inert, and the transient-classify skip counter had zero hits. Thus garbage-at-rest and that promotion shortcut are not supported roots. Current get_symbol_type_raw obtains a symbol and returns found.type_ only after optional/nil checks; its neighbor explicitly avoids optional aggregate crossings. Those reads show the boundary remains relevant but do not overturn the report ablations or identify a lifetime fault. Remaining evidence: Use retained rejected-stage2 artifact and non-vacuous per-run module fixtures to locate the first lifetime transition; prior attempted reader fixes must not be retried unchanged.
- Review corrections: Downgrade root certainty to uncertain; the title and intermediate transient hypothesis are contradicted by the report correction. No new execution or retry cycle was conducted.

## selfhost_hir_cache_encode_hir_type_segv_2026-08-22 — Self-host HIR cache encoding segfaults in `hc_enc_hir_type` (2026-08-22)

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/selfhost_hir_cache_encode_hir_type_segv_2026-08-22.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/generated/hir_codec.spl:6871; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/generated/hir_codec.spl:8300; Target-ancestry history: 9625bb7a158
```
- Review rationale: The report backtrace enters hc_enc_hir_type through symbol/table/module serialization after HIR diagnostics; disabling frontend caching only bypassed it. Current type encoding validates node formation and registration, then serializes optional kind/span; symbol-table encoding sorts keys and serializes optional symbols/scopes. These are actual field accesses and guards, not evidence from a filename. They leave both schema/version compatibility and native aggregate validity unresolved for the admitted b22c425 compiler. Remaining evidence: Bind producer and cache schema, compare full encoder/decoder symbol-table schema and capture the type entering the failing frame. No cache-format or ownership remedy is yet justified.
- Review corrections: Queue validity=valid replaced by uncertain after independent report and owner review; see rationale.
