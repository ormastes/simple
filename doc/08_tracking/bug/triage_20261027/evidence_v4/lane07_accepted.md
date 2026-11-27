# V4 lane 07 accepted evidence

Accepted classifications in V4: 153. Assessment target: `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`.

- 49 accepted records are inherited field-for-field from V3; their detailed evidence is preserved in [V3 lane 07 evidence](../evidence_v3/lane07_accepted.md).

- 104 additional accepted records are detailed below.

## selfhost_names_with_no_import_path_masked_by_seed_flat_resolution_2026-08-01 — 66 compiler names are declared in one module with no import path on any importer's graph

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/selfhost_names_with_no_import_path_masked_by_seed_flat_resolution_2026-08-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/desugar/placeholder_lambda.spl:40; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/desugar/placeholder_lambda.spl:787; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/compiler.spl:11; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/compiler.spl:58
```
- Review rationale: The report distinguishes true missing imports from export-use propagation and corrects two earlier class-A attributions. Its remaining table names expr_interpolated_string and CodegenMode/CodegenPipeline. Current placeholder_lambda explicitly imports the accessor owner and invokes the preserving accessor; current backend/compiler explicitly imports CodegenMode/CodegenPipeline and uses them for pipeline selection. These concrete residual examples have changed. They cannot certify all 145 historical file/symbol pairs or establish that the remaining census is still current. Remaining evidence: Reconcile the retained unique file/symbol census against exact current import/export reachability; do not widen resolver visibility or re-add already present imports.
- Review corrections: Historical missing-import inventory is not a current outstanding count; inspected residual entries already have explicit owner imports.

## selfhost_noimport_carveouts_error_panic_blockdsl_nilname_2026-08-01 — `error` and `panic` are not both builtins in the self-hosted front end: both lower to

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/selfhost_noimport_carveouts_error_panic_blockdsl_nilname_2026-08-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Expressions/expression_support.spl:64; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:2499; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:8199
```
- Review rationale: The report distinguishes genuine panic builtin handling from nonexistent global error, and its final ledger corrects the block-DSL trigger to ordinary example strings rather than assuming raw docstrings. Current HIR admits panic and live MIR direct-call dispatch routes it to lower_bootstrap_panic_call. That implementation emits rt_panic with message/default message and terminates Abort, preventing a returning weak-stub fallthrough. The error-call sites and nil-concatenated identifier are separate unresolved questions; this partial repair cannot close the combined record. Remaining evidence: Investigate the remaining real-file example-string and nil-name slices and error callers with a qualified frontend; do not call the panic name-only whitelist a complete fix.
- Review corrections: The panic interception is now present and stronger than a NamedVar workaround; report final ordinary-string correction supersedes the raw-docstring-only hypothesis.

## server_compiler_bootstrap_moving_rust_inputs_2026-08-12 — Server compiler bootstrap blocked by moving Rust inputs

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/server_compiler_bootstrap_moving_rust_inputs_2026-08-12.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh:3620; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh:3657; Target-ancestry history: 6f53cfa8cd4
```
- Review rationale: The report describes three bounded bootstrap attempts, two correctly refusing publication after Rust inputs changed. The current owner re-fingerprints after Cargo, exits on mismatch, prepares an immutable generation, acquires authority and fingerprints again immediately before publication. These live checks substantiate the protective refusal mechanism. They do not invalidate the tracked operational inability to admit a compiler or identify which concurrent write caused a current failed build. Remaining evidence: Reconcile retained pre/post fingerprint details and source/build receipts in an isolated session; stable-input recovery is not a reason to weaken authority checks.

## set_literal_s_brace_unparsed_2026-09-06 — `s{...}` set literal is unparsed — seed has no production, self-hosted frontend has half

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/set_literal_s_brace_unparsed_2026-09-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/lexer.spl:24; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl:82; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl:542; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/lexer/identifiers.rs:380
```
- Review rationale: The report distinguishes set operations from missing literal syntax and downstream SetLit nodes from live frontend production. Current lexer facade delegates to CoreLexer; the live primary identifier route recognizes only a finite adjacent custom-block list that excludes s, otherwise returns expr_ident. The seed custom-prefix s arm recognizes sh/sql/schema/style and not s{. Scoped core/bridge searches also found no EXPR_SET_LIT/SetLitStart. These owner branches support the historical literal gap without claiming a complete new lexer/parser/bridge design or equating Set.from with literal acceptance. Remaining evidence: Trace remaining live CoreLexer token production and flat-to-typed converter contracts before choosing a complete cross-compiler repair; execute a real s{1,2,3} fixture only under a qualified runner.
- Review corrections: Late focused source tracing replaced the earlier incomplete prefix investigation; valid feature gap is supported, while solution and structural scope remain unknown.

## sffi_admitted_receipt_open_handle_binding_gap_2026-08-24 — SFFI admitted receipt is not yet bound to the open provider handle

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sffi_admitted_receipt_open_handle_binding_gap_2026-08-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/sffi/dynamic.spl:242; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/sffi/dynamic.spl:263; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/sffi/sffi_signature.spl:209; Target-ancestry history: 2c1058023c6
```
- Review rationale: The report correctly distinguishes sealed bytes/private fields from cryptographic authority. Current load_signed_linux calls verify_sffi_evidence_v2, derives the expected artifact digest from that result, loads a sealed artifact and stores both in SignatureVerifiedExactArtifactDynLib. resolve_evidence_bound_i64_manifest now requires that carrier, checks identity and resolves every slot before publication. This contradicts an unchanged caller-digest-only description of this route, but the cryptographic trust owner and provider-generation/lifetime guarantees were not fully audited here. Remaining evidence: Trace verify_sffi_evidence_v2 trust roots/token construction and generation-bound thunk lifetime, then qualify visibility and sabotage on an admitted runtime. Generic integer dispatch remains unsafe.
- Review corrections: The source now has a signed carrier and a stronger resolver parameter contract; do not infer complete cryptographic/provider-generation closure from its presence.

## sffi_authority_census_ambient_call_gap_2026-08-24 — SFFI authority census omits ambient raw calls

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sffi_authority_census_ambient_call_gap_2026-08-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/audit/sffi-call-authority-census.shs:18; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/common/mir_text_codegen.spl:15; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/common/mir_text_codegen.spl:305; Target-ancestry history: 4edef8fab8e
```
- Review rationale: The current census source builds its raw set from local extern declarations and named sffi imports, then emits only call spellings in that set within fn/me bodies. It has no resolved HIR provider identity. Thus an otherwise ambient foreign name is invisible by construction, and source spelling is not authoritative cross-engine inventory. The particular mir_text_codegen example has moved to imported sosix_env_get_nullable, so it is no longer evidence of a current direct rt_env_get call. The scanner completeness problem remains independently supported. Remaining evidence: Produce and reconcile resolved declaration/provider identities with pure-Simple rt_* negative controls; the old exact call-site oracle must be updated to its current owner.
- Review corrections: The quoted ambient call migrated to a facade, and the current scanned shell lacks the report-described wildcard enhancement. Neither fact proves authoritative coverage.

## sffi_contract_inventory_red_on_origin_main_2026-09-03 — `push-sffi-v2-authority` is RED on unmodified `origin/main` (2026-09-03)

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sffi_contract_inventory_red_on_origin_main_2026-09-03.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/audit/sffi-contract-inventory.shs:348; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/audit/sffi-contract-inventory.shs:471; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/audit/sffi-contract-inventory.shs:505; Target-ancestry history: 88aac2ffe28
```
- Review rationale: The report includes a same-binary pristine-main versus branch comparison with 416 signature variants. Current inventory still deduplicates signatures per symbol and classifies >1 as source_signature_variants, counts those symbol rows, and fails against default 399. The source therefore supports the reported gate meaning and excludes interpreting the migration count as the cause. It cannot reproduce the old 416 count or identify the actual 17 symbols requiring reconciliation without the source-bound symbol ledger. Remaining evidence: Retain the current authoritative per-symbol signature table, compare contract owners and resolve divergent ABI declarations; do not raise ceilings or bypass the push gate.

## sffi_manifest_signature_native_test_compile_cost_2026-08-21 — SFFI manifest-signature native test compile cost

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sffi_manifest_signature_native_test_compile_cost_2026-08-21.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:681; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:995
```
- Review rationale: The report observes multi-minute closure compilation before any Ed25519 execution, with one completed attempt failing in fixture HIR. Current explicit-AOT runner builds with --entry-closure and a generated entry, and cleanup_native_generated_files can remove the per-executable cache unless artifacts are retained. This shows concrete cache/closure policy relevant to the complaint, but does not measure which current phase dominates or prove cache retention would cure the broad closure cost. Remaining evidence: Capture source-bound setup/compile/link/execute timing and cache keys for the leaf signature spec; retain golden signatures and keep verification on admission paths.
- Review corrections: Queue validity=valid replaced by uncertain after independent report and owner review; see rationale.

## sffi_u8_return_nil_and_cross_engine_len_2026-08-18 — SFFI `-> [u8]` siblings: interpreter binds `nil`, and `rt_bytes_alloc` length disagrees across engines

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sffi_u8_return_nil_and_cross_engine_len_2026-08-18.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:1284; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:1321; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/mod.rs:834; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1583; Target-ancestry history: 65484db025d
```
- Review rationale: The report retracts the old Option premise and tracks nil-on-read-error plus JIT allocation-length divergence. Current registered interpreter handler rt_file_read_bytes returns Value::Nil on fs::read error, while rt_bytes_alloc allocates packed byte storage, resizes to the requested positive length and returns that storage. The missing-file half therefore has direct current implementation support; no JIT length ABI trace or current execution establishes the other half. A one-handler change would not discharge the combined report. Remaining evidence: Trace JIT byte-array return/length ABI and restore both discriminating cases under a qualified runner before claiming a shared remedy.

## sha3_wrong_under_jit_while_kat_passes_2026-08-17 — SHA3 returns wrong digests under the JIT while its KAT passes 7/7

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sha3_wrong_under_jit_while_kat_passes_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/crypto/sha3.spl:267; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/crypto/sha3.spl:288; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/crypto/sha3.spl:341; Target-ancestry history: 62b3cd16d9e
```
- Review rationale: The report supplies ablation evidence that signed-wide-int unboxing was repaired while raw digest bytes still diverged; later hex output additionally depends on broken substring. Current SHA3 retains tuple context with nested integer lists; update reads tuple fields and returns updated lists, finalize emits requested bytes from lanes, and one-shot SHA3-256 chains those calls. This preserves the report meaningful aggregate-boundary lead, but reading the algorithm does not establish a JIT return-marshalling root or permit crediting the wide-int fix for SHA3. Remaining evidence: Trace current tuple/list return ABI and retain direct-byte cross-engine oracle with demonstrated execution mode; avoid substring-based digest evidence.

## simd_lane_ops_reject_f32_cast_values_2026-08-25 — `std.simd` lane ops reject values produced by `as f32` (2026-08-25)

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fix_candidate`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simd_lane_ops_reject_f32_cast_values_2026-08-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/simd.rs:524; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/simd.rs:596; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/simd.rs:865; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/simd.rs:1110; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/value.rs:2886; Target-ancestry history: 9ecc62bf608
```
- Review rationale: The actual current mul_f32x4 entry calls binop_f32x4, which unpacks Vec4f through require_f64_field for each lane. That common converter accepts only Value::Float and Value::Int; the type model separately defines Value::Float32(f32), which reaches the error arm. The same converter serves f32x8 and f64 siblings. A bounded remedy is to accept Float32 and widen its f32 payload to f64 in this common extractor; unpack_vec4f already performs the final f32 conversion. No ownership/phase contract change is required. Remaining evidence: Test cast-produced Float32 vectors across arithmetic/FMA/sibling ops and retain invalid-field rejection; no runtime qualification was performed.
- Review corrections: Current exact entry-to-converter analysis supports known/no/fix_candidate instead of unknown remedy. The report Float64 wording is not the current enum spelling; Value::Float is f64.

## simple_check_diagnostics_contract_raw_parser_error_not_stable_format_2026-07-20 — simple check prints raw legacy parser text instead of error[Exxxx]; all 10 contract exa...

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_check_diagnostics_contract_raw_parser_error_not_stable_format_2026-07-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/check/main.spl:248; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/cli/check.rs:229; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/02_integration/app/diagnostics/check_diagnostics_contract_spec.spl:44; Target-ancestry history: 6dcc157f07d
```
- Review rationale: The report admits competing formatter-regression versus aspirational-contract explanations. Current integration test really invokes a deployed CLI and asserts E0002, expected/found and help strings; it is not merely documentation. Current Simple check parses then prints raw path/error strings, with a separate semantic result path. The Rust check owner instead builds structured CheckError values and converts ParseError. This supports a real cross-entry output-contract gap while leaving exact deployment dispatch and per-kind parity unresolved. Remaining evidence: Bind the deployed check entry to its source producer and compare each diagnostic kind against the current contract; the fixed Linux binary path in the fixture also limits portability.

## simple_check_segfaults_on_hello_world_2026-09-01 — `simple check` SEGVs on a two-line hello world

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_check_segfaults_on_hello_world_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/main.rs:91; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/cli/check.rs:93; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/cli/check.rs:229
```
- Review rationale: The report has a fresh Windows seed two-line check SEGV with a same-binary run control and explicitly distinguishes native module-init/CRT crashes. Current Rust check owner reads source, calls Parser::new/parse, then import, boundary, annotation and concurrency validators; read and parse failures become structured results. No observed source branch identifies where the reported native crash occurred. Current Simple check code would be a different implementation and cannot close the seed report. Remaining evidence: Collect exact Windows binary identity and stack for check versus run, locating the first failing frame before selecting a fix or inferring platform scope.
- Review corrections: Queue validity=valid replaced by uncertain after independent report and owner review; see rationale.

## simple_cli_invocation_attempts_user_gitconfig_lock_2026-09-09 — Simple CLI invocation attempts to lock the user's .gitconfig during a read-only smoke probe

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_cli_invocation_attempts_user_gitconfig_lock_2026-09-09.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/main.rs:1172
```
- Review rationale: The report contains no retained invoking argv or lock trace and later explicitly labels environment attribution a hypothesis. Current main sets a stack guard, starts real_main on a large-stack thread or invokes it directly for GUI mode; this entry logic does not establish a Git-config writer. Scoped searches and entry inspection do not prove absence through wrappers or subprocesses. Conservative uncertainty is supported: the claimed host effect is not disproved, but no compiler-source attribution or root remedy is established. Remaining evidence: Capture Windows process ancestry, exact argv/executable and pre/post config/lock identity; distinguish wrapper/environment behavior from compiler behavior.

## simple_compiler_select_promotes_stage2_binary_without_run_subcommand_2026-08-06 — simple-compiler-select promotes a stage2 bootstrap CLI that answers `run` with unknown...

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_compiler_select_promotes_stage2_binary_without_run_subcommand_2026-08-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/lib/simple-compiler-select.shs:35; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/lib/simple-compiler-select.shs:191; Target-ancestry history: 88aac2ffe28
```
- Review rationale: The report amendment retracts the fail-open interpretation of two rejected crashing candidates; the surviving issue is advertised run capability versus measured check/native-build. Current selector still probes check p.spl then real native-build --entry p.spl and can accept a compilation-capable candidate without running source. That is concrete contract evidence independent of old bootstrap dispatch line numbers. It cannot establish that a present admitted full CLI exists or that adding a selector flag alone supplies one. Remaining evidence: Trace current run-dependent callers into explicit capability admission and qualify a full CLI; preserve candidate crash rejection and do not weaken guard requirements.
- Review corrections: Retain the report retraction: rejecting two crashing candidates is sound, not invalidity of the remaining run-capability problem.

## simple_frontend_profile_runtime_unavailable_2026-09-03 — Tiny frontend profiling unavailable in admitted release runtime

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_frontend_profile_runtime_unavailable_2026-09-03.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/check/main.spl:224; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/check/main.spl:248; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/check/main.spl:267
```
- Review rationale: The report records failed tiny run/check/compile/optimizer invocations on a macOS rc.1 artifact, not measured frontend slowness. Current Simple check has phase marks around preflight, scope setup, source read, parse, lint and semantic analysis and records failure outcomes. Those are useful instrumentation surfaces, but their presence is not evidence the report artifact can execute them or that a current producer-authenticated runtime has succeeded. No bottleneck or performance repair is established. Remaining evidence: Obtain admitted source/binary receipts and successful tiny fixture plus phase counters before timing frontend work or recommending an optimization.
- Review corrections: Queue validity=valid replaced by uncertain after independent report and owner review; see rationale.

## simple_lint_ast_rules_unwired_2026-07-19 — Production `simple lint` omits semantic AST rules

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_lint_ast_rules_unwired_2026-07-19.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/lint/main.spl:24; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:250; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:285; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:327; Target-ancestry history: 548babb5977
```
- Review rationale: The report describes an implemented ARG/COLL/STUB/W0404 slice but still-pending wildcard leaves. The actual CLI facade exports the parsed-owner entry points, and current owner calls argument, collection and stub checks, filters STUB to 001/002 to avoid duplicate 003, and now calls check_star_export_file with policy/source location handling. W0406 imports are assigned to the EasyFix owner rather than duplicated. This is material progress beyond the report, but complete CLI/query parity and non-vacuous current binary evidence remain unverified. Remaining evidence: Review the wildcard-import EasyFix and query/LSP split with real missing-rule fixtures, then qualify Stage4; presence of dispatch does not establish complete semantic lint coverage.
- Review corrections: The pending wildcard-export statement is stale: current parsed adapter invokes check_star_export_file. Do not close the whole report from this partial source progress.

## simple_mcp_windows_source_startup_blocked_by_transport_jit_and_shared_stderr_2026-09-09 — Simple MCP Windows source startup is not concurrency-safe and cannot be verified

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_mcp_windows_source_startup_blocked_by_transport_jit_and_shared_stderr_2026-09-09.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:bin/simple_mcp_server.cmd:20; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:bin/simple_mcp_server.cmd:88; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:bin/simple_mcp_server.cmd:106; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/mcp/main.spl:19; Target-ancestry history: 88aac2ffe28
```
- Review rationale: The report separates shared stderr locking, generic transport ambiguity and an unadmitted disabled executable. Current CMD verifies native hashes, defaults source execution to interpreter, supports inherited stderr, atomically claims a unique log directory with mkdir and appends stderr there. The source entry imports protocol framing/envelope owners rather than the reported server.app extraction dependency. These directly address the recorded contention/dependency shape, but fallback still permits seed paths and does not supply an admitted native server or current two-instance initialize evidence. Remaining evidence: Build/identify admitted Windows runtime/server and retain two simultaneous initialize responses with per-instance logs; do not rename the old disabled artifact into service.
- Review corrections: The process-global stderr redirect is no longer current source behavior. Partial wrapper/source changes must not be confused with native qualification.

## simple_pipe_codebase_duplicate_scan_2026-08-24 — `simple_pipe` codebase duplicate scan and child startup

- Source receipt: `adjudication_v2_21`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_pipe_codebase_duplicate_scan_2026-08-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/mcp/main_lazy_query_tools.spl:511; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/mcp/main_lazy_query_tools.spl:550; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl:464; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl:484; Target-ancestry history: bf33c11dd6e; a5bec06f5e3
```
- Review rationale: The report defines independent raw regex and workspace-symbol contracts and requires watcher-authoritative freshness before caching. Both current provider handlers still call _simple_pipe_search_text and _simple_pipe_workspace_symbols separately for one request; the workspace helper launches query.spl in a child (argv in app provider, shell in lib provider). Parent result assembly uses arrays/join, which mitigates copying but leaves the distinct producer startup. This substantiates the live duplicated-provider shape without asserting a proven compatible index remedy or current latency numbers. Remaining evidence: Trace child query traversal and prove cap/order/error compatibility plus watcher loss fallback before replacing the producer; measure source-bound cold/warm latency and child counts.

## simple_ring_async_base_open_evidence_2026-08-26 — SimpleRing async-base open evidence

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_ring_async_base_open_evidence_2026-08-26.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/async_ring/simple_ring.spl:123; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/desugar/desugar_async.spl:268
```
- Review rationale: The report distinguishes hosted steady-state safety from placement, polling, concurrency and runtime qualification. SimpleRing.create constructs dynamic arrays and pushes capacity entries; desugar_await_expr still emits block_on. Neither establishes fixed placement or universal polling. Retain the open qualification record; allocation traces, delayed-I/O progress and model/performance receipts remain absent.
- Review corrections: No runtime or allocation-free claim follows from the finite trace count.

## simple_test_default_runner_silent_vacuous_pass_2026-09-06 — `bin/simple test <spec>` exits 0 with NO output at all, and the Rust runner caches by spec mtime only

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_test_default_runner_silent_vacuous_pass_2026-09-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/no_examples_gate.spl:36; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/cli/test_runner/result_cache.rs:74
```
- Review rationale: The full report records two distinct false greens. The cache check compares only spec mtime and size, and recording persists those same values, so dependency edits remain invisible to that key. A no-verdict helper converts rc=0 to failure, but this does not establish that the report's exact single-spec dispatch executes it. A transitive dependency fingerprint is a concrete cache remedy; the silent dispatch cause still requires its own trace.
- Review corrections: Downgrade research known/no/fix_candidate for the composite record: the cache remedy does not diagnose the independent silent runner path.

## simple_test_nested_runner_timeout_2026-06-28 — A spec that shells out to a nested `bin/simple test` times out the outer test daemon

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_test_nested_runner_timeout_2026-06-28.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/daemon_backlog.spl:25; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_client.spl:204
```
- Review rationale: The report supplies a nested-wrapper daemon timeout and a fast direct child, then rejects later Windows timeout results as unusable. Current daemon policy documents a serialized FIFO with blocking child execution; client lock identity checks use PID/cmdline. These are relevant contention mechanisms, not a demonstrated nested-call diagnosis or isolation fix. A source-contract workaround cannot replace paired direct/nested execution evidence.
- Review corrections: No inference of current reproduction from historical timeout or shared queue policy.

## simple_web_html_layout_renderer_layout_paint_coverage_gap_2026-08-07 — Layout renderer line coverage measured 40% against a 90% target, a 50-point gap

- Source receipt: `adjudication_v2_22`; inspection `report_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_web_html_layout_renderer_layout_paint_coverage_gap_2026-08-07.md
```
- Review rationale: The complete report supplies measured instrumentable-line denominators and remaining 35-54 percent coverage, after slow_it unblocked measurement. This is valid coverage debt, explicitly broader than a discrete product defect. No target-matched hit-line artifact or newly executed coverage matrix was reviewed, so the historical percentages are not current measurements and no single root remedy is accepted.
- Review corrections: Correct research evidence reference to the actual .md report; tracking scope and dead-code notes do not support invalid closure.

## simple_web_layout_corpus_perf_2026-05-31 — famous_site_corpus_spec takes 86222ms and the runner flags it PERF BUG

- Source receipt: `adjudication_v2_22`; inspection `report_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_web_layout_corpus_perf_2026-05-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/gui/wm_compare/famous_site_corpus_spec.spl:10
```
- Review rationale: The report corrects the moved corpus path and explicitly rejects the 29-second Windows outer-timeout result. The current fixture imports the corpus builders, layout report and production renderer, consistent with the moved workload. The last usable reported 86215ms result is historical; neither a current profile nor a bottleneck-specific remedy is established.
- Review corrections: Do not count path migration or a runner failure as improved layout performance.

## simple_web_text_decoration_geometry_clip_2026-06-25 — text-decoration-thickness and text-underline-offset produce no visibly changed pixels due

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_web_text_decoration_geometry_clip_2026-06-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_raster.spl:54; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_raster.spl:1054
```
- Review rationale: The report records failed differential thickness/offset pixels with stable underline color. Current raster painting actually consumes offset and scaled thickness in fb_text_underline_clip, using the inherited paint clip whose ancestor overflow rules intersect box bounds. Thus properties reach painting, beyond mere style serialization, but this does not prove adequate decoration ink bounds or reproduce the reported clipping. Exact differential pixel fixtures remain required.
- Review corrections: Replace research field/serialization-only evidence with the actual raster call and clip construction; keep the suspected root cause unknown.

## simple_web_textarea_overlay_review_hard_stop_2026-07-27 — Simple Web textarea overlay review hard stop

- Source receipt: `adjudication_v2_22`; inspection `report_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_web_textarea_overlay_review_hard_stop_2026-07-27.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:31; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_raster.spl:54
```
- Review rationale: The full report describes rejected, unintegrated candidate commits, not a measured production defect. Its two rejection reasons are concrete: Draw IR depending on a CPU painter and feature-local text externs. Current renderer imports the common BrowserTextInputOverlay contract and has shared clip machinery; those observations do not establish candidate integration or the complete textarea graph. Accept a conservative uncertain disposition, retaining exact candidate graph/facade and CRLF/RTL/selection qualification as the next evidence.
- Review corrections: Downgrade validity to uncertain and inspection to report_reviewed: the proposed adapter tag check and resolved-text helper do not adjudicate the rejected candidate dependency graph. No invalidity or fix is inferred.

## simple_web_textarea_overlay_review_hard_stop_2026-07-27_tldr — Simple Web textarea overlay hard stop — TLDR

- Source receipt: `adjudication_v2_22`; inspection `report_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_web_textarea_overlay_review_hard_stop_2026-07-27_tldr.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simple_web_textarea_overlay_review_hard_stop_2026-07-27.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:31
```
- Review rationale: The full report and TLDR name the same three rejected commits, two final ownership blockers and absent execution. The obsolete heading identifies duplication, not falsity. The current common overlay import cannot establish integration of that rejected multiline candidate. Retain the same conservative uncertain disposition as the full report, pending exact candidate/current graph and regression evidence.
- Review corrections: Duplicate is not invalid. Mirror the full-report scope correction rather than accepting current textarea behavior from an obsolete heading.

## simpleos_arm64_el0_server_syscall_and_virtio_net_gap_2026-08-14 — _forward_net_ipc unconditionally returns -38 so mounted EL0 apps cannot bind/listen/accept

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_arm64_el0_server_syscall_and_virtio_net_gap_2026-08-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/abi/syscall_shim_net.spl:100; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/abi/syscall_shim_net.spl:114
```
- Review rationale: The report's handoff supersedes the original unconditional ENOSYS attribution. Current net_socket routes through portable_net_dispatch_v1 after capability validation and net_bind invokes portable_net_bind_args_checked_v1 with scheduler/IPC ownership. This confirms source progress at the POSIX boundary, not a complete ARM SVC/descriptor lifecycle or host-visible NIC/block durability result. Keep the composite qualification gap open.
- Review corrections: Do not characterize the active syscall route solely by the historical syscall_net stub.

## simpleos_arm64_qmp_input_transport_missing_2026-07-24 — SimpleOS ARM64/RV64 QMP input transport evidence gap

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_arm64_qmp_input_transport_missing_2026-07-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/compositor/arm64_virtio_input_backend.spl:286
```
- Review rationale: The full report distinguishes ARM MMIO and RV modern PCI source paths, plus RV font/block reachability. Current shared backend requires the readiness mask and pumps bounded raw events into feed_raw_event; unavailable producers do not masquerade as an idle queue. This establishes a relevant consumer contract, not current-ELF QMP/device/state/frame delivery or RV font integration. Target-specific correlated capture remains required.
- Review corrections: No UART, host nonce, backend declaration or idle queue is admitted as live input evidence.

## simpleos_artifact_manifest_signer_safe_io_zeroization_blockers_2026-08-24 — SimpleOS artifact manifest signer safe-I/O and zeroization blockers

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_artifact_manifest_signer_safe_io_zeroization_blockers_2026-08-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/crypto/ed25519.spl:519; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/crypto/ed25519_scalar.spl:21
```
- Review rationale: The full report updates safe-I/O and typed wipes while retaining nested signing-workspace debt. pure_ed25519_sign allocates seed hash, clamped scalar, prefix and prefix-message arrays and calls scalar/point operations; scalar conversion/subtraction allocates more arrays. Top-frame seed wiping cannot account for these secret lifetimes. The necessary coordinated ownership/cleanup contract is structural, but a complete causally verified root remedy is not yet demonstrated.
- Review corrections: Keep typed wipe progress distinct from whole-operation erasure; safe-I/O draft claims remain unadmitted.

## simpleos_baremetal_backend_resolve_empty_override_rt_process_run_trap_2026-08-11 — After metal/cuda/rocm probes are fixed, boot dies in 21 repeated FAULT @ 0x49bacXXX (ca...

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_baremetal_backend_resolve_empty_override_rt_process_run_trap_2026-08-11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_qualcomm.spl:64; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_qualcomm.spl:249
```
- Review rationale: Full report reviewed, including superseded sections. QualcommBackend.create now derives compile-target architecture/bits; x86 gets zero bits and init rejects it before invoking Vulkan. This is the proposed source repair for the post-ROCm fault, but the report explicitly calls the attribution a leading explanation without exact instruction/serial correlation. Empty-override and shell-trap historical progress must not close the remaining CPU fault.
- Review corrections: Residual investigation completed at the actual Qualcomm owner, replacing the research pass's unrelated web_render_backend/runner references; aggregate remedy remains unknown.

## simpleos_checksum_target_artifact_admission_gap_2026-08-20 — SimpleOS checksum target artifact admission gap

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_checksum_target_artifact_admission_gap_2026-08-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/services/launcher/launcher_checksum_tool_gate.spl:22
```
- Review rationale: The report tracks target artifact authority, not hashing correctness. Current checksum launcher resolves package identity then returns blocked with CHECKSUM_TOOL_TARGET_ARTIFACT_TOKEN_UNAVAILABLE; it cannot proceed to legacy spawn. Exact native bytes, digest-bound consume-once lookup and operand-scoped FileRead delegation still need proof. A correct rejection does not invalidate the missing prerequisite.
- Review corrections: Replace checksum implementation-only evidence with the actual launcher boundary.

## simpleos_dbd_dbfs_tls_auth_gap_2026-08-20 — SimpleOS dbd DBFS, TLS, and authentication gap

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_dbd_dbfs_tls_auth_gap_2026-08-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/dbd/dbd_protocol.spl:42; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/dbd/dbd_launch.spl:62; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/crypto/entropy_platform.spl:7
```
- Review rationale: The full report contains superseding credential/DBFS progress followed by an older entropy append. Current private facts mark auth/framing true and TLS/DBFS false; startup_blocker returns tls-owner-unavailable, and launch checks readiness before Ready. The declared rt_entropy_fill remains a call in entropy_platform with no match in the scoped runtime searches, but no universal provider-absence claim is needed. Provisioning, provider/durability execution and wipe qualification remain unresolved.
- Review corrections: Reject stale boot-credential-first diagnosis. Structural change remains unknown rather than deriving necessity from subsystem breadth or old closure lists.

## simpleos_direct_lfb_blend_span_qemu_gate_2026-08-12 — Direct-LFB blend-span gate reports skip: SIMPLEOS_KERNEL_ELF unset, so no boot evidence...

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_direct_lfb_blend_span_qemu_gate_2026-08-12.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/drivers/framebuffer/fb_driver.spl:521; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/x86_64/boot/direct_lfb_blend_span.h:11
```
- Review rationale: The report corrects its earlier absent-x86 implementation claim and explains registry A versus driver B mismatch. Current caller passes address/width/height/pitch to span8; the C owner compares them against its registry before destination access, bounds source/count/row arithmetic and preserves transparent zero-access behavior. This is a concrete present remedy. Base compilation, exact guest route/readback and 8K measurements remain unverified.
- Review corrections: Change structural_change from no to yes: the remedy changes the caller/provider ABI to carry destination identity; static fill or hosted evidence is not guest blend execution.

## simpleos_fabricated_rt_guard_weak_real_false_positive_2026-07-28 — Fabricated-`rt_*` link guard misclassifies weak-but-real definitions — blocks landing

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_fabricated_rt_guard_weak_real_false_positive_2026-07-28.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/simpleos_native_guards.spl:147; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/simpleos_native_symbols.spl:273; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/simpleos_native_trivial_body.spl:500; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:config/simpleos_fabricated_rt_baseline.sdn:75
```
- Review rationale: The report's weak-binding false-positive cause has a present local remedy: the guard builds real definitions from an any-binding scan minus body-classified constants, instead of reusing the weak-dropping helper. The baseline regeneration description matches that body-aware set and records per-entry measurement. This supports source-fixed pending current exact-entry qualification, without allowing all weak symbols or widening baseline debt.
- Review corrections: Historical baseline counts and measurements remain historical; no current link PASS or uninspected commit-title proof is accepted.

## simpleos_fat32_transactional_mount_owner_blocked_2026-08-24 — FAT32 transactional mount owner is blocked on device and operation ownership

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_fat32_transactional_mount_owner_blocked_2026-08-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/fs/_Fat32Filesystem/mount_owner.spl:4; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/fs/fat32_boot_capsule_binding_owner_v1.spl:25; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/boot/boot_fs_mount.spl:303
```
- Review rationale: Full report reviewed through the fourth rejected draft. Current capsule binding creates identity/capsule registrations and publishes a seal, but boot_fs_mount has only its import and still calls legacy fat32_mount_publish. The legacy owner stores filesystem, device and readiness separately and exposes separate readers. Capsule presence therefore cannot close production lifecycle/identity/operation ownership. Structural integration is required; its complete safe remedy remains unknown.
- Review corrections: Retain the fourth draft and production-use distinction; an unused import is not authenticated mount adoption.

## simpleos_filesystem_durable_sync_barrier_gap_2026-08-20 — SimpleOS filesystem durable-sync barrier gap

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_filesystem_durable_sync_barrier_gap_2026-08-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/fs_driver/mount_table.spl:1805
```
- Review rationale: The full report distinguishes portable FAT32/DBFS/NVFS recovery from mounted namespace and SimpleOS synchronization admission. Current fsync/fdatasync checks the active mount's DurableSync before invoking its driver and otherwise returns Unsupported. This is truthful capability dispatch, not proof of device flush or power-loss durability. Binding mounted namespace mutations and synchronized ingress to the durable owner remains a structural obligation; real per-target flush/remount evidence is absent.
- Review corrections: No positive counter, in-memory LSN, hosted mutex or capability bit is treated as hardware durability.

## simpleos_freestanding_kernel_elf32_wrap_and_weak_gate_overbroad_2026-08-06 — In-guest /usr/bin/simple hello.spl exits rc=70 with str.clear on a non-text receiver=0x0

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_freestanding_kernel_elf32_wrap_and_weak_gate_overbroad_2026-08-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:3499; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-simpleos-x86-kernel-elf.shs:78; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:6684
```
- Review rationale: Full composite report reviewed. ELF32 wrapping is opt-in and the weak-symbol opt-in is restricted to designated syscall fallback names/functions. The separate in-guest rc70 symptom remains undiagnosed. Current runtime diagnostic expressly says raw zero may be integer zero or unwritten storage; it refuses rather than substitutes. Neither that guard nor the two titled fixes localizes the offending clear call or proves a present module-init failure.
- Review corrections: Correct the report/research inference that receiver=0x0 proves an uninitialized collection: current source explicitly preserves integer-zero ambiguity. Do not close the composite on the two titled repairs.

## simpleos_freestanding_nil_array_init_optimizer_guard_fold — Freestanding one-binary builds never run module-global array initializers; nil reaches

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_freestanding_nil_array_init_optimizer_guard_fold.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:1340; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:2821; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/entry_closure_global_init_tests.rs:6
```
- Review rationale: Full report reviewed and successor native linker traced. The current freestanding path calls generate_init_caller; it discovers module-prefixed dynamic initializers and emits __simple_call_module_inits. The regression file distinguishes the entry-wrapper initializer loss from already-handled library globals. Therefore a blanket present absence of global initialization is unsupported. No matching optimized i64-guard IR or source-bound guest failing artifact was reviewed, so accept uncertain/unknown rather than promote either historical root attribution or scratch fixes.
- Review corrections: Residual now meaningfully investigated beyond generic C codegen. Downgrade current validity to uncertain; missing scratch is not invalidity, and init-caller generation alone is not runtime closure.

## simpleos_harden_probe_build_target_2026-06-28 — Harden probe ELF and FAT32 image targets do not exist so AC-1/2/8/9/10 specs are

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_harden_probe_build_target_2026-06-28.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/build-simpleos-nvfs-positioned-qemu.shs:20; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/qemu_systest_contract.spl:496; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/x86_64/harden_probe_entry.spl:29
```
- Review rationale: The producer now selects a harden-probe entry/artifact and the contract has firmware arguments. However the actual entry only checks a capability predicate and reports live capability enforcement UNAVAILABLE, allocator traps UNAVAILABLE, and PIE/RELRO/SSP UNVERIFIED. The report's substantive AC-1/AC-2/hardening witnesses are not implemented merely because build paths exist. Keep open for the missing executable probe owners and then admitted firmware execution.
- Review corrections: Reject research known/no/fixed_pending_verification: the actual producer body contradicts implementation-complete classification.

## simpleos_harness_silent_native_build_2026-07-26 — WM harness emits zero output during 2h+ kernel build because trace gates are never

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_harness_silent_native_build_2026-07-26.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/lib/simpleos-wm-fullscreen/build.shs:1; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/lib/simpleos-wm-fullscreen/build.shs:122
```
- Review rationale: The report separates guest log mode from compiler progress and buffered subprocess output. Current build component prints a timestamped stage and enables phase profiling, while an independent poller emits active-attempt/log-byte heartbeats to stderr during the child. This directly remedies harness-wide total silence even if compiler output buffers. Actual redirected long-build progress and any alternate capture path remain untested; no compiler-flush fix is claimed.
- Review corrections: Scope known remedy to the inspected harness heartbeat, not universal subprocess streaming or per-module live flushing.

## simpleos_http_ssh_capability_manifest_unwired_2026-08-21 — HTTP and SSH capability manifests are not wired to production owners

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_http_ssh_capability_manifest_unwired_2026-08-21.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/http_server/server.spl:540; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/sshd.spl:592; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/contracts/execution/simpleos_server_protocol_capabilities.spl:38
```
- Review rationale: Current HTTP owner projects manifests after readiness/probe identities and worker request-response evidence. SSH accept paths call the consuming probe publisher, which binds generation/sequence/authority and withholds SFTP by passing owner_ready=false. Factories omit H3/WebTransport/WebSocket. This repairs the reported absence of production-owner projections at source level; fresh protocol/auth/channel and configuration-bound evidence is still required, with no unsupported protocol readiness claim.
- Review corrections: No live protocol PASS inferred from factories or standalone specs.

## simpleos_initramfs_role_digest_validation_gap_2026-08-20 — SimpleOS initramfs role/digest validation gap

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_initramfs_role_digest_validation_gap_2026-08-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/port/initramfs_validate.spl:259; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/loader/cpio_newc.spl:78; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/os/port/initramfs_pack_archive_validation_spec.spl:261
```
- Review rationale: The role validator resolves exact allowed guest paths, checks payload hashes, rejects duplicates/missing roles and requires distinct role digests. The bounded newc parser rejects malformed headers and unsafe paths; behavioral specs include canonical archive and malformed-header cases. These are concrete present source remedies matching the report's bounded raw/RLE zstd scope. Runtime archive, canonical image and in-guest toolchain qualification remain untested.
- Review corrections: Unsupported sequence-compressed zstd is a deliberate fail-closed limitation, not a claimed complete decoder.

## simpleos_loader_owned_image_token_gap_2026-08-20 — SimpleOS loader-owned image execution authority gap

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_loader_owned_image_token_gap_2026-08-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/loader/executable_admission_pipeline.spl:239; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/loader/executable_admission_pipeline.spl:303; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/loader/executable_manifest_signature_verifier.spl:164; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/loader/installed_artifact_catalog_boot_owner_v1.spl:163; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/loader/fs_exec_spawn.spl:259
```
- Review rationale: The old report is superseded at source level: admission calls a real canonical-payload Ed25519 verifier, checks a private initialized trust capsule, and can issue a token; boot catalog population initializes trust roots. fs_exec also has scheduler authenticated adoption. Diagnostic retrieve_once still returns execution_authorized=false, but that is not the only execution path. Exact production boot provisioning, consume/replay/close-retry and cross-architecture ownership qualification were not established; keep the historical authority gap open without claiming the verifier is absent.
- Review corrections: Correct research's missing-verifier/unobtainable-token inference and stale no-scheduler seam. Remaining structural work is unknown because substantial contracts already exist.

## simpleos_native_performance_campaign_runtime_admission_blocked_2026-08-20 — SimpleOS native performance campaign blocked by runtime admission

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_native_performance_campaign_runtime_admission_blocked_2026-08-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/contracts/execution/simpleos_performance_v1.spl:323
```
- Review rationale: The report requires admitted test/run authority and raw comparable campaign samples. Current admission checks sample/RSS counts, warmup, canonical budgets, fixture/binary/image/config/baseline identities and Native host, rejecting non-native samples. This enforces the evidence contract but produces neither samples nor runtime authority. Retain the legitimate operational qualification blocker with no root code remedy or benchmark PASS.
- Review corrections: No compile-only Stage2, seed or QEMU result is promoted to native campaign evidence.

## simpleos_physical_board_bringup_hardware_blocked_2026-08-11 — No physical SimpleOS board in this environment so every board-runnable claim stays

- Source receipt: `adjudication_v2_22`; inspection `report_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_physical_board_bringup_hardware_blocked_2026-08-11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/machine_profile.spl:17
```
- Review rationale: The complete report distinguishes USB image software preparation from actual board boot and later provenance-gate repair. MachineProfile still records QEMU machine/CPU/firmware fields; that is not a selected physical-board receipt. No same-boot image/controller/native GPU/NIC/capture evidence was supplied for this review. Keep the hardware qualification item open; neither an image checker nor rejection of QEMU provenance demonstrates physical bring-up.
- Review corrections: No inference that unselected hardware or an operational prerequisite is an invalid bug.

## simpleos_privileged_load_consumer_gap_2026-08-20 — SimpleOS privileged executable load consumer gap

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_privileged_load_consumer_gap_2026-08-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/loader/executable_admission_pipeline.spl:239; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/loader/executable_manifest_signature_verifier.spl:164; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/loader/fs_exec_spawn.spl:259
```
- Review rationale: The report's absent verifier and scheduler adoption statements are stale: real signature verification/token issuance and fs_exec authenticated scheduler adoption exist at the target. The compatibility retrieval is explicitly non-authorizing, which must not be generalized to every receipt. No current mapped-lease transfer, release-failure/replay or ARM/RV whole-space reclamation qualification was inspected. Accept the historical incomplete-consumer qualification as open, with current completeness and remaining remedy unknown.
- Review corrections: Correct research's blanket missing-verifier conclusion and retain the source adoption seam; structural_change becomes unknown rather than assuming every old architectural gap remains.

## simpleos_process_tool_target_artifact_admission_gap_2026-08-20 — SimpleOS process tool target artifact admission gap

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_process_tool_target_artifact_admission_gap_2026-08-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/services/launcher/launcher_process_tool_gate.spl:17
```
- Review rationale: The process report tracks executable admission beyond PM snapshot functionality. Actual launcher dispatch resolves the canonical package but returns PROCESS_TOOL_TARGET_ARTIFACT_TOKEN_UNAVAILABLE; it has no successful spawn branch. Native package bytes, digest/token binding and per-target filesystem launch/filter/error/latency evidence remain unresolved. This supports keeping a valid artifact boundary issue open without characterizing the process listing code as broken.
- Review corrections: Replace coreutils-wrapper-only evidence with actual launcher refusal logic.

## simpleos_qemu_virtio_serial_host_gpu_transport_2026-07-30 — No VirtIO console device or framed host-GPU port exists so x86_64 and RISC-V have no

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_qemu_virtio_serial_host_gpu_transport_2026-07-30.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/service/extern.spl:16; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/drivers/virtio/virtio_console_queue_owner.spl:34; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-simpleos-qemu-host-gpu-2d.shs:1107
```
- Review rationale: Full report reviewed through the later queue-owner increment. A shared fixed queue lease owner now exists, but architecture adapters still own discovery/interrupt registration; the inspected Unix socket facade sends/receives text. The wrapper retains virtio-serial-unimplemented. Codec/session/queue foundations do not establish binary-safe endpoint, console device integration or WM framed transport. Those cross-owner interfaces are structural; live x86/RV correlated delivery remains absent.
- Review corrections: Correct the broad claim that there is no console queue owner: a generic queue owner exists, while device/endpoint/WM integration remains unproven.

## simpleos_riscv64_component_rows_lose_string_content_2026-08-31 — riscv64 in-guest component rows lose string CONTENT (mcp / caret / testrun)

- Source receipt: `adjudication_v2_22`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_riscv64_component_rows_lose_string_content_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c:335; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c:1616
```
- Review rationale: The full report separates successful closure/control flow from lost string content and notes the unchanged transcript after rt_index_get repair. Current concat checks HEAP_STRING and copies bytes; bytes_to_text checks array form, bounds length and converts raw/tagged slots. These relevant routines do not identify the first corrupt stage or prove the guest path correct. Keep unknown root remedy pending same-artifact in-guest length/first-byte probes through fetch, concat, bytes conversion and extraction.
- Review corrections: Strong symbol presence and cross-architecture success are not a current reproduction or root-cause proof.

## simpleos_scenario_runner_no_selfhosted_binary_deployed_2026-08-06 — os test --scenario fails with no runnable pure-Simple compiler because every candidate

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_scenario_runner_no_selfhosted_binary_deployed_2026-08-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/_QemuRunner/os_build_run.spl:381-500
```
- Review rationale: The report’s September correction is real at the target: version checking rejects both seed banners and the build selects one qemu_compiler_select_v1-admitted candidate before backend capability testing. LLVM uses _candidate_backend_smoke; candidate environment is pinned to prevent delegate substitution. This supports a deployment/admission blocker, not invalidity of the refusal. No current admitted candidate or tooling-passed guest receipt is available in this review; aggregate remedy and required structure remain unknown. Remaining evidence: Read the qemu_compiler_select_v1 admission owner and retain same-artifact LLVM canary and tooling-success receipt; no current deployment claim is made.
- Review corrections: September discovery repair supersedes the historical permissive candidate list; seed rejection is protective, not the defect.

## simpleos_server_credential_zeroization_gap_2026-08-14 — Server credential read into immutable [u8]/text has no compiler-resistant zeroization on

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_server_credential_zeroization_gap_2026-08-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/servers_user/main.spl:431-488; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/dbd/dbd_protocol.spl:270-319; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/crypto/secure_memory.spl:58-99
```
- Review rationale: Report sections 17-55 and 148-180 describe a corrected bytes/wipe path with host-only evidence. Current servers_user.provision_database_service uses DbdBootCredentialOwnerV1.admit_source, wipes the caller buffer and revokes on failure before provision_service_from_boot_owner. The boot owner streams bytes, wipes source, finishes digest, zeroizes workspace and only then configures the provider. secure_zero_u8_range performs byte volatile writes, a barrier, volatile readback and another barrier. This supersedes the report’s old provision_service raw-buffer flow. Signed ARM readback/artifact scan and complete generated target-code qualification remain absent; do not assert every copy is compiler-proof from facade source. Remaining evidence: Trace persistent stream zeroize implementation and ARM volatile code generation; retain signed guest and secret-scan evidence.
- Review corrections: Missing-primitive diagnosis is stale; target has a newer boot credential owner. Retain unknown aggregate solution because the target qualification and full workspace implementation were not established.

## simpleos_server_exit_cleanup_integration_blocker_2026-08-24 — SimpleOS server-exit cleanup integration blocker — 2026-08-24

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_server_exit_cleanup_integration_blocker_2026-08-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/scheduler/_Scheduler/scheduler_lifecycle.spl:240-266; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/scheduler/scheduler_task_mgmt.spl:318-339; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/fd_io.spl:542-619
```
- Review rationale: Completed the previously truncated report section50-128 and read production scheduler/finalize/FD owner. The report’s missing PreparingExit and task-only FD authority claims are stale: current exit_task_by_id publishes PreparingExit and removes ready state before finalize; FD cleanup uses lifecycle-bound leases and retained retry receipts. Nevertheless finalize discards the FD close count and grant result, and publishes Zombie after only architecture-specific terminal gates. FD cleanup can retain a live descriptor/retry receipt and still return a successful-close count. Thus the tracked terminal-cleanup integration gap is supported by an actual live caller/owner mismatch; cross-CPU and all-provider proof remains unresolved, not assumed from the state name. Remaining evidence: Trace cross-CPU task-quiescence, capability/DBD/namespace terminal receipts, one-shot publication and reap ownership; current inspected FD/scheduler boundary does not consume terminal disposition.
- Review corrections: Accept valid based on live discarded cleanup outcome, not lower worker capsule comments. PreparingExit and lifecycle-bound FD reservations now exist, superseding report absence claims. Scheduler owner bytes are identical between d805 inventory and c0 target.

## simpleos_simple_web_decode_string_fault_storm_2026-07-12 — Baremetal decode_string faults on heap-like tagged values so the canonical renderer

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_simple_web_decode_string_fault_storm_2026-07-12.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/function_lowering.spl:179-215; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2445-2525
```
- Review rationale: Read report evolution from array ABI guesses to demonstrated Path.starts_with misbinding and the September typed theme-helper mitigation. Current MIR reset_function_local_tracking clears per-function receiver/aggregate ownership tables explicitly addressing stolen primitive receivers; method_calls_literals proves declared/recovered Str before builtin handling and excludes custom owners from erased text fallback. These are causally relevant protections, but the inspected text-shape arm does not itself prove starts_with’s separate predicate route. Historical zero-fault evidence and fast production-path host fixture cannot qualify the current freestanding renderer. Conservative unknown solution/structure remains supported. Remaining evidence: Trace the starts_with predicate route and production theme caller, then retain current zero-exception three-frame guest receipt.
- Review corrections: Do not treat historical interpolation mitigation or later host fixture as current guest reproduction.

## simpleos_ssp_codegen_feature_lag_2026-06-28 — No stack-smashing protector anywhere: clang invocation lacks -fstack-protector-strong and

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_ssp_codegen_feature_lag_2026-06-28.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/compile/native.spl:104-109; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:907-916; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/_MirToLlvm/class_def.spl:365
```
- Review rationale: Read the entire amended SSP report, including historical Clang linkage/fault receipts and explicit unresolved Cranelift route. At target native_stack_protector_flags emits strong protection for hosted ELF/SimpleOS; core_codegen places naked/noinline first and sspstrong only otherwise, and class_def binds policy to SimpleOS, non-bare-metal and resolve_hardening.ssp. This disproves the old “nowhere” wording while leaving the aggregate backend/guest acceptance open. No broad solution follows from the hosted policy. Remaining evidence: Trace actual default native-build preset/backend mapping and emitted SimpleOS guard/failure linkage, then target runtime receipt.
- Review corrections: Historical no-SSP source claim superseded by present hosted policy; seed/Clang probes are not current reproduction.

## simpleos_syscall_mount_table_bypass_2026-08-24 — SimpleOS syscall MountTable bypass

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_syscall_mount_table_bypass_2026-08-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/ipc/syscall_file.spl:374-425,447-469
```
- Review rationale: The full report identifies mount bypass and unsafe prior integration rather than an approved generic VFS fix. Current _handle_file_open explicitly returns ENOSYS for authorized protected DBFS paths because production descriptors cannot bind the virtual object; ordinary paths use fat32_mount_fs.open_at/create_at and fat32_fd_register. Reads dispatch by FD_TYPE_FAT32 to fat32_fd_read_into. This directly supports the current backend integration gap. Its safe remedy spans pinned operations, generations and dup/close semantics not established here; solution/structural scope remain unknown. Remaining evidence: Trace shared open-file description owner, dup/close, mount epoch and operation pin contracts; verify FAT32 append/truncate prerequisites.
- Review corrections: Promote uncertain to valid for the demonstrated DBFS/descriptor gap, without accepting the rejected integration design.

## simpleos_target_struct_receiver_valid_missing_2026-08-11 — SimpleOS target codegen lacks `rt_struct_receiver_valid`

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_target_struct_receiver_valid_missing_2026-08-11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/simple_core/core_memory.spl:692-707; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/common/boot/freestanding_value_registry_impl.h:137-146; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/x86_64/boot/freestanding_value_registry.c:18; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/services/init/service_manager_main.spl:1-27
```
- Review rationale: Read the 28-line report: the recorded failure occurred while compiling a ServiceWatch receiver, and primitive PID1 arrays were a workaround. Target now defines rt_struct_receiver_valid both in simple_core.core_memory and in the shared freestanding registry; the x86_64 freestanding translation unit includes that registry. The shared implementation strips tags, rejects invalid offset/width and wraparound, and asks registered allocation containment. Thus literal symbol absence is stale, but compile-time host abort versus target linkage/representation remains unresolved. Current service_manager_main has evolved to catalog service spawning and includes DependencyContainment, so the old workaround description is not proof of a current successful build. Remaining evidence: Bind the target bundle’s linked registry and struct registrations to generated field accesses, then an admitted compile and freestanding receiver smoke.
- Review corrections: Current symbol implementations preclude repeating global absence; uncertain does not invalidate the historical abort.

## simpleos_text_tool_target_artifact_admission_gap_2026-08-20 — SimpleOS text tool target artifact admission gap

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_text_tool_target_artifact_admission_gap_2026-08-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/services/launcher/launcher_text_tool_gate.spl:21-42; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/shell/_ShellApp/run_loop.spl:250,312,559
```
- Review rationale: Full report tracks target-native grep bytes, digest, loader token and filesystem evidence rather than grep semantics. Current launcher_dispatch_text_tool_v1 unconditionally produces a blocked result for recognized package identities, including TEXT_TOOL_TARGET_ARTIFACT_TOKEN_UNAVAILABLE. Shell run_loop has live dispatch call sites in direct and expanded command flows. The missing admission path is therefore source-supported; merely filling in the package metadata or removing the gate is not an acceptable remedy. Remaining evidence: Trace canonical package producer and loader token minting, then target-specific bytes/digests and FAT32/DBFS/NVFS execution.
- Review corrections: Promote uncertainty to valid for the present blocked launcher branch; retain untested and unknown remedy.

## simpleos_toolchain_deployment_desktop_boot_blockers_2026-08-14 — Six named blockers (host CLI crash, target payload, guest lld, image manifest, desktop

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_toolchain_deployment_desktop_boot_blockers_2026-08-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/mir_lowering_types.spl:979-1024; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/mir_lowering_stmts.spl:695,924; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1752,2030
```
- Review rationale: Read all seven deployment rows and superseded/current compiler attempt ledgers, including overwritten mutable log limitation. Target copy_local_hir_type_metadata passes scalar IDs, finds source and destination in aligned arrays, rejects nil/zero source types and copies type/isolation/resource metadata locally; multiple MIR callers use it. This supports the narrow aggregate-copy containment while proving nothing about admitted Stage3/4, target lld, image receipts, desktop or physical board. The umbrella remains conservatively uncertain/unknown rather than an invented single fix. Remaining evidence: Current immutable Stage3/4 lineage plus same-run manifest, image and desktop receipts; original logs overwritten cannot be rehabilitated from their hash text.
- Review corrections: Do not promote focused scalar-copy repair or historical seed checks into aggregate closure; title’s six blockers is also stale relative to seven table rows.

## simpleos_vulkan_board_gap_venus_is_qemu_only — Venus is a command-forwarding protocol with no host on a physical board, so Vulkan has no

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_vulkan_board_gap_venus_is_qemu_only.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl:66-90; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/renderdoc/simpleos_board_vulkan_provenance.spl:46-69
```
- Review rationale: Read the full report including September integrity gate. Target Vulkan ICD explicitly reports no real device transport: _venus_device_available returns false and _venus_transport_send fails unavailable instead of issuing handles. The independent board admission API rejects PhysicalBoard plus VenusVirtioGpu and checks physical provenance. These source facts support the physical-board delivery gap and preserve the QEMU/board distinction. Historical host version claims are not current facts; a standalone provenance predicate is not an integrated physical GPU driver. Remaining evidence: Identify native board driver/transport caller and board-qualified device, submission/fence and render receipt; no native-board execution owner established.
- Review corrections: Promote uncertainty to valid for the demonstrated modeled/unavailable transport; do not treat integrity validation as a Vulkan implementation.

## simpleos_wm_4k_footprint_exceeds_heap_window_2026-07-14 — SimpleOS WM 4K regressed: DrawIR first-frame footprint exceeds the entire sub-384MB heap window

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_wm_4k_footprint_exceeds_heap_window_2026-07-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/drivers/framebuffer/fb_driver.spl:151-181
```
- Review rationale: Read all report corrections: original heap-window hypothesis was superseded by per-element concatenation O(N²), followed by separate compositor and NVMe failures. Current FramebufferDriver.from_scanout_raw constructs direct MMIO state with empty back_buffer and host_buffer; the historical _zero_u32_buffer no longer exists in scoped owned source. This source evolution removes the reported allocation from this constructor, but neither establishes all 4K renderer memory behavior nor resolves later VFS failures. Keep the historical defect valid without treating heap enlargement as the root repair. Remaining evidence: Compare historical zero-buffer removal diff and constructor callers with current 4K image; retain memory/continuation guest receipt separating downstream VFS failure.
- Review corrections: The title’s heap-layout diagnosis is superseded. Present direct-write constructor is not proof of full WM gate success.

## simpleos_wm_gate_provenance_reject_after_boot_chain_fixes_2026-08-04 — After the boot-chain fixes the WM gate still rejects every window with

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_wm_gate_provenance_reject_after_boot_chain_fixes_2026-08-04.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/compositor/simple_web_window_renderer.spl:569-619; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/compositor/engine2d_wm_frame_executor.spl:357-389
```
- Review rationale: Full report records empty material provenance and no exception frames, so the rejection was not a crash. Current simple_web renderer derives material provenance after backend execution, rejects material digest mismatch with an empty frame, and otherwise copies material kind/reason/digest into WmContentFrame. engine2d_wm_frame_executor calls wm_content_frame_web_provenance_valid once, logs the same rejection, and admits image resources only if valid and URI is unique. This establishes active producer/consumer flow but not whether the reported window3 empty-material condition persists. Remaining evidence: Trace material witness contents and validator cases for the exact production theme, then same-run three-window provenance and framebuffer evidence.
- Review corrections: Retain uncertainty instead of equating guarded source with successful provenance; historical guest-render-fault label described validation rejection.

## simpleos_wm_lane_not_board_runnable_2026-08-08 — No SimpleOS image exists in which a WM actually runs and renders; every gate is preflight

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_wm_lane_not_board_runnable_2026-08-08.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-kv260-simpleos-boot-release.shs:28-58
```
- Review rationale: Read initial no-WM claim and subsequent QEMU/physical-carrier corrections. Target KV260 wrapper now makes missing bitstream/kernel/image or USB presence BLOCKED with exit2, then invokes actual board bring-up and spec; thus the old exit0 vacuous skip is corrected in source. That does not establish board boot/rendering or erase the physical-board delivery requirement. The report itself records QEMU progress, so blanket current “no image anywhere” is unsupported. Remaining evidence: Bind physical target/bitstream/kernel and stable board identity to a fresh boot/serial/render receipt; QEMU is a distinct target.
- Review corrections: Vacuous exit0 subclaim is stale; no-board-hardware wording was already corrected in report. Overall board status remains untested/uncertain.

## simpleos_wm_render_lanes_blocked_on_pure_simple_bin_2026-08-19 — SimpleOS WM rendering evidence lanes blocked: no usable pure-Simple build binary

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_wm_render_lanes_blocked_on_pure_simple_bin_2026-08-19.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-simpleos-wm-fullscreen-evidence.shs:88-108; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/lib/simpleos-wm-fullscreen/admission.shs:557-606
```
- Review rationale: Full report distinguishes builder refusal from healthy historical firmware/input test. Current canonical wrapper sources dedicated admission/build/runtime/report owners. Admission rejects seed paths, missing/nonexecutable candidates, failed simpleos_admitted_runtime_verify_auto, failed version identity or seed banners, then hashes the selected binary. This is a real admitted-runtime prerequisite for rendering, not invalidity of the gate. No current admitted runtime plus desktop build/render receipt was reviewed, so generic bootstrap advice is not a concrete known fix. Remaining evidence: Obtain admitted lineage for the exact selected compiler and run canonical desktop build/render evidence; input-test success cannot substitute.
- Review corrections: Current refusal exits1, superseding historical exit0 fail record; absence of fresh builder qualification remains a valid dependency.

## simpleos_x64_ssh_live_banner_exchange_timeout_2026-06-29 — OpenSSH times out during banner exchange against the guest sshd; serial shows rt-net

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/simpleos_x64_ssh_live_banner_exchange_timeout_2026-06-29.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/ssh_session.spl:472-524; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/net/rt_net_socket_facade.spl:455-473,522-533
```
- Review rationale: Full report isolates pre-authentication banner/KEXINIT timeout. Current do_version_exchange sends through rt_net_send_ssh_banner, receives exact identification bytes, validates those bytes and closes on invalid data; it no longer retries a text take that could consume the following packet. Socket facade special-cases boot socket200 and otherwise resolves registry/os_fd, returning empty bytes for missing entry or readiness failure. These relevant paths explain remaining discrimination points, but do not identify which current socket or wire condition matches the historical nil branch. Remaining evidence: Bind the x64 runtime socket registry and boot TCP receive/send implementation to same-run OpenSSH banner/KEX transcript; no runtime test performed.
- Review corrections: Historical nil-receive observation is not current reproduction; current byte-only identification flow has evolved.

## smf_reader_memory_binding_decode_changes_exported_set_2026-09-19 — BUG: fixing `SmfReaderMemory.parse_binding` changes what `exported_symbols()` returns for a mixed-binding module

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/smf_reader_memory_binding_decode_changes_exported_set_2026-09-19.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/linker/_SmfReaderMemory/symbol_parser.spl:271-278; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/linker/_SmfReaderMemory/header_parser.spl:157-186; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/99.loader/module_loader_compat.spl:1396-1435,1498-1508; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/smf_writer.spl:525-540
```
- Review rationale: Read report’s intentional decode change and latent local-relocation risk. Target parse_binding widens u8 then correctly selects Global/Weak/Local. exported_symbols filters defined public/weak symbols, retaining all-local fallback only for legacy unmarked sections. The loader still ALLOCATES its symbols dictionary only from exported_symbols; it uses symbols_in_table_order to name relocation targets but then looks up addresses in that exported dictionary/global registry. Thus full-table naming alone does not repair local target availability. Inspected smf_writer.build_symbol_entry still emits binding byte1; this bounds that writer but does not prove every writer emits Global. Remaining evidence: Trace all SMF writers and construct mixed local/public relocation fixture for admitted runtime; assess allocation/address-map versus public export separation.
- Review corrections: Promote uncertainty to valid latent consumer risk; ordered relocation names do not equal a full private address table.

## smf_standalone_interp_fallback_functions_unavailable_2026-06-14 — BUG: standalone SMF cannot run interp-fallback functions (string interpolation, slices)

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/smf_standalone_interp_fallback_functions_unavailable_2026-06-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/compilability.spl:98-163; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/simple_core/core_memory.spl:748-752
```
- Review rationale: Read standalone missing snapshot report and separate Windows COFF qualification blocker. Target compilability analyzer now has AotNative mode which keeps string interpolation native; default create() remains HybridJit and scoped compiler search finds no external create_for_mode/AotNative caller. Therefore the mode declaration alone cannot be accepted as active remedy. simple_core.rt_interp_call still returns rt_function_not_found (tagged nil3). This is compatible with absent standalone bridge support but the actual SMF producer’s routing/serialization path remains unresolved. Remaining evidence: Trace active standalone SMF producer to analyzer and MIR/serialization; prove native string lowering or serialized fallback body registration on current self-hosted runtime.
- Review corrections: AOT mode exists but no active caller was established; historical “neither exists” wording and blanket solution claims both need qualification.

## sosix_bootstrap_blocked_by_btrfs_metadata_reserve_2026-08-11 — SOSIX bootstrap blocked by btrfs metadata reserve

- Source receipt: `adjudication_v2_23`; inspection `report_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sosix_bootstrap_blocked_by_btrfs_metadata_reserve_2026-08-11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sosix_bootstrap_blocked_by_btrfs_metadata_reserve_2026-08-11.md:10-29; history 88aac2ffe28
```
- Review rationale: Read full report and target-bound history: the observation is a child stalled in btrfs_tree_read_lock during fingerprinting, with only1MiB unallocated despite large estimated free space; build was terminated before compiler verdict. Bounded searches of scripts/bootstrap, scripts, .claude/rules, .codex, .agents and bin did not locate the report’s device-unallocated guard. That missing current contract does not refute a host-state incident. There is no current storage receipt, and safe recovery cannot be inferred from this historical snapshot. Remaining evidence: Locate original operational preflight owner/receipt and compare current host storage state under an explicitly authorized operations lane; no deletion or balance recommended here.
- Review corrections: Accept conservative unknown as an investigated historical operational blocker, not a compiler failure or invalid report.

## sosix_process_sharing_spec_pre_existing_red_2026-08-27 — sosix_process_sharing_spec pre-existing RED — `sosix_dataset_active` not found

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sosix_process_sharing_spec_pre_existing_red_2026-08-27.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/system/app/os/feature/sosix_process_sharing_spec.spl:9-41; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/sosix/share.spl:33-80
```
- Review rationale: Full report’s six missing-variable failures do not establish declaration absence at target. Spec selectively imports sosix_share_init and dataset/queue APIs, then calls init before creation/seal/read assertions. share.spl declares sosix_dataset_active plus all sibling state arrays and sosix_share_init writes them directly. The failed name is an owner-private global reached from an imported function, not a variable the spec forgot to import. Source presence cannot prove selective-import environment resolution works. Remaining evidence: Trace loader function-environment retention for selectively imported share functions and run the six scenarios with admitted runtime.
- Review corrections: Reject report’s unsupported “referenced variable missing from module” diagnosis; declaration exists, so exporting globals is not established root remedy.

## sosix_qemu_external_host_admission_and_collector_gaps_2026-08-11 — SOSIX/QEMU External-Host Admission and Collector Gaps

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sosix_qemu_external_host_admission_and_collector_gaps_2026-08-11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-sosix-qemu-matrix.ps1:260-300; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/qemu/simple-qemu-host-admission.shs:126-154,185; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/collect-sosix-qemu-evidence.shs:20-50,121
```
- Review rationale: Full report’s closed normalization heading conflicts with explicitly partial Windows/macOS qualification. Current Windows matrix calls simple-qemu-host-admission.shs through Invoke-SosixShellTool and requires detected/requested windows plus identity, advertised accelerator and executable probe all pass. The shared owner contains bounded QMP capabilities/quit probing and final probe-status gate. Collector’s documented contract requires exactly24 bundles and source/compiler/nonce/artifact identities. This establishes a newer admission route; it does not establish native WHPX, macOS execution or collector receipt validity. Remaining evidence: Review shared Windows probe dispatch and collector implementation then retain native Windows/macOS signed identity and execution bundles; no host relabeling.
- Review corrections: Do not inherit closed heading; Windows now consumes a shared executable-probe contract but native qualification remains untested.

## sosix_qemu_matrix_media_and_selfhost_blockers_2026-08-11 — SOSIX/QEMU Matrix: Current-Host Media and Self-Hosted Runner Blockers

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sosix_qemu_matrix_media_and_selfhost_blockers_2026-08-11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-sosix-qemu-matrix.shs:153-165,168-225
```
- Review rationale: Read full six-guest media/lineage chronology including diagnostic executions, nonce limits and obsolete heading. Current matrix explicitly sets compiler_in_filesystem_for false for all six targets because its actual fs_exec boot entries do not emit canonical compiler protocol. check_row invokes host admission and refuses missing kernel/image. Thus a missing historical template path cannot negate the ongoing canonical media/compiler-evidence requirement. Historical guest flows and seed5/5 do not supply current admitted lineage. Remaining evidence: Obtain current six-target canonical media/source/compiler identities and nonce-bound guest receipts; inspect remaining per-row runtime validation before release classification.
- Review corrections: Promote uncertain to valid tracked delivery gap; reject obsolete-by-template-absence closure reasoning.

## sosix_stage2_blocked_by_runtime_wide_int_merge_2026-08-11 — SOSIX executable gates blocked by incomplete runtime wide-integer merge

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sosix_stage2_blocked_by_runtime_wide_int_merge_2026-08-11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:1531-1546,2594-2613,3894-3921,5460-5481,6991-7007; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime.h:406
```
- Review rationale: Full report describes a historical concurrently incomplete merge and explicitly warns against renaming unsigned representation. Target runtime_native defines both signed RtCoreWideInt and unsigned RtCoreUInt, registry/type-checked as_heap helpers, rt_value_u64 allocation/registration, and rt_value_as_u64 signed/unsigned decoding; runtime.h declares rt_value_u64. Inspected ordering handles unsigned comparisons without narrowing negative signed values. This supersedes named missing-type/declaration failures, but does not prove whole translation-unit build or all equality/hash/packed-array semantics. Remaining evidence: Inspect dictionary hash/canonicalization and packed-u64 equality invariants, then authorized focused C check plus source-matched bootstrap; no compiler execution here.
- Review corrections: Historical unknown RtCoreUInt/rt_value_u64 sites are stale at target. Retain unknown aggregate solution instead of mechanical signed/unsigned rename.

## source_change_inferred_return_field_layout_2026_10_11 — explicit return-type import/control keeps the producer ABI failure visible.

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/source_change_inferred_return_field_layout_2026_10_11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/source_change/contracts_v1.spl:70-135; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/fixtures/compiler/source_change_contract_cases.spl:19-24; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/fixtures/compiler/source_change_contract_native.spl:1-33; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_codec_support.spl:359-374
```
- Review rationale: Read full report including explicit nominal control failure and causal restraint around malformed persisted symbols. Current SourceChangeShapeV1 remains bool+text; batch_shape validates bounds and returns exact well_formed_change_batch string. The fixture executes inferred and annotated return paths and rejects any field/reason mismatch, retaining all16 real case checks. Current hir_codec_support.put_i64 renders the typed value first and only writes N for rendered nil, avoiding numeric3 versus nil comparison. This confirms the current codec remedy mechanism, but newer source cannot repair a frozen historical producer nor prove codec causation for the returned-field corruption. Remaining evidence: Retain newly admitted producer identity, fresh/warm cache symbols and constructor/return/projection results; do not alter record layout or claim codec alone fixes fields.
- Review corrections: Promote uncertainty to valid historical field-transport defect with current root unknown; explicit annotation is a diagnostic, not a fix.

## source_fixture_spec_unescaped_interpolation_and_content_drift_2026-07-20 — Source-guard specs put {ident} in interpolating strings so they die with `variable

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/source_fixture_spec_unescaped_interpolation_and_content_drift_2026-07-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.spl:12-25; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:1-29; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_declarations_bootstrap.spl:174-191; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_import_resolution.spl:71-101
```
- Review rationale: Read all amendments separating brace repair from expected Dict migration and duplicate-tree history. Target numbered spec escapes the opening import brace but still asserts exact rt_dict_keys strings against module_lowering.spl and absence of .keys(). Current lowering is split: module_declarations_bootstrap actively gets module_classes.keys(), sorts and iterates guarded class declarations; glob import registration moved to module_import_resolution with ModuleSurface contract. The legacy test/unit twin is absent at target, so old two-active-copy assertion is not current evidence. The test/source contract demonstrably drifted; this does not itself prove .keys() is currently miscompiled. Remaining evidence: Audit remaining named specs and current Dict dispatch contract before replacing source assertions or migrating product code; inspect test-discovery successor after legacy-tree removal.
- Review corrections: Opening brace repaired; current source decomposition and absent legacy twin supersede old line/copy claims. Valid test-contract drift is not proof of global product Dict failure.

## spec_cross_module_eval_warnings_not_observed_2026-08-05 — A spec importing eval_tables and eval separately reads eval_warnings back as 0 after a

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spec_cross_module_eval_warnings_not_observed_2026-08-05.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/eval.spl:335-347; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/eval_tables.spl:19,1236-1247; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/module_loader_core.spl:580-614,650-680
```
- Review rationale: Read whole report’s same-file versus cross-file distinction and workaround limits. Target eval.spl exposes pub eval_warnings and getter; report_match_fallthrough still pushes through that global, but eval_tables now explicitly imports it rather than relying solely on co-compilation. Loader initializes imported val/var declarations after dependency registration and binds selected function owners per caller. Those relevant changes remove a claimed missing-import precondition, but do not prove one mutable global instance or observable cross-file writeback. The report’s missing clear-helper remains separate from shared-state causation. Remaining evidence: Trace runtime global alias/writeback identity across selectively loaded functions and getter, then actual warning-state and Deny abort scenario; pure message helpers are insufficient.
- Review corrections: Current explicit eval_warnings import supersedes no-import description; no cross-module correctness inferred from public declaration.

## spec_describe_in_main_leaks_exit_code_2026-08-30 — `describe` as the trailing expression of `fn main() -> ()` leaks a non-zero exit code

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spec_describe_in_main_leaks_exit_code_2026-08-30.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/eval_calls.spl:325-361; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/eval_decls.spl:323-340; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/mod.spl:193-194
```
- Review rationale: Full report isolates a historical seed behavior and explicit return-unit workaround. Current pure-Simple eval_function_call records last statement value, replaces it only for explicit return, copies value structs and returns it; inspected path does not normalize declared unit return. eval_module forwards main’s value through the pipeline. This is a relevant tail-value propagation risk, but the native/seed versus self-hosted process-status transport and BDD outcome combination have not been established, so do not declare current repro or a solved bug. Remaining evidence: Trace public run result conversion into OS exit and BDD outcome merge, with unit-return describe fixture on the exact admitted runtime.
- Review corrections: Historical Rust-seed diagnosis is not automatically a current pure-Simple repro; explicit return remains workaround only.

## spec_helper_block_if_imported_call_not_callable_2026-08-19 — Spec-file helper with imported call inside block-if expression fails "semantic: value is not callable" under `simple test`

- Source receipt: `adjudication_v2_23`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spec_helper_block_if_imported_call_not_callable_2026-08-19.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/eval.spl:631-654; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/eval_calls.spl:41-79,170-178,287-361
```
- Review rationale: Read full nested A→B/block-if/import reproducer and passing controls. Target eval_if_expr evaluates chosen arm via eval_expr; eval_call resolves direct names using eval_caller_file, then caller-scoped/flat tables and environment; function calls save/set/restore current declaration ID and lexical frame. The generic value-is-not-callable site applies after indirect callee evaluation. These are the exact ownership/environment boundaries relevant to the symptom; no source inspection establishes which historical seed AST/helper frame selected a noncallable value, and inlining cannot count as root remedy. Remaining evidence: Trace block expression frame handling and parsed callee shape with the retained helper/import fixture, then admitted spec-run versus direct-run comparison.
- Review corrections: Retain unknown causation and untested current runtime; copied/inlined passing fixture does not close nested helper semantics.

## spec_run_fixed_cost_dominates_single_spec_runtime_2026-08-11 — Spec-run cost: daemon startup pays a full-tree lint pass; content-bound specs pay a separate, larger tax

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spec_run_fixed_cost_dominates_single_spec_runtime_2026-08-11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_args.spl:108; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_main.spl:419
```
- Review rationale: Current arguments default both session flags true; main routes through daemon responsiveness and run_tests_via_daemon with direct fallback. The full report measures a historical Rust seed on a loaded host and separately documents content-bound glslang work. Routing confirms applicability, not the claimed double lint attribution or current cost. Current profile and daemon startup owner remain undiagnosed.

## spec_step_bare_import_duplicates_file_rename_stack_overflow_2026-08-27 — `use std.spec.step` puts a duplicate `file_rename` in the unit; every atomic write self-recurses

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spec_step_bare_import_duplicates_file_rename_stack_overflow_2026-08-27.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/scv/store.spl:28; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/database/atomic.spl:200; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/file_ops.spl:450; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io_runtime.spl:500
```
- Review rationale: SCV scv_write_text calls database.atomic.atomic_write, whose rename imports std.io_runtime.file_rename. Current nogc io wrapper now uses uniquely named rename_path, which directly calls rt_file_rename; the report-era runtime_file_rename alias is absent from that wrapper. This is a relevant mitigation overlooked by research, but no compiler alias-resolution remedy or source-matched duplicate-import result establishes the broader root fix. Keep uncertain with unknown root solution.
- Review corrections: Research cited unrelated gc_async wrapper and missed the actual nogc wrapper mitigation; added atomic owner and direct rename_path boundary. No current recursive alias claim retained.

## spec_step_text_truncated_at_escaped_quote_2026-09-03 — Generated `step("...")` text is truncated at the first escaped quote, producing unparseable specs

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spec_step_text_truncated_at_escaped_quote_2026-09-03.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/cli/sound_cmd_pattern_spec.spl:124; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/io/run_sdn_lints_profile_spec.spl:37; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/office/sheets/formula_ref2_spec.spl:177; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/office/word/protection_spec.spl:122; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/spec_gen/spec_gen_drop_and_path_spec.spl:29; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/backend/svmg_lowering_spec.spl:250
```
- Review rationale: Independently checked all six reported residual spec paths: each implicated escaped-quote step retains trailing text and closing delimiter at c0. The report only suspects a generator quote split and requires producer repair. Corrected examples alone do not establish producer safety or a root solution.
- Review corrections: Repaired emitted examples do not establish a generator remedy; change research fixed_pending_verification to keep_open because the report explicitly requires durable producer repair.

## spec_test_loader_impl_method_dispatch_2026-08-27 — Spec-test loader fails method dispatch and mangles names for locally-defined classes and helpers

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spec_test_loader_impl_method_dispatch_2026-08-27.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_execute.spl:48; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/test_runner/core_spec.spl:150; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/test_runner/core_spec.spl:301
```
- Review rationale: Executor builds child arguments and runs the selected binary; current core_spec run_suite retains parser.feed and wraps the suite in a describe/it assertion. Full report distinguishes file-specific dispatch, assert_true shadowing, uppercase name mangling and success_rate failure; minimal probes did not isolate the trigger. Neither ordinary child invocation nor surviving method calls diagnose test-loader resolution.

## spec_to_be_true_to_be_false_seed_intrinsic_gap_2026-07-02 — Bug: `expect(x).to_be_true()` / `.to_be_false()` fail with "method not found on type bool"

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spec_to_be_true_to_be_false_seed_intrinsic_gap_2026-07-02.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_method/mod.rs:526; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_method/mod.rs:648; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/spec.spl:1285
```
- Review rationale: The report explicitly says source patched and rebuild pending despite a closed normalization header. Current Rust intrinsic recognition and strict Value::Bool arms implement both missing matchers; the owner bytes also match d805. This directly repairs the described seed dispatch omission, without certifying deployment or self-hosted execution.
- Review corrections: Proposed action changed from keep_open to fixed_pending_verification because the reported source patch and strict arms are present at c0; header closure is not accepted as runtime proof.

## spec_toplevel_return_unit_diagnostic_lacks_file_line_2026-09-03 — `cannot convert tuple to int` from a spec has no file:line

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spec_toplevel_return_unit_diagnostic_lacks_file_line_2026-09-03.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/error.spl:150; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/35.semantics/error_formatter.spl:131; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/value_impl.rs:148
```
- Review rationale: Full report concerns missing source provenance on an otherwise correct implicit-main rejection. Current generic formatters have spans, but the matching Rust value conversion constructs a semantic error with code/help context without a source span and a type-name message. The path from spec implicit main to that conversion remains untraced, so no fix or current result is inferred from generic formatter capability.
- Review corrections: Added matching Rust conversion owner; generic location-aware formatters alone do not establish the producer path.

## spec_verdict_forgeable_from_example_name_2026-08-17 — A spec file's pass/fail verdict is forgeable from an example's NAME

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spec_verdict_forgeable_from_example_name_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_executor_parsing.spl:150; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_single.spl:695; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_single.spl:1435
```
- Review rationale: Current output parsers still use example/failure substring recognition. The single-file caller invokes parse_child_example_summary on stdout plus stderr alongside structured evidence and verdict parsing, so vulnerable parsing is live in a broader decision tree. The full report demonstrates only historical false RED and expressly lacks a false-GREEN witness. Root solution remains unknown until actual precedence and the reported seed producer are qualified.
- Review corrections: Checked actual caller alongside structured verdict/evidence; no blanket forged-verdict claim from the substring parser alone.

## specs_assert_against_nonexistent_product_paths_2026-08-10 — 835 specs read 949 absent product paths so their negative to_equal(false) legs pass

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/specs_assert_against_nonexistent_product_paths_2026-08-10.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-spec-missing-path-vacuity.shs:65; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-spec-missing-path-vacuity.shs:129
```
- Review rationale: Read all retractions and later census corrections. The current scanner splits quoted literals, filters prefixes, then compares tracked paths; it does not prove a path is read or connect an empty value to a negative assertion. Its three controls establish only basic extraction behavior. The general vacuity risk remains valid, while historical counts and blanket obsolete/never-existed labels cannot be accepted as current diagnosis.

## spipe005_residual_assertion_free_examples_2026-08-01 — SPIPE005 still fires 1790 times across 196 files for assertion-free SPipe examples

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spipe005_residual_assertion_free_examples_2026-08-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/90.tools/lint/_LintMain/traceability_and_assertions.spl:359
```
- Review rationale: The complete report separates real placeholders, duplicate-tree counting, transient generated artifacts, and scanner artifacts. Current check_spipe_example_bodies stops at indentation without tracking multiline literal state, which directly supports the reported false body truncation mechanism. This narrow mechanism does not validate the historical 1752/188 census or diagnose the entire residual corpus; keep the broad report open with unknown aggregate remedy.

## spipe_docgen_deployed_macos_cli_stale_2026-09-09 — Deployed macOS CLI cannot regenerate the rendering knowledge manual

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spipe_docgen_deployed_macos_cli_stale_2026-09-09.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/cli/_CliMain/main_and_help.spl:630; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/io/_CliCommands/run_commands.spl:663; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/02_integration/app/llm_process/knowledge_routing_process_spec.spl; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/06_spec/02_integration/app/llm_process/knowledge_routing_process_spec.md
```
- Review rationale: Independently calculated c0 source/manual hashes: both exactly match the report. Current CLI dispatch routes spipe-docgen to cli_run_file of the generator, whereas the reported old Mach-O treated it as a filename. Output freshness and same-artifact generator qualification remain absent; source dispatch alone does not fix the secondary allocator or nil-result failures.

## spipe_lacks_context_mode_chunking_and_surfaces_2026-08-31 — SPipe knowledge provider lacks context-mode's chunking, stemming and exec surfaces (2026-08-31)

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spipe_lacks_context_mode_chunking_and_surfaces_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/search/document.spl:102; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/search/analyzer.spl:20; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/spipe_knowledge_provider/lexical.spl:238; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/mcp/main_lazy_query_tools.spl:435
```
- Review rationale: SearchHit and SearchHitV1 remain document-level without snippets; lexical rank construction emits document IDs and the frozen analyzer declares no stemming. The inspected simple_pipe dispatcher recognizes context/codebase/search/ponytail and rejects other surfaces. This corroborates the scoped capability request, including versioned model/API changes for chunk hits and stemming, without proving global absence or a complete execution-sandbox design.
- Review corrections: The report is valid; structural_change changed from unknown to yes because chunk/snippet requires extending the current hit/document contract and an execution surface has separate sandbox/ownership design.

## spipe_streaming_sha_interpreter_value_array_copy_timeout_2026-08-25 — SPipe streaming SHA interpreter verification exceeds budget

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spipe_streaming_sha_interpreter_value_array_copy_timeout_2026-08-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/spipe_knowledge_provider/provider_streaming_sha256_spec.spl:57; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/spipe_knowledge_provider/streaming_sha256.spl:104; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/spipe_knowledge_provider/streaming_sha256.spl:203
```
- Review rationale: The report ends with a second 180s exit-124 attempt on an identified Rust seed, no matrix summary or RSS. Current deterministic_bytes still pushes every byte; streaming SHA owns fixed buffers and performs in-place compression, but update receives an array plus range. Those semantics support bounded state and possible copy boundaries, not measured attribution, guaranteed copies, or a known performance remedy.

## spirv_builder_module_drops_to_interpreter_via_unresolved_jit_symbol_2026-08-11 — Any module using SpirvBuilder drops whole-module to interpreter on unresolved JIT symbol

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spirv_builder_module_drops_to_interpreter_via_unresolved_jit_symbol_2026-08-11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/plugins/backend_vulkan/vulkan/spirv_builder.spl:45; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/os/vulkan/spirv_khronos_validation_spec.spl:27
```
- Review rationale: The full report identifies unresolved SpirvBuilder_dot_create in a historical JIT log, explicitly separating output validity from dispatch. Current plugin builder still has static create and Khronos spec describes independent output validation. These do not establish symbol registration or strict JIT success; no root fix is shown by a relocated builder or conformance checks.

## spl_doctest_composite_fails_wildcard_reexport_modes_2026-08-25 — SPL-doctest composite fails on a wildcard re-export that imports fine standalone

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spl_doctest_composite_fails_wildcard_reexport_modes_2026-08-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/test_runner_modes.spl:30; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/doctest_runner.spl:441; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/doctest_runner.spl:266; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/15.blocks/blocks/modes.spl:6
```
- Review rationale: Research selected the app duplicate as active without checking the std owner. Current library test_runner_modes imports std.test_runner.doctest_runner and calls run_spl_doctests_same_file; that library builder still injects use std.spec.* at lines 441-442, unlike the app duplicate. modes.spl retains its wildcard re-export. The suspected interaction remains unproven and cannot be classified repaired. The library failure formatter must be distinguished from sdoctest.runner as well.
- Review corrections: Research app duplicate was not sufficient std owner evidence. Library composite still injects wildcard; library child execution uses bounded process API. No repair inferred from the duplicate or separate sdoctest formatter.

## spl_doctest_harness_aborts_unsafe_not_found_2026-08-25 — `--spl-doctest` aborts on every input at origin/main — `function `unsafe` not found`

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spl_doctest_harness_aborts_unsafe_not_found_2026-08-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/doctest_runner.spl:6; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_client.spl:400
```
- Review rationale: Full report isolates a historical source-tree endpoint change under one Rust seed but leaves the culprit commit unknown. Current library doctest owner imports bounded process and file APIs and finds its binary through test_executor_parsing, avoiding the broad execute import in the app duplicate. This changes the graph from research assumptions; it does not identify the historical unsafe failure edge or prove modern compatibility.
- Review corrections: Research app duplicate was not sufficient std owner evidence. Library composite still injects wildcard; library child execution uses bounded process API. No repair inferred from the duplicate or separate sdoctest formatter.

## spl_doctest_phase_emits_no_verdict_line_on_abort_2026-08-25 — SPL-doctest phase exits non-zero with NO verdict line when a source file fails to compile

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spl_doctest_phase_emits_no_verdict_line_on_abort_2026-08-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/test_runner_modes.spl:80; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/doctest_runner.spl:475; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_client.spl:410
```
- Review rationale: Current library modes prints its start banner then calls run_spl_doctests_same_file; the client emits a terminal summary only after that returns. Library child failures produce BlockResults using bounded process results, but a harness/load abort outside that result path is not thereby covered. The historical missing-verdict distinction remains real; an external abort receipt design is not proven implemented by ordinary child-error handling.
- Review corrections: Research app duplicate was not sufficient std owner evidence. Library composite still injects wildcard; library child execution uses bounded process API. No repair inferred from the duplicate or separate sdoctest formatter.

## spl_doctest_variable_not_found_class_2026-08-24 — SPL doctest class `semantic: variable X not found` — triage 2026-08-24

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/spl_doctest_variable_not_found_class_2026-08-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/http_server/middleware.spl:70; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/async/promise.spl:7; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/file.spl:112; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/doctest_runner.spl:441
```
- Review rationale: The amended report retracts missing MiddlewarePipeline.add, Promise and FileHandle read/create APIs; current correct-family implementation confirms all three. Library doctest assembly appends std.spec and executes children, so import repair and fixture/source-alone failures must remain separate from nonexistent API claims. Neither historical net counts nor the wrong-family diagnosis establishes aggregate completion.
- Review corrections: Correct-family definitions checked; use library owner rather than app duplicate for assembly claims.

## squashed_snapshot_e274cd33719_gutted_81_files_2026-09-07 — `e274cd33719` is a squashed stale snapshot that gutted 81 files repo-wide

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/squashed_snapshot_e274cd33719_gutted_81_files_2026-09-07.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/compositor/frame_pacer.spl:42; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/compositor/cursor.spl:84; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/compositor/hosted_wm_capture_evidence.spl; e274cd33719af76bfb315a1b046b73140755d5ee and parent 0fce018eda368724ab9650aa8af1207c3f9179ce:src/os/compositor/{frame_pacer,cursor,hosted_wm_capture_evidence}.spl; current-bound path history
```
- Review rationale: Independently compared parent/snapshot/current objects. e274cd33719 has one parent; frame_pacer loses its contract and thread_sleep in the snapshot and current restores them; cursor goes 294 to 6 lines then current restores 294 with IBeam hotspot. Residual hosted_wm_capture_evidence changes dimensions, pixel receiver use and theme receipt fields; current is not byte-identical to the snapshot and intervening c0-bound history includes transplantation. This supports the historical damage while leaving residual ownership and blanket restoration unjustified.

## ssa_alloca_value_return_admission_spec_conflict_2026-08-21 — SSA alloca lane rejects `Ret(Some(..))` — four reproducer specs RED, two specs assert the opposite

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/ssa_alloca_value_return_admission_spec_conflict_2026-08-21.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl:954; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl:1385; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl:1749; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl:1834; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/unit/compiler/mir_opt/var_reassign_analysis_spec.spl:154; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/driver/ssa_local_payload_source_spec.spl:32; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/mir_opt/ssa_alloca_ret_operand_unwrap_free_spec.spl:175; 771e05e33b7 (c0-bound log and actual admission/use/rewrite diff)
```
- Review rationale: The current alloca implementation admits structurally valid return operands, counts returned locals as uses, and rewrites loads; bound history 771e05e33b7 implements that policy. However the cited legacy var_reassign_analysis_spec still explicitly requires rejection of every present return and exact unsupported-value-return reason; ssa_local_payload_source_spec also pins the obsolete unwrap spelling, while implementation uses ??. Research fixed_pending_verification therefore overstates reconciliation of the reported conflicting-spec contract. Keep open pending coordinated spec/contract resolution and native safety qualification.
- Review corrections: Reject research fixed_pending_verification: explicit legacy rejection assertions survive; driver source assertion also requires obsolete unwrap. Implementation improvement is not full conflicting-spec resolution.

## ssh_daemon_baremetal_only_and_duplication_2026-08-05 — sshd cannot bind a host socket because its network layer is baremetal-only

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/ssh_daemon_baremetal_only_and_duplication_2026-08-05.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/sshd.spl:561; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/ssh_session.spl:556; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/ssh_client/ssh_known_hosts.spl:118; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/arch/riscv64/boot/freestanding_runtime.c:2483
```
- Review rationale: Current sshd start calls boot-local TCP bind; scoped search finds its definition in RISC-V freestanding runtime and none in src/runtime. The session consumes the accelerated AES packet path and known-host parsing has real malformed-store rejection and key material logic. Full report reverses WIP deletion advice and distinguishes portable/accelerated roles. The host gap and ownership questions remain; neither blanket duplication removal nor mandatory structural redesign follows without a target/owner decision.
- Review corrections: Structural yes not established: actual host transport target and owner contract remain undecided; cross-directory findings alone are not proof of a required architectural change.

## sspec_simple_check_describe_it_parser_2026-06-28 — Bug: `bin/simple check` rejects SSpec `describe`/`it` DSL files

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sspec_simple_check_describe_it_parser_2026-06-28.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/cli/check.spl:268; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/check/sspec_source.spl:21; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/check/check_sspec_guidance_shared_lexer_spec.spl:34
```
- Review rationale: The report accepts either parser support or actionable check guidance. _check_path now calls check_sspec_guidance before parse_module; the lexer-backed recognizer detects std.spec plus top-level describe and emits E-SSPEC-CHECK with the interpreter test command. Tests assert guidance for real and comment-delimiter fixtures and silence for ordinary/docstring-only cases. Guidance owner is identical to d805. This is a concrete local source remedy; current latency and CLI behavior remain untested.

## stage2_admission_source_quiescence_unsatisfiable_in_shared_tree_2026-08-31 — Stage 2 admission source-quiescence invariant is unsatisfiable in the shared working tree

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_admission_source_quiescence_unsatisfiable_in_shared_tree_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh:4722; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh:4757; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-in-snapshot.shs:77
```
- Review rationale: The source guard still compares before/after source snapshots, verifies both sanity receipts, and resnapshots after private publication. The isolated helper actually creates a detached worktree at a resolved committed SHA and excludes uncommitted edits. This supports the operational isolation procedure while preserving admission integrity; it does not erase the historical shared-tree workflow limitation or settle separate diagnostic path gaps.

## stage2_aot_error_message_lost_invalid_heap_2026-09-06 — Stage-2 AOT compile error reports `<invalid-heap:0x…>` instead of its message

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_aot_error_message_lost_invalid_heap_2026-09-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_aot_native_output.spl:3355; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_aot_native_output.spl:3399; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_aot_native_output.spl:4463
```
- Review rationale: Current _finish_selected_module_compile still receives Result<CompiledModule,CompileError> across a call boundary, renders Err(err), and sends text to _aot_compile_failure. The helper prints literal, bare values and lengths before returning an interpolated Err; its comments explicitly retain the ABI defect and retract an earlier claim it ran on a failing path. This is diagnostic hardening, not proof the originally corrupted payload survives or that upstream representation is repaired. Reject fixed_pending_verification for the full report.
- Review corrections: Research treated diagnostic hardening as message-plumbing repair. Actual owner explicitly preserves the ABI defect and retracts claimed execution on a different failing path; no matching producer representation or payload survival proof.

## stage2_binary_vulkan_backend_init_segfault_2026-08-09 — Stage2 self-hosted binary SIGSEGVs in VulkanBackend.init while the Rust seed runs the

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_binary_vulkan_backend_init_segfault_2026-08-09.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:868; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl:230; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl:568; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_dynload.c:1739
```
- Review rationale: Traced current RenderBackend.init through VulkanSession.init, availability/device checks, vulkan_sffi_init and rt_vulkan_init. runtime_dynload provides a GPU_CALL0 dispatch wrapper and lists the provider symbol among required Vulkan entries; that establishes routing rather than runtime qualification. The historical seed control cannot prove soundness of a different Stage2 producer or identify its crash cause; keep uncertainty and unknown remedy.

## stage2_candidate_segv_at_monomorphize_2026-09-13 — Pinned Stage-2 candidate SIGSEGVs at the monomorphize phase

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_candidate_segv_at_monomorphize_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/40.mono/monomorphize_integration.spl:472; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/40.mono/monomorphize_integration.spl:5232
```
- Review rationale: The report identifies a rejected candidate only by path, size and hash prefix, with cold-index admission required before task 4/6 monomorphize crash. Current run_monomorphization constructs a pass and calls process_modules, which collects generic definitions and rewrites roots/worklists; several operations lie under the phase label. No retained full identity/backtrace binds the old fault to one operation. Conservative uncertainty is supported; --version is not compiler qualification.

## stage2_compiled_program_returned_array_len_zero_2026-09-20 — Stage-2-compiled programs: `.len()` of a function-returned array is 0

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_compiled_program_returned_array_len_zero_2026-09-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:658; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3210; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/mir/returned_struct_array_native_spec.spl:16
```
- Review rationale: Current local_is_runtime_array checks metadata plus explicit MIR Array/Slice discriminants; the len dispatcher uses that predicate before changing rt_len to rt_string_len. The native spec builds an imported fixture and requires native exit and exact stdout, preventing zero-loop validation. This is a concrete candidate for the reported misrouting and field provenance, but report explicitly lacks repaired-compiler evidence and defers an owned Slice fixture. The old binary precise cause and complete Array/Slice remedy remain unknown.

## stage2_cranelift_direct_segv_nil_struct_fields_2026-08-24 — Stage-2 SEGV: unguarded deref of nil struct fields in stage2-generated code (2026-08-24)

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_cranelift_direct_segv_nil_struct_fields_2026-08-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:332; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl:441
```
- Review rationale: The report contains two distinct historical backtraces. Current backend build_signature still directly reads params and return_type.kind. The matching HIR owner is _Items/declaration_lowering, not research statements.spl: it now gates synthesized main/bootstrap and binds the get_symbol_type Option directly with if val, explaining an adjacent unwrap hazard. Neither this safeguard nor a direct field read proves old constructor/store/dict-read corruption is repaired or shared between both crashes.
- Review corrections: Research statements.spl excerpt concerned a different Expr payload path; traced the reported lower_function/get_symbol_type owner and its current direct Option binding instead.
