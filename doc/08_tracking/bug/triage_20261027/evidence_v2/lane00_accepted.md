# V2 lane 00 accepted review evidence

Accepted classifications captured: 57. Assessment target: `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`.

## 2998 — retain array type across optional dictionary lookup

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/40.mono/monomorphize/cycle_detector.spl:138](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/40.mono/monomorphize/cycle_detector.spl#L138)
- Review rationale: DFS checks graph membership and binds graph[node] to explicit [text] before iteration. The three workaround markers establish a live typing workaround but contain no failing optional-lookup case or diagnosed inference owner; validity and remedy remain uncertain.
- Review corrections: structural_change: yes -> unknown; Structural yes is unsupported by this consumer workaround.

## BUG-2026-10-12-CONTEXT-COMPARISON — Rust seed treats a context comparison tail as a context statement

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_hir_pipeline_lowering.spl:198](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_hir_pipeline_lowering.spl#L198)
- Review rationale: Custody matching explicitly returns the context comparison after computing the context. The annotated Rust-seed parsing claim is not independently reproduced and this consumer does not identify a parser repair.
- Review corrections: structural_change: yes -> unknown; Structural yes is unsupported; recorded line198 is function start, annotation is line213.

## BUG-BOOTSTRAP-FROZEN-PLUGIN-SCOPE-20261011 — Bootstrap Stage2/Stage3 omit plugin owners from frozen source selection

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bootstrap_frozen_plugin_source_scope_2026-10-11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/bootstrap_frozen_plugin_source_scope_2026-10-11.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh:1766](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/bootstrap-from-scratch.sh#L1766); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh:4314](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/bootstrap-from-scratch.sh#L4314); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh:4566](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/bootstrap-from-scratch.sh#L4566)
- Review rationale: Historical frozen snapshot omitted both imported plugin owners. Constructor now selects canonical src/plugins and threads its root through actual Stage2 execution/transcript and other vectors; the root-selection remedy directly addresses omission without relaxing admission. Newly bound native qualification remains absent.
- Review corrections: reproducibility: reproducible -> untested; Historical reproducible becomes untested.

## BUG-HIR-FORWARDING-EXTRACTOR-20261011 — Cache HIR forwarding fixture uses obsolete Stage3 command extraction boundary

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/cache_hir_stage3_extraction_boundary_2026-10-11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/cache_hir_stage3_extraction_boundary_2026-10-11.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/scripts/bootstrap_cache_hir_controls_test.shs:52](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/scripts/bootstrap_cache_hir_controls_test.shs#L52)
- Review rationale: Extractor now stops at exact output argument, requires closed=1, and mutates that terminator to prove refusal. This directly fixes historical overcapture/missing-boundary acceptance; historical shell PASS is not this audit execution.
- Review corrections: reproducibility: reproducible -> untested; Historical reproducible becomes untested.

## BUG-MIR-ENUM-FIELD-RECEIVER-20261010 — Native80030 loses enum field receiver for TrustAuditStatus.name

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/enum_field_receiver_80030_2026-10-10.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/enum_field_receiver_80030_2026-10-10.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/00.common/assurance/trust_audit.spl:49](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/00.common/assurance/trust_audit.spl#L49)
- Review rationale: The original audit.status.name() expression is still used in canonical hashing. Report identifies retained80030 MIR receiver failure and two repair leads but cannot bind either to failing producer. No demonstrated matching current repair was established; explicit binding is only a workaround.
- Review corrections: reproducibility: reproducible -> untested; solution: known -> unknown; structural_change: yes -> unknown; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> keep_open; Historical reproducible becomes untested; known/structural yes overstates report-only fix leads.

## BUG-MODULE-STATIC-REGISTER-ARRAY-INFERENCE-20261011 — MIR cannot infer module static register arrays from explicitly typed i64 constants

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/module_static_register_array_inference_2026-10-11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/module_static_register_array_inference_2026-10-11.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/native/mach_inst.spl:62](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/70.backend/backend/native/mach_inst.spl#L62)
- Review rationale: Historical six-module HIR pass followed eleven MIR initializer inference failures despite scalar i64 constants. Current register arrays have explicit [i64] annotations; these restore consumer declarations but do not repair inference. The report explicitly leaves compiler repair unqualified.
- Review corrections: reproducibility: reproducible -> untested; structural_change: yes -> unknown; Historical reproducible becomes untested; structural yes is undiagnosed.

## BUG-NATIVE-NESTED-STRUCT-NIL-COPY-20261016 — tagged-nil-nested-record-copy-guard

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_nested_struct_nil_copy_2026_10_16.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/native_nested_struct_nil_copy_2026_10_16.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/mir_data.spl:229](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/mir_data.spl#L229)
- Review rationale: Builder supplies canonical DriverManifestAttr with false presence at all three inspected sites. Report maps earlier crash to tagged nil3 copied through a raw-zero guard, and records later focused TCO workaround success; it explicitly does not qualify producer nil guard. Remedy and architectural scope remain undiagnosed here.
- Review corrections: reproducibility: reproducible -> untested; structural_change: yes -> unknown; Historical reproducible becomes untested; structural yes unsupported; later focused workaround PASS is distinct from producer fix.

## BUG-NATIVE-RESULT-CHAR-UNWRAP-20261017 — result-char-unwrap-unsupported-use-real-pattern

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_result_char_unwrap_2026_10_17.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/native_result_char_unwrap_2026_10_17.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:949](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl#L949)
- Review rationale: Report retains a concrete Result<char,text>.unwrap MIR rejection. Current unwrap core dispatches on payload kinds and fails unsupported kinds; fixture Ok/Err matching bypasses that path. No carrier-correct Char remedy was independently proven.
- Review corrections: reproducibility: reproducible -> untested; structural_change: yes -> unknown; Historical reproducible becomes untested; structural yes unsupported.

## BUG-NATIVE-U8-TO-I64-TEXT-DISPATCH-20261017 — numeric-u8-to-i64-resolves-text-parser

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_u8_to_i64_text_dispatch_2026_10_17.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/native_u8_to_i64_text_dispatch_2026_10_17.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2526](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl#L2526); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:4854](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl#L4854)
- Review rationale: Report COFF routes u8 array indexing through text conversion and fails ASCII byte65. Current owner now excludes proven numeric locals from erased text fallback and provides numeric to_i64 casting, but byte-index provenance through these guards is not established. Keep source remedy as lead pending exact fixture qualification.
- Review corrections: reproducibility: reproducible -> untested; structural_change: yes -> unknown; Historical reproducible becomes untested; structural yes unsupported; current numeric guard prevents assuming old dispatch persists.

## BUG-X86-EVEX-STATIC-ARRAY-INFERENCE-20261017 — producer0015_cannot_infer_register_id_array

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/BUG-X86-EVEX-STATIC-ARRAY-INFERENCE-20261017.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/BUG-X86-EVEX-STATIC-ARRAY-INFERENCE-20261017.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/native/_X8664Avx512/evex_encoding.spl:82](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/70.backend/backend/native/_X8664Avx512/evex_encoding.spl#L82)
- Review rationale: Full report records producer0015 static initializer errors and later focused workaround execution. Both current arrays retain explicit [i64] and original register IDs; compiler inference owner remains explicitly unfixed.
- Review corrections: validity: uncertain -> valid; structural_change: yes -> unknown; Standalone report supplies historical validity beyond annotation; no current reproduction or structural diagnosis.

## a174_aggregate_receiver_provenance_2026_10_16 — retain-explicit-aggregate-receiver-type

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/database/core.spl:676](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/database/core.spl#L676)
- Review rationale: Validation explicitly types table, row array and each SdnRow before get(valid); marker records aggregate receiver provenance workaround. This is a consumer preservation technique, not evidence of root repair.
- Review corrections: structural_change: yes -> unknown; Unsupported structural=yes downgraded to unknown; workaround is not a root solution.

## a174_enum_scalar_codec_wire_boundary_2026_10_16 — generate-typed-enum-prototypes-and-schema-owned-wire-nil-slots

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/compiler_schema/codec_gen.spl:734](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/compiler_schema/codec_gen.spl#L734)
- Review rationale: Decoder generator retains typed-enum-prototype/wire-nil marker while encoder now rejects nil, illformed and unregistered nodes. Row contains no standalone failure or diagnosis of enum scalar wire boundary; nearby encoder guards do not establish a fix.
- Review corrections: validity: valid -> uncertain; reproducibility: reproducible -> untested; structural_change: yes -> unknown; Unsupported structural=yes downgraded to unknown; workaround is not a root solution.

## a174_enum_tuple_literal_provenance_2026_10_16 — retain-tuple-payload-type-at-constructor

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/04_smoke/enum_wire_boundary_native.spl:136](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/04_smoke/enum_wire_boundary_native.spl#L136)
- Review rationale: Smoke fixture binds (7,9) as an explicit (i64,i64) then tests TupleOnly restored payload values and slot rejection. Real assertions exist, but no original untyped-constructor failure or runtime outcome is provided.
- Review corrections: Unsupported structural=yes downgraded to unknown; workaround is not a root solution.

## a174_named_enum_payload_owner_2026_10_16 — retain-declared-owner-through-positional-payloads

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_types.spl:784](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/20.hir/hir_types.spl#L784)
- Review rationale: HirType.named converts primitive names through HirTypeKind payload constructors; marker says declared owner must survive positional payloads. This consumer alone does not diagnose enum payload provenance loss; nearby metadata cache filter is not that fix.
- Review corrections: structural_change: yes -> unknown; Unsupported structural=yes downgraded to unknown; workaround is not a root solution.

## a174_nominal_enum_operator_resolution_2026_10_16 — compare-exhaustive-canonical-section-names

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/smf/runtime_std_package_membership_v1.spl:260](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/smf/runtime_std_package_membership_v1.spl#L260)
- Review rationale: Aggregate validation compares canonical section-kind names while also checking names, content and bounds. Enum-name comparison is an active workaround; no direct enum operator failing case or root remedy is supplied.
- Review corrections: structural_change: yes -> unknown; Unsupported structural=yes downgraded to unknown; workaround is not a root solution.

## a174_struct_nil_comparison_dispatch_2026_10_16 — old-producer-record-presence-dispatch

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/compiler_schema/codec_gen.spl:428](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/compiler_schema/codec_gen.spl#L428)
- Review rationale: Current node encoder binds once to an optional typed local and checks presence before unwrap, addressing documented double-read and nil copy-in hazards. This has moved beyond stale line436; it does not establish a general struct-nil comparison dispatch fix.
- Review corrections: validity: valid -> uncertain; reproducibility: reproducible -> untested; structural_change: yes -> unknown; Unsupported structural=yes downgraded to unknown; workaround is not a root solution.

## a174_transient_promote_inference_2026_10_16 — retain-explicit-text-owner-at-generic-promotion

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/40.mono/mono_archive_current_registration_seal_v1.spl:53](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/40.mono/mono_archive_current_registration_seal_v1.spl#L53)
- Review rationale: Seal owner explicitly supplies transient_promote<text> for authority, schedule and proof while preserving pause/end and ownership refusal. Marker proves inference workaround use but supplies neither failing inferred call nor generic inference remedy.
- Review corrections: structural_change: yes -> unknown; Unsupported structural=yes downgraded to unknown; workaround is not a root solution.

## acpi_spec_three_reads_return_zero_2026-09-19 — The acpi unit spec's three positive reads return 0, and it is NOT the nested-fn capture defect it was attributed to

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/acpi_spec_three_reads_return_zero_2026-09-19.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/acpi_spec_three_reads_return_zero_2026-09-19.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/os/acpi/acpi_test.spl:168](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/os/acpi/acpi_test.spl#L168); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/acpi/hpet_table.spl:40](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/kernel/acpi/hpet_table.spl#L40); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/acpi/fadt.spl:50](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/kernel/acpi/fadt.spl#L50)
- Review rationale: Full report rules out nested-function capture and retains three positive reads returning zero. Actual HPET owner combines reader words at GAS address and returns optional u64; FADT owner prefers valid extended GAS then legacy port. Specs cast those optional results. No local forced-zero read exists; fixture versus optional conversion remains undiagnosed.
- Review corrections: reproducibility: reproducible -> untested; inspection_level: report_reviewed -> source_reviewed; Historical execution is not current reproduction; source/report limits stated explicitly.

## admit_is_a_hard_keyword_unusable_as_identifier_2026-08-21 — `admit` is a hard keyword and cannot name a function

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/admit_is_a_hard_keyword_unusable_as_identifier_2026-08-21.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/admit_is_a_hard_keyword_unusable_as_identifier_2026-08-21.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/lexer/identifiers.rs:281](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/parser/src/lexer/identifiers.rs#L281)
- Review rationale: Current seed lexer treats admit/assume as keywords unless immediately followed by ! or (. This partially contextual rule does not admit the import-identifier form described by the report. Choosing broader contextual syntax versus documenting reservation is still an unresolved contract decision.
- Review corrections: reproducibility: reproducible -> untested; solution: known -> unknown; structural_change: yes -> unknown; inspection_level: report_reviewed -> source_reviewed; Historical execution is not current reproduction; source/report limits stated explicitly.

## aes128_gcm_verification_blocked_by_env_access_parse_2026-08-25 — AES-128-GCM verification blocked by hosted environment parse

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/aes128_gcm_verification_blocked_by_env_access_parse_2026-08-25.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/aes128_gcm_verification_blocked_by_env_access_parse_2026-08-25.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/io/env_access_host.spl:16](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/io/env_access_host.spl#L16)
- Review rationale: Full report clearly tracks environment-source parse blocking AES test loading, not an AES correctness failure. Current host owner has typed callback fields and exported registrations; no matching parser cause or qualified producer is established. Preserve blocker validity and unknown remedy.
- Review corrections: validity: uncertain -> valid; reproducibility: reproducible -> untested; inspection_level: report_reviewed -> source_reviewed; Historical execution is not current reproduction; source/report limits stated explicitly.

## allow_reserved_as_hard_keyword_2026-09-13 — `allow` and `forbid` cannot be used as identifiers — hard keywords the lexer's own comment says are contextual

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/allow_reserved_as_hard_keyword_2026-09-13.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/allow_reserved_as_hard_keyword_2026-09-13.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/lexer/identifiers.rs:260](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/parser/src/lexer/identifiers.rs#L260); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/lexer/identifiers.rs:333](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/parser/src/lexer/identifiers.rs#L333)
- Review rationale: Current lexer comment declares allow contextual but AOP table still emits Allow/Forbid tokens. Full report's renamed-variable control supports a real reservation discrepancy. Root remedy must reconcile parser identifier/AOP handling; deleting tokens without caller review is not yet established.
- Review corrections: reproducibility: reproducible -> untested; solution: known -> unknown; structural_change: yes -> unknown; inspection_level: report_reviewed -> source_reviewed; Historical execution is not current reproduction; source/report limits stated explicitly.

## app_launchers_no_admitted_runtime_aarch64_linux_2026_10_19 — bin/devhub, bin/caret and 5 sibling launchers never probe bin/release/aarch64-unknown-linux-gnu and reject the seed, so they exit 127 on aarch64 Linux

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:bin/devhub:32](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/bin/devhub#L32)
- Review rationale: Frozen description reports missing aarch64 candidate plus no admitted runtime. Current devhub has explicit aarch64-linux candidate and enforces provenance. Path omission has changed; admitted full CLI prerequisite remains real. Full launcher-family remedy cannot be claimed from one wrapper.
- Review corrections: reproducibility: reproducible -> untested; solution: known -> unknown; structural_change: no -> unknown; recommended_action: fixed_pending_verification -> keep_open; Historical execution is not current reproduction; source/report limits stated explicitly.

## app_modules_referenced_by_specs_exist_nowhere_2026-08-04 — Spec-referenced app symbols missing: handle_os_inline / handle_os_build_inline

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/app_modules_referenced_by_specs_exist_nowhere_2026-08-04.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/app_modules_referenced_by_specs_exist_nowhere_2026-08-04.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/cli/_CliMain/args_and_os_commands.spl:407](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/cli/_CliMain/args_and_os_commands.spl#L407); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/cli.spl:258](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/cli.spl#L258)
- Review rationale: Full report has two resolved module gaps plus OS target policy and userland_target residuals. Current inline build shim uses get_target, but separate os.cli build still uses get_qemu_target. Restored wrapper names do not prove active route or full policy contract fixed; remaining owner choice/route evidence is required.
- Review corrections: solution: known -> unknown; structural_change: no -> unknown; recommended_action: fixed_pending_verification -> keep_open; Raw known/local fixed conclusion omitted residuals in full report.

## arm64_attested_build_rejects_rust_seed_by_design_2026-09-01 — arm64 attested build: `compiler-version-invalid` is a BY-DESIGN Rust-seed refusal, not a stale binary (2026-09-01)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/arm64_attested_build_rejects_rust_seed_by_design_2026-09-01.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/arm64_attested_build_rejects_rust_seed_by_design_2026-09-01.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/lib/simpleos-arm64-guest-source-fingerprint.shs:94](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/check/lib/simpleos-arm64-guest-source-fingerprint.shs#L94)
- Review rationale: Full report correctly distinguishes successful seed parser update from intentionally refused seed admission and absent Stage4 os-build CLI. Current version/path guard matches that refusal. Correct protection does not invalidate tracked missing admitted full CLI and unproven firmware handover.
- Review corrections: validity: uncertain -> valid; inspection_level: report_reviewed -> source_reviewed; Historical execution is not current reproduction; source/report limits stated explicitly.

## armv7_windows_backend_plugin_target_rejected_2026_10_26 — armv7-w64-mingw32 native-build fails: BACKEND_SESSION_AUTHORITY load rejected: BACKEND_PLUGIN_TARGET

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/armv7_windows_backend_plugin_target_rejected_2026-10-26.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/armv7_windows_backend_plugin_target_rejected_2026-10-26.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend_plugin/builtin_adapter.spl:132](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/70.backend/backend_plugin/builtin_adapter.spl#L132)
- Review rationale: Historical armv7-mingw HIR completes then backend admission rejects. Current target mapper accepts arm but not armv7, with later supports_target gate. Canonical triple normalization/manifest admission preceding this mapper remains untraced; adding a leaf alias alone is not a proven full remedy.
- Review corrections: validity: uncertain -> valid; reproducibility: reproducible -> untested; structural_change: yes -> unknown; Historical execution is not current reproduction; source/report limits stated explicitly.

## array_set_missing_on_interpreter_2026-08-18 — `[T].set(i, v)` is missing on the interpreter (present in codegen)

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/array_set_missing_on_interpreter_2026-08-18.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/array_set_missing_on_interpreter_2026-08-18.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl:1079](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl#L1079); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler_core/interpreter/array_method_set_spec.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/compiler_core/interpreter/array_method_set_spec.spl); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/language/array_set_spec.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/language/array_set_spec.spl)
- Review rationale: Inventory-to-target diff adds exact-arity set dispatch, evaluates arguments before current-length lookup, normalizes integer negative indices and returns val_array_set bool. Direct dispatcher spec prevents native masking and checks bounds/type/arity controls. This is newly authored pure-Simple parity repair; original seed failure and production runtime qualification remain separate.
- Review corrections: reproducibility: reproducible -> untested; recommended_action: fix_candidate -> fixed_pending_verification; Historical execution remains untested for target; independently observed current source differs from raw claims where stated.

## atomic_write_tagged_text_abi_2026_10_12 — Atomic snapshot write receives raw pointers instead of tagged text

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/text_extern_abi.spl:275](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/text_extern_abi.spl#L275); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/fixtures/bootstrap/atomic_write_tagged_text_probe.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/fixtures/bootstrap/atomic_write_tagged_text_probe.spl)
- Review rationale: Current boxed-text registry gives both atomic write externs indices[0,1], matching report's raw-pointer versus tagged-text cause. Real fixture checks multiline persisted readback and empty replacement. Registry-only historical PASS does not qualify changed compiler atomic roundtrip.
- Review corrections: reproducibility: reproducible -> untested; Historical execution is not current reproduction; source/report limits stated explicitly.

## backend_interpreter_symbol_type_unresolved_monomorphize_2026-08-11 — backend/interpreter.spl `unresolved type: Symbol` at stage4 native-build

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/backend_interpreter_symbol_type_unresolved_monomorphize_2026-08-11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/backend_interpreter_symbol_type_unresolved_monomorphize_2026-08-11.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/interpreter.spl:10](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/70.backend/backend/interpreter.spl#L10); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:231](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl#L231)
- Review rationale: Full report already observed HirSymbol/SymbolId and no direct Symbol at historical failure; it hypothesizes transitive alias registration or stale producer. Current successor retains those names and terminal-kind alias handling, but that does not identify missing transitive type in failing Stage4 producer. Keep known remedy unproven.
- Review corrections: solution: known -> unknown; structural_change: yes -> unknown; recommended_action: fixed_pending_verification -> keep_open; Raw known fix inferred from absence of bare Symbol was insufficient: report already observed same absence.

## bare_result_return_type_any_payload_2026-10-24 — bare result return type any payload (workaround registered)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bare_result_return_type_any_payload_2026-10-24.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/bare_result_return_type_any_payload_2026-10-24.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/linker/linker_wrapper_helpers.spl:160](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/70.backend/linker/linker_wrapper_helpers.spl#L160)
- Review rationale: Report's bare Result yielded Any payload rejected by MIR. Current find_runtime_binary spells Result<text,text> under explicit workaround. Type-check rejection versus return-based inference remains undecided; annotation is not a general compiler remedy.
- Review corrections: reproducibility: reproducible -> untested; structural_change: yes -> unknown; Historical execution is not current reproduction; source/report limits stated explicitly.

## bidirectional_checker_missing_provider_imports_2026_10_12 — Bidirectional checker lacks explicit declaring-provider imports

- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/30.types/bidirectional_checking.spl:10](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/30.types/bidirectional_checking.spl#L10); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/30.types/bidirectional_checking.spl:638](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/30.types/bidirectional_checking.spl#L638); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/30.types/bidirectional_inferencer.spl:15](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/30.types/bidirectional_inferencer.spl#L15); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/30.types/bidirectional_types.spl:106](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/30.types/bidirectional_types.spl#L106); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/hir/bidirectional_checker_source_hir_spec.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/compiler/hir/bidirectional_checker_source_hir_spec.spl)
- Review rationale: Current checker explicitly imports types and reexports TypeInferencer; inferencer imports nominal providers. BidirOption replaces builtin-colliding custom Option across return/let contracts. Actual three-source HIR spec checks zero errors and nominal owner plus inference semantics. Cross-module nominal contract repair is present but unexecuted.
- Review corrections: validity: uncertain -> valid; solution: unknown -> known; recommended_action: keep_open -> fixed_pending_verification; Source repair independently traced through three owners and actual regression; no historical/current execution conflation.

## bin_caret_dropped_native_only_launcher_policy_2026-09-06 — bin/caret dropped its native-only launcher policy (2 of 3 committed spec examples fail; deliberately not fixed)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:bin/caret:45](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/bin/caret#L45)
- Review rationale: Full report tracks native-only policy loss and explicitly rejects weakening live spec. Current wrapper still execs runtime run with CARET_ENTRY after version probe; native artifact/fallback policy absent. Restore requires qualified artifact and full sibling cs contract review; workaround/deployment blocker is not invalidity.
- Review corrections: reproducibility: reproducible -> untested; solution: known -> unknown; structural_change: no -> unknown; recommended_action: fixed_pending_verification -> keep_open; Historical execution is not current reproduction; source/report limits stated explicitly.

## block_error_span_source_metadata_loss_2026_10_12 — Block error spans lose source filename

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/15.blocks/blocks/error_helpers.spl:35](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/15.blocks/blocks/error_helpers.spl#L35); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/fixtures/compiler/block_error_span_native.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/fixtures/compiler/block_error_span_native.spl); `7847623d84d73438e04f40ce05ed61f129283cf2`
- Review rationale: Both error constructors now preserve ctx.payload_span.file and existing offset/length semantics. Actual fixture asserts file, nonzero offsets, ranges and empty span. Source unchanged since inventory; historical recovered-seed focused PASS is separate from current production qualification.
- Review corrections: reproducibility: reproducible -> untested; Historical execution is not current reproduction; source/report limits stated explicitly.

## block_highlighting_raw_escape_native_hex_2026_10_12 — Block highlighting raw escapes and missing native hex method

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/15.blocks/blocks/highlighting.spl:104](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/15.blocks/blocks/highlighting.spl#L104); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/15.blocks/blocks/highlighting.spl:224](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/15.blocks/blocks/highlighting.spl#L224); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/blocks/highlighting_native_contract_spec.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/compiler/blocks/highlighting_native_contract_spec.spl)
- Review rationale: Frozen description identifies unavailable str.is_hex_digit and raw escaped-text comparisons. Current strings compare backslash as escaped double-quoted text and numbers call imported binary_inspect is_hex_digit. Actual spec checks escaped quote, comment newline, hex and signed-exponent spans. Narrow source remedy present; latest producer qualification absent.
- Review corrections: Raw historical/native qualification remains untested; source remedy supported by actual functions/tests.

## bootstrap-builder-owner-native-string-methods-2026-09-30 — bootstrap-builder-owner-native-string-methods-2026-09-30

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/windows_process_owner.spl:99](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/io/windows_process_owner.spl#L99)
- Review rationale: Current _windows_upper_ascii_v1 preserves non-ASCII byte spans using codepoint width while converting ASCII lowercase, marked as workaround for60b93 text.to_upper/text.chars lowering. No separate report or failing original expression is supplied; this consumer demonstrates workaround only, not defect validity/root fix.
- Review corrections: structural_change: yes -> unknown; Annotation/source investigation supports uncertainty, not inferred structural compiler remedy.

## bootstrap_admission_producer_selftest_greps_wrong_file_2026-09-05 — Bootstrap admission producer `--selftest` greps the wrong file and always FAILs

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bootstrap_admission_producer_selftest_greps_wrong_file_2026-09-05.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/bootstrap_admission_producer_selftest_greps_wrong_file_2026-09-05.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-bootstrap-planner-admission-producer.shs:45](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/check/check-bootstrap-planner-admission-producer.shs#L45); `/tmp/simple-bug-triage-review-20261027/context/compact_notes.md`; `/tmp/simple-bug-triage-review-20261027/context/triage_comments_draft.tsv`
- Review rationale: Checker now assigns actual producer script and greps entry-closure/current planner_entry_rel, directly fixing wrong-file assertion. Blob unchanged inventory-to-target.17-fixture host run was reported but retained output/source-bound receipt unavailable; root explicitly confirmed no replay and current classification untested.
- Review corrections: reproducibility: unreproducible -> untested; inspection_level: executed -> source_reviewed; Historical execution remains untested for target; independently observed current source differs from raw claims where stated.

## bootstrap_dual_planner_receipts_share_planner_artifact_2026_10_19 — Producing the Stage 3 and managed Stage 4 planner receipts in one run overwrites the shared planner binary and unbinds the Stage 3 receipt

- Classification: `valid`, `untested`, `known`, structural change `unknown`; action `fix_candidate`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bootstrap_dual_planner_receipts_share_planner_artifact_2026_10_19.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/bootstrap_dual_planner_receipts_share_planner_artifact_2026_10_19.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs:268](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs#L268); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/lib/bootstrap-planner-admission-bound.shs:253](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/check/lib/bootstrap-planner-admission-bound.shs#L253)
- Review rationale: Current scope_key uses runtime+closure only, canonical directory omits target, producer removes that directory then rebuilds planner; target-specific receipts can bind sequentially overwritten bytes. Preserve one immutable bound planner for both receipts or introduce target-distinct producer/verifier path binding. Alternative remedies differ in structural scope.
- Review corrections: reproducibility: reproducible -> untested; structural_change: no -> unknown; inspection_level: report_reviewed -> source_reviewed; Historical execution remains untested for target; independently observed current source differs from raw claims where stated.

## bootstrap_facade_check_silent_exit_on_symlinked_pwd_2026-08-31 — bootstrap-from-scratch.sh exits 1 silently when invoked from a symlink-aliased PWD

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bootstrap_facade_check_silent_exit_on_symlinked_pwd_2026-08-31.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/bootstrap_facade_check_silent_exit_on_symlinked_pwd_2026-08-31.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh:1043](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/bootstrap-from-scratch.sh#L1043); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/lib/bootstrap-stage3-provenance.shs:28](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/check/lib/bootstrap-stage3-provenance.shs#L28)
- Review rationale: Current constructor resolves script/repo using pwd-P before exporting facade path; facade also resolves physical directory and emits explicit mismatch diagnostic. Both address full report's logical-versus-physical silent refusal. Symlink-PWD bootstrap not executed here.
- Review corrections: reproducibility: reproducible -> untested; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> fixed_pending_verification; Historical execution remains untested for target; independently observed current source differs from raw claims where stated.

## bootstrap_flat_function_tail_local_payload_loss_2026-08-16 — Legacy flat function lowering can replace a present tail with local zero

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fix_candidate`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bootstrap_flat_function_tail_local_payload_loss_2026-08-16.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/bootstrap_flat_function_tail_local_payload_loss_2026-08-16.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/module_lowering.spl:1499](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLowering/module_lowering.spl#L1499)
- Review rationale: Dormant method still lowers optional tail and uses result??LocalId(0) under presence guard. Full report explains mixed-tail payload hazard and no observed caller. Adopt existing scalar last-block-result contract before reactivation; no present runtime reproduction is inferred from dormant code.
- Review corrections: inspection_level: report_reviewed -> source_reviewed; recommended_action: keep_open -> fix_candidate; Historical execution remains untested for target; independently observed current source differs from raw claims where stated.

## bootstrap_frontend_budget_pins_one_hir_worker_2026-10-19 — Bootstrap frontend policy pins SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=3000000 and tree-rss-policy prices a job at 96 MiB (codegen shard) so the enforced cap sits on the 5.59 GiB floor: the shard clamp admits one HIR worker at any thread count

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/lib/tree-rss-policy.shs:103](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/lib/tree-rss-policy.shs#L103); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/lib/product-frontend-policy.shs:29](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/lib/product-frontend-policy.shs#L29); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/tests/phase-c-frontend-policy-test.shs](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/tests/phase-c-frontend-policy-test.shs)
- Review rationale: Current fanout-host default is5120MiB per job and product frontend share uses actual enforced cap; Windows retains intentional96MiB/pinned policy. Test exercises actual child environment for both backends, explicit narrower budget and contradictions. This addresses old floor/one-worker mismatch within existing budget fields; host runtime scaling remains untested.
- Review corrections: reproducibility: reproducible -> untested; structural_change: yes -> no; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> fixed_pending_verification; Raw fixed3m/floor assertion is stale; structural yes not required for this existing-contract pricing/share correction.

## bootstrap_full_inventory_truncated_after_tool_failure_2026_10_12 — Full keep-going bootstrap truncates diagnostic inventory after tool failure

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bootstrap_full_inventory_truncated_after_tool_failure_2026-10-12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/bootstrap_full_inventory_truncated_after_tool_failure_2026-10-12.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-phase-verification.shs:318](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/bootstrap-phase-verification.shs#L318); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-verification-campaign.shs:12](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/bootstrap-verification-campaign.shs#L12); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/tests/full-inventory-selection-test.py](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/tests/full-inventory-selection-test.py)
- Review rationale: Full keep-going policy now resolves effective limit0 before actual selector, while fail-fast/slim retain configured cap. Real synthetic selector test checks14133selection,14125resumption and retained-failure status. Default8 alone is stale evidence; native inventory qualification remains untested.
- Review corrections: reproducibility: reproducible -> untested; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> fixed_pending_verification; Historical execution remains untested for target; independently observed current source differs from raw claims where stated.

## bootstrap_imported_free_method_rebind_2026_10_12 — Imported libc free rebinds to RtStringBuilder.free in bootstrap closure

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/imports.rs:790](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/compiler/src/pipeline/native_project/imports.rs#L790); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/fixtures/repro/compiler/bootstrap_imported_free_method_rebind/actual_path_identity.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/fixtures/repro/compiler/bootstrap_imported_free_method_rebind/actual_path_identity.spl)
- Review rationale: Frozen account retains libc free rebound to builder method and failed local-extern workaround. Current global import-map selection now prioritizes exact extern identity over bare method fallback; real fixture exercises path_identity cleanup alongside RtStringBuilder.free. LLVM downstream use and producer binding remain untraced, so this is repair lead rather than complete qualification.
- Review corrections: validity: uncertain -> valid; structural_change: yes -> unknown; Raw source point476 is stale; actual matching repair lead is790. No producer-level PASS inferred.

## bootstrap_raw_byte_loop_unbox_2026_10_16 — inspect-codepoints-without-decoding-raw-u8-words-as-tagged-integers

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_build/native_entry_closure_receipt.spl:75](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_build/native_entry_closure_receipt.spl#L75)
- Review rationale: Current root validator checks forbidden path syntax then iterates text codepoints to reject C0/DEL, marked raw-u8 tagged-integer decoding workaround. No original byte-loop failure or compiler decoding owner diagnosis is supplied; source workaround does not establish known root fix.
- Review corrections: validity: valid -> uncertain; solution: known -> unknown; structural_change: no -> unknown; Raw valid/known/no claims were unsupported by annotation alone; conservative uncertainty after actual predicate inspection.

## bootstrap_scv_literal_brace_source_identity_2026_10_12 — SCV guard rejects literal tracked brace filenames

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/lib/BootstrapProductScv.pm:84](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/lib/BootstrapProductScv.pm#L84)
- Review rationale: source_path now includes escaped literal braces in restricted src/test alphabet while rejecting empty,dot,parent components. This directly addresses authenticated literal brace filenames in full report without shell expansion or deleting inputs. New sealed bundle/generator post-verification remains unqualified.
- Review corrections: reproducibility: reproducible -> untested; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> fixed_pending_verification; Historical execution is not current reproduction; source/report limits stated explicitly.

## bootstrap_watchdog_wall_clock_budget_2026_10_11 — Watchdog elapsed budgets follow civil-clock adjustments

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/resource/process-tree-rss-watchdog.pl:12](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/resource/process-tree-rss-watchdog.pl#L12); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-watchdog-monotonic-budget.py](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/check/check-watchdog-monotonic-budget.py)
- Review rationale: Current watchdog uses CLOCK_MONOTONIC for starts/deadlines/cadence and validates startup defined/nonnegative before forks. Python control extracts actual helpers/expressions and has12 meaningful simulated clock assertions. Historical clock-step causation is unproven; source remedy is local and workload qualification remains outstanding.
- Review corrections: reproducibility: reproducible -> untested; Historical execution is not current reproduction; source/report limits stated explicitly.

## borrowed_dict_index_owner_2026_10_11 — Borrowed Dict indexing lowers text keys as array offsets

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fix_candidate`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:683](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl#L683); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:707](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl#L707); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:2488](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl#L2488)
- Review rationale: Exact Dict/Ref(Dict) helper exists, but local_is_runtime_dict still tests only bare Dict and getter MIR recovery also tests bare Dict. Compound read references helper. Concrete local remedy is consistently use existing exact view helper for predicate/getter while retaining HIR decode and negative Ptr/Ref(Array) exclusions; not a completed repair.
- Review corrections: structural_change: yes -> no; Historical execution is not current reproduction; source/report limits stated explicitly.

## bounded_read_limit_allocation_2026_10_12 — Bounded regular-file reads eagerly allocate the policy limit

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bounded_read_limit_allocation_2026-10-12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/bounded_read_limit_allocation_2026-10-12.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:14071](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/runtime/runtime_native.c#L14071)
- Review rationale: Both public bounded readers call one handle-admitted helper, allocate stat size+1, grow geometrically within limit, cap each read1MiB and free/close on error. This matches concrete over-allocation root remedy. Focused historical Linux42case evidence does not qualify new compiler or explain separate29GiB OOM.
- Review corrections: reproducibility: reproducible -> untested; inspection_level: report_reviewed -> source_reviewed; Historical execution is not current reproduction; source/report limits stated explicitly.

## brace_dictionary_type_tags_discarded_2026-10-05 — Brace dictionary annotations discard key and value type tags

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/brace_dictionary_type_tags_discarded_2026-10-05.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/brace_dictionary_type_tags_discarded_2026-10-05.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser.spl:1383](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/parser.spl#L1383)
- Review rationale: Brace annotation now retains key/value parser tags through dict_type_register and optional suffix just like Dict<K,V>. Original discarded children explain Any erosion without changing runtime ABI. Full report's real structural/native tests remain unexecuted in this audit.
- Review corrections: reproducibility: reproducible -> untested; inspection_level: report_reviewed -> source_reviewed; Historical execution is not current reproduction; source/report limits stated explicitly.

## browser_dom_event_object_gc_retention_2026-07-31 — Browser DOM event object GC reachability reclamation not implemented

- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/browser_dom_event_object_gc_retention_2026-07-31.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/browser_dom_event_object_gc_retention_2026-07-31.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/02_integration/rendering/browser_session_event_retention_spec.spl:59](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/02_integration/rendering/browser_session_event_retention_spec.spl#L59); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/script/event_api.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/gpu/browser_engine/script/event_api.spl)
- Review rationale: Full report tracks retained JS event objects while allowing page references. Actual regression asserts stable native/global registration counts but growing object store. Current event_api only routes DOM events; VM reachability across globals/callbacks/listeners requires cross-owner reclamation, not immediate event deletion.
- Review corrections: validity: uncertain -> valid; Old source lines/measurements and historical execution are not current qualification.

## browser_engine_css_contain_size_unimplemented_2026-08-08 — CSS contain:size parses but is never consulted by the sizing pass

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/containment.spl:5](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/gpu/browser_engine/containment.spl#L5); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout_engine.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout_engine.spl); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/gui/web_css/web_css_visibility_containment_spec.spl:262](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/03_system/gui/web_css/web_css_visibility_containment_spec.spl#L262)
- Review rationale: Full report and real geometry spec require height5 independent of child40. Containment owner explicitly excludes size and successor layout engine has no contain-size/intrinsic read. Missing feature remains valid; complete sizing remedy and scope need design.
- Review corrections: solution: known -> unknown; structural_change: yes -> unknown; recommended_action: fix_candidate -> keep_open; Old source lines/measurements and historical execution are not current qualification.

## browser_engine_css_position_fixed_not_viewport_anchored_2026-08-08 — position:fixed resolves against nearest ancestor not the viewport

- Classification: `valid`, `untested`, `known`, structural change `unknown`; action `fix_candidate`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout_engine.spl:1645](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout_engine.spl#L1645); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout_foundation.spl:355](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout_foundation.spl#L355); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/gui/web_css/web_css_positioning_spec.spl:172](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/03_system/gui/web_css/web_css_positioning_spec.spl#L172)
- Review rationale: Successor engine absolute-position branches pass parent x/y into offset helpers and never inspect position_fixed. Foundation fixed reads merely exclude margin collapse. Real spec requires viewport(1,2) inside20px margin. Remedy is fixed-specific viewport containing-block selection across existing layout branches; no runtime result claimed.
- Review corrections: structural_change: yes -> unknown; Old source lines/measurements and historical execution are not current qualification. Structural scope remains unknown until viewport geometry propagation through recursive layout contracts is traced.

## browser_engine_table_row_horizontal_layout_2026-07-11 — browser_engine: table rows lay cells vertically (no horizontal table layout)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/browser_engine_table_row_horizontal_layout_2026-07-11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/browser_engine_table_row_horizontal_layout_2026-07-11.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout_engine.spl:435](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout_engine.spl#L435)
- Review rationale: Full historical report's unwired table-flow premise no longer describes current engine: it imports layout_table, calculates columns, advances cell offsets and equalizes row heights. Tag defaults/default auto-sizing reachability and original HN fixture remain unqualified, so no complete fix or current failure is claimed.
- Review corrections: solution: known -> unknown; structural_change: yes -> unknown; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> keep_open; Historical execution remains untested for target; independently observed current source differs from raw claims where stated.

## browser_engine_text_metrics_api_drift_2026-07-20 — browser_engine text-metrics spec: residual API gaps after content_x/y landed

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl:30](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl#L30); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/layout_box.spl:92](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/gpu/browser_engine/layout_box.spl#L92)
- Review rationale: Full report separates four API/resource failures. Current BeLayoutBox supplies content_x/content_y methods and BeRenderResult definition still lacks reported warnings field in inspected definition. Missing probe function/resource nil path remain unqualified; one API addition does not establish complete repair.
- Review corrections: validity: uncertain -> valid; structural_change: yes -> unknown; Old source lines/measurements and historical execution are not current qualification.

## browser_engine_wikipedia_render_perf_2026-07-11 — Real-page software render is ~176s interpreted; 10s budget always degrades

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:2191](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl#L2191)
- Review rationale: Full report preserves interpreted real-page throughput and budget overshoot independently from fixed blank degraded output. Current renderer still partitions style70%, layout90%, paint100% and invokes real style computation. That mitigation does not establish throughput fix; needs representative bound performance evidence.
- Review corrections: structural_change: yes -> unknown; Old source lines/measurements and historical execution are not current qualification.

## browser_layout_module_exceeds_128kib_parser_limit_2026-07-31 — Four browser layout modules exceed the 128 KiB parser limit

- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fix_candidate`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_module_split_spec.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_module_split_spec.spl); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_decl_apply.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_decl_apply.spl)
- Review rationale: Full report requires lossless layer-preserving split and byte conservation. Exact target has18family blobs; original layout is95B facade, engine125923B, foundation109845B, but decl_apply132899B exceeds131072. Current spec discovers all family inputs and checks strict size bound. Complete lossless split of remaining oversized owner; parser/RSS qualification absent.
- Review corrections: Old source lines/measurements and historical execution are not current qualification.

## bug_add_rename_path_recursion_rewrites_db_2026-10-04 — bug-add crashes with rename_path infinite recursion, and its bug_db.sdn.tmp drops ~1700 existing lines

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bug_add_rename_path_recursion_rewrites_db_2026-10-04.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/bug_add_rename_path_recursion_rewrites_db_2026-10-04.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io_runtime.spl:500](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/io_runtime.spl#L500)
- Review rationale: Full report preserves two independent defects: recursion at rename and temporary DB losing rows. Current wrapper only calls rt_file_rename in unsafe FFI; source itself has no recursion. Dispatch identity and serialization preservation need diagnosis; do not merge temporary DB or assume fixing rename prevents loss.
- Review corrections: reproducibility: reproducible -> untested; structural_change: yes -> unknown; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> keep_open; Historical execution is not current reproduction; source/report limits stated explicitly.

## bug_add_seed_rename_path_stack_overflow_2026_10_19 — bug-add on the Rust seed overflows the stack in rename_path and saves nothing

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bug_add_seed_rename_path_stack_overflow_2026_10_19.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/bug_add_seed_rename_path_stack_overflow_2026_10_19.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io_runtime.spl:500](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/io_runtime.spl#L500)
- Review rationale: Distinct later seed report reproduces rename recursion and explicitly leaves chosen wrapper unestablished. Current rename_path remains direct runtime extern; relation to earlier record does not invalidate it. Root extern-dispatch binding is still unknown.
- Review corrections: reproducibility: reproducible -> untested; structural_change: yes -> unknown; inspection_level: report_reviewed -> source_reviewed; Historical execution is not current reproduction; source/report limits stated explicitly.

## byte_at_reads_zero_from_slice_result_2026-07-28 — `byte_at()` reads zeros out of a `slice()` result

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/byte_at_reads_zero_from_slice_result_2026-07-28.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/byte_at_reads_zero_from_slice_result_2026-07-28.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/tls/_TlsUtilities/hex_encoding.spl:342](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/tls/_TlsUtilities/hex_encoding.spl#L342)
- Review rationale: Actual byte_at nil/bounds guards then indexes; slice copies using byte_at and append. Full report isolates sliced versus literal arrays but does not explain representation/dispatch difference. No obvious local zero fill exists; preserve genuine historical symptom and unknown compiler/runtime remedy.
- Review corrections: reproducibility: reproducible -> untested; structural_change: yes -> unknown; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> keep_open; Historical execution is not current reproduction; source/report limits stated explicitly.
