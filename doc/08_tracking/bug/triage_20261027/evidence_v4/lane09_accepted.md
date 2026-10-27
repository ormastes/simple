# V4 lane 09 accepted evidence

Accepted classifications in V4: 149. Assessment target: `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`.

- 70 accepted records are inherited field-for-field from V3; their detailed evidence is preserved in [V3 lane 09 evidence](../evidence_v3/lane09_accepted.md).

- 79 additional accepted records are detailed below.

## text_to_bytes_method_missing_on_text_receiver_2026-09-06 — `"lit".to_bytes()` — method not found on `text`

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fix_candidate`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/text_to_bytes_method_missing_on_text_receiver_2026-09-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_method/string.rs:18-31; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/text_bytes.spl:26-39; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/plan_acceptance/cuda_host_validation_spec.spl:76-84
```
- Review rationale: The report targets the Rust seed interpreter, not the pure-Simple interpreter as low research inferred. Independently inspected seed string receiver dispatch: bytes produces the UTF-8 byte array at string.rs:28-30, while scoped dispatch search has no to_bytes arm. The free function does not provide receiver syntax. Add the to_bytes receiver alias to the existing conversion; CUDA API qualification remains a separate blocker.
- Review corrections: solution: unknown -> known; structural_change: unknown -> no; recommended_action: keep_open -> fix_candidate. Low research attributed seed report to pure-Simple interpreter. Current seed receiver owner independently located; local bytes alias remedy supported. See independent rationale.

## three_computedstyle_concepts_2026-08-10 — three unrelated ComputedStyle types coexist (blink entity, browser_engine style, ui) with

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/three_computedstyle_concepts_2026-08-10.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/blink/entity/computed_style.spl:97-120,153-180; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/style/computed.spl:19-54; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/style/animation_controller.spl:42-59; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/ui/render_opt/web_style.spl:155-205
```
- Review rationale: Three current roles remain distinct: Blink typed properties implement layout/visibility decisions; WebComputedStyle stores CSSDeclaration and animation_controller diffs property values; ComputedStyleHot stores interned IDs/flags and apply_declarations visits decls.count. The browser type was renamed, but these roles cannot be collapsed merely because their old names matched. Intentional architectural debt remains; no demonstrated root consolidation remedy.
- Review corrections: inspection_level: report_reviewed -> source_reviewed.  See independent rationale.

## tiny_ui_web_wm_integration_blockers_2026-08-14 — Tiny UI/Web/WM integration blockers

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/tiny_ui_web_wm_integration_blockers_2026-08-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/tiny_browser/app.spl:88-123,198-223; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/services/tiny_wm/model.spl:257-277; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/app/tiny_browser/feature/tiny_ui_web_wm_spec.spl:24-28
```
- Review rationale: Full blocker report requires fourteen independent functional/target/allocation conditions. Current TinyBrowser retains WM/present and arena fields, and TinyWmKiosk derives direct_present from one visible opaque full-output root. Those source conditions support partial repair but not target evidence or no-hidden-allocation. Broad blocker remains open, with per-owner and external allocator qualification required; no whole-family remedy established.
- Review corrections: inspection_level: report_reviewed -> source_reviewed.  See independent rationale.

## tls_no_fd_upgrade_blocks_starttls_2026-08-25 — TLS facade cannot upgrade an existing fd — STARTTLS (SMTP 587 / IMAP 143) is unimplementable

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/tls_no_fd_upgrade_blocks_starttls_2026-08-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/tls_sffi.spl:18-33; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_https_openssl_core.c:370-433; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/llm_caret/infra_mail.spl:439-450
```
- Review rationale: Current TLS facade/provider exports connect-by-host/address, with SSL_connect and failure cleanup of its newly created connection. mail_send explicitly refuses port587 before acquiring a socket. The reported missing in-place upgrade remains a concrete API/ownership gap; the proposed success-only fd ownership transfer has no implementation or failure-cleanup proof, so solution remains unknown.
- Review corrections: structural_change: unknown -> yes.  See independent rationale.

## tls_signature_positive_verification_blockers_2026-06-06 — TLS signature verification has no positive test: ed25519/RSA-PSS/cert-chain specs cannot

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/tls_signature_positive_verification_blockers_2026-06-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/sffi/signature.rs:256-279,363-394; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/os/os_rt_ed25519_sign_spec.spl:118-143; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/os/os_tls_cert_chain_spec.spl:80-103
```
- Review rationale: Report records positive Ed25519/RSA-PSS rejection despite negative checks. Current Rust provider invokes ring verification and checked key/signature length gates; chain spec still requires valid RSA-PSS and an anchored positive chain. Positive oracles exist but were not executed, and provider presence does not identify or resolve the historical interop root. Preserve open and untested.
- Review corrections: inspection_level: report_reviewed -> source_reviewed.  See independent rationale.

## to_equal_treats_nil_as_false_green_2026-09-01 — `expect(nil).to_equal(false)` passes — `to_equal` disagrees with `==` (2026-09-01)

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/to_equal_treats_nil_as_false_green_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/bdd.rs:722-753,1175-1229,1326-1342; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_method/mod.rs:580-596; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/value.rs:3252-3256
```
- Review rationale: Low research inspected the matcher constructor, but actual chained to_equal calls nullable_eq in interpreter_method/mod.rs:580-596. More decisively, expect rewrites a direct ExistsCheck subject into Bool at bdd.rs:1336-1341. Thus the report reproducer d.get(missing).? is converted before equality, so strict nil equality does not demonstrate repair. Literal nil and the reported optional-expression shape must be separated; intended assertion/operator contract remains unresolved.
- Review corrections: inspection_level: report_reviewed -> source_reviewed. Reject low fixed-source inference: actual chained matcher and assertion-specific ExistsCheck coercion differ from MatcherValue::Exact path. See independent rationale.

## top_level_array_index_assign_in_loop_silently_dropped_2026-08-25 — Module-level `arr[i] = arr[i] + 1` inside a top-level loop is silently dropped (2026-08-25)

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/top_level_array_index_assign_in_loop_silently_dropped_2026-08-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter/node_exec.rs:336-344; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_control.rs:384-413,3846-3885
```
- Review rationale: Full report update broadens failure from array writes to top-level scalar/loop-state loss, sensitive to declaration count and position. Current node_exec dispatches while/for with mutable environment; exec_while has shape-specialized fast paths and exec_for temporarily installs then restores loop bindings. These owners do not establish where module scope is discarded, nor does array_set repair answer the report. No root remedy identified; preserve exact multi-declaration fixtures for eventual qualification.
- Review corrections: inspection_level: report_reviewed -> source_reviewed.  See independent rationale.

## trait_conformance_check_ignores_arity_2026-08-04 — trait conformance matches by method NAME only; parameter types are never compared

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/trait_conformance_check_ignores_arity_2026-08-04.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_eval.rs:138-162,1060-1135
```
- Review rationale: The report explicitly ends ARITY ARMED / TYPES OPEN. Current interpreter_eval compares receiver-normalized arities of each matched method and accumulates problems, but does not compare parameter types in that loop. This is stronger than low research inspecting only the standalone census checker. Cross-backend conformance and same-arity type drift remain unresolved; no full remedy established.

## trait_default_body_segfaults_via_trait_object_2026-08-06 — a trait method with a default body segfaults when invoked through a trait object

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/trait_default_body_segfaults_via_trait_object_2026-08-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/fixtures/repro/compiler/trait_default_body_segfault/probe3_trait_default_body_crashes.spl:54-106; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs:2210-2255; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/common_backend.rs:2038-2074
```
- Review rationale: The report rules out a universal missing-default-body explanation: AOT controls worked while a healthy JIT was unavailable. Reconstructed fixture invokes a default me body containing fn calls. Current module_pass injects per-impl default bodies; common_backend relocates method slots and leaves absent entries zero, with additional selfless thunks. Neither observation identifies the crashing JIT slot or receiver dispatch. Do not infer a fix from default injection alone.
- Review corrections: inspection_level: report_reviewed -> source_reviewed.  See independent rationale.

## transient_empty_scope_highwater_scan_2026_10_12 — Empty transient scopes scan prior allocation high water

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bug_db.sdn (matching transient description); c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:1918-1940,2183-2200,2530-2550; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_memory.c:229-265; historical d47c62df389 inspected via git log bound to c0b3ad911f4cb00c0f3550b05baa8d06347d17d0
```
- Review rationale: Frozen DB description names an owner-mode1 candidate, not a current runtime PASS. Independently inspected d47c62df389 in c0 ancestry: it adds the raw-table empty-length return retained at runtime_native.c:2183-2189, clearing tombstones if necessary. Scope end invokes this owner, while non-owner runtime_memory uses a separate guarded scan. This is a bounded remedy for empty raw-table high-water scanning; other immortal-object scans and cross-platform/full-compiler qualification remain outside the demonstrated fix.
- Review corrections: validity: uncertain -> valid; solution: unknown -> known; structural_change: unknown -> no; recommended_action: keep_open -> fixed_pending_verification. Upgrade unknown to known bounded raw-table source remedy after actual historical diff; no current performance reproduction inferred. See independent rationale.

## tree_size_guard_hangs_on_btrfs_metadata_exhaustion_2026-08-11 — `check-tree-size-push.shs` scan phase stalls for 15-20+ min — root cause: btrfs metadata-chunk exhaustion, not the script

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/tree_size_guard_hangs_on_btrfs_metadata_exhaustion_2026-08-11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-tree-size-push.shs:157-198,236-266,945
```
- Review rationale: Full report contains measured write/CPU progress and Btrfs metadata exhaustion, distinguishing extreme slowness from deadlock. Current guard uses mktemp scratch and writes parsed tree listings there; EXIT/signal cleanup cannot survive SIGKILL. Operational restoration of filesystem headroom addresses the reported bottleneck. Current guard now uses one cached ls-tree listing, so the report two-call description is historical. No host maintenance or runtime verification performed; guard rules remain intact.
- Review corrections: solution: unknown -> known; structural_change: unknown -> no; inspection_level: report_reviewed -> source_reviewed. Current guard uses one cached full tree listing, not report historical pair; no current host condition inferred. See independent rationale.

## treesitter_node_module_missing_and_spec_tautological_2026-08-04 — std.parser.treesitter_node does not exist and its spec asserts nothing, so the red is

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/treesitter_node_module_missing_and_spec_tautological_2026-08-04.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/std/parser/treesitter_node_spec.spl:32-41,54-78,100-136
```
- Review rationale: Full report and current spec support vacuous API-shape tests: Point sign disjunctions, nil-or-not-nil and nonnegative text length cannot validate node behavior. Scoped current library/parser search found no treesitter_node successor; absence remains bounded search evidence. Report overstates result>=0 or result==-1 as universal for every i64 (values below -1 fail), so its exact 19/23 count is not endorsed. Missing API and vacuous examples remain real; implement-versus-remove owner decision is unresolved.
- Review corrections: inspection_level: report_reviewed -> source_reviewed. Structural yes unsupported before API owner decision; use unknown. Do not repeat report inaccurate universal-i64 or exact vacuity-count claim. See independent rationale.

## type_alias_static_dispatch_unresolved_2026-08-04 — `type X = Y` does not resolve as a static-call receiver — X.new() sees nil

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:NONE; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs:452; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_eval.rs:1228; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl:860
```
- Review rationale: The full report distinguishes imported DbfsWal.new from direct SharedWal.new. Independently inspected the seed module exporter: Node::TypeAlias explicitly inserts Value::Nil into both exports and env, whereas interpreter_eval can bind local aliases to Value::Constructor when the class is known. Thus a local alias facility does not repair the reported imported receiver route. HIR imported nominal forwarding and template registration also exist, invalidating the report's old consumer census without proving this seed route repaired. Keep historical imported-dispatch defect valid; full root remedy across engines remains unknown.
- Review corrections: Independent review narrows the claim to imported aliases: local constructor binding now exists. Do not repeat blanket claim that aliases never reach any receiver.

## type_alias_swapped_winner_is_inert_2026-08-01 — a swapped duplicate-`type` alias winner is inert: the alias target is never stored

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:NONE; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_declarations_bootstrap.spl:259; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl:860; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/types.spl:1224
```
- Review rationale: Read the whole latent collision report, including its empty reachable divergent-provider census and explicit entry-closure exception. Target local registration stores ParserTypeAlias templates and imported registration guards an existing binding before define; nominal imported aliases can forward to the target symbol. Therefore its discarded-target/zero-reader inertness proof is obsolete. No current reachable divergent collision was established, so uncertain/unknown and keep_open is supported rather than live-miscompile or invalid closure.
- Review corrections: Retain first-pass uncertainty; local and imported registration undermine historical no-target proof, but do not establish present miscompile.

## typed_array_variable_binding_zeroes_elements_2026-08-17 — Binding a typed array variable to another variable zeroes its elements

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/typed_array_variable_binding_zeroes_elements_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/collections.rs:7059; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/codegen/packed_array_copy_roundtrip_spec.spl:150; history a4cc6f61dfb; history 4e24b1b7423
```
- Review rationale: Read the report through fix, deployment caveat and separate u8 aliasing residual. Target rt_array_copy allocates matching packed storage and copies raw words/bytes before generic handling; this directly prevents the reported untagging divide-by-eight. Target regression checks the discriminating large value plus JIT/interpreter equality, not just length or small zeros. Target-bound history locates a4cc6f61dfb and its cherry-pick 4e24b1b7423. Existing local remedy supports fixed_pending_verification for this u64 mechanism; no current deployed result and no claim to fix excluded u8 copy semantics.
- Review corrections: Confirm unknown -> known, structural no, keep_open -> fixed_pending_verification for the packed-copy mechanism only.

## u64_shift_signed_outside_typed_fn_2026-09-03 — u64 shift/display go SIGNED outside a `-> u64` typed function

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/u64_shift_signed_outside_typed_fn_2026-09-03.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter/node_exec.rs:43; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter/node_exec.rs:207; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter/expr/ops.rs:1295
```
- Review rationale: Report's typed val max-u64 loses signedness outside a typed return. Target binding owner now converts annotated integer values to UInt at the declared width, and shift dispatch explicitly uses UInt wrapping_shr/wrapping_shl. Target-bound history for coerce_to_declared_type shows extending this treatment to const/static/module binding sites. This is a causal local remedy for signed binding/shift leakage, pending exact shift/display probe qualification. SIMD wrappers alone would not establish a fix.
- Review corrections: Confirm known local binding/shift remedy and fixed_pending_verification; no present display result asserted.

## u8_cast_push_yields_unpacked_byte_array_2026-09-06 — BUG: `push(x as u8)` grows a `[u8]` whose storage is not byte-packed

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/u8_cast_push_yields_unpacked_byte_array_2026-09-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter/node_exec.rs:43; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_method/collections.rs:1200; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/structural/wire.spl:108; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/common/structural/u8_push_byte_packing_spec.spl:27
```
- Review rationale: Full report and exact regression distinguish equal indexed bytes from wrong wire reconstruction. Typed empty [u8] binding now produces ByteArray; handle_byte_array_methods delegates then repacks UInt or Int byte-range results. This addresses construction layout without relying on masking workaround. Current wire_get readers perform indexed masked reconstruction, and regression checks both u64 and u32 cast-push shapes. Existing packing remedy is causally supported, but receiver writeback and real interpreter run remain qualification work.
- Review corrections: Confirm known/no/fixed_pending_verification for binding and byte-result preservation; do not describe current wire.spl as a direct raw-pointer reader.

## ui_web_ws_any_cast_fails_in_spawned_thread_2026-08-04 — Web server dies on first WebSocket upgrade: `as TcpStream` cast fails in spawned reader thread

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/ui_web_ws_any_cast_fails_in_spawned_thread_2026-08-04.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/ui.web/async_ws.spl:24; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/ui.web/async_server.spl:292; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/concurrent/thread.spl:163; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/concurrency.rs:437
```
- Review rationale: The full report isolates Any-to-TcpStream cast after spawn. Target reader takes TcpStream and BoundedChannel directly and the async server passes those values through generic thread_spawn_with_args. The inspected seed context handler clones arguments and executes synchronously with supplied class tables. This avoids the exact cast and differs from true native worker transport; it does not prove general class-registry repair or a working asynchronous WebSocket upgrade. Historical defect stays valid/open with unknown root remedy.
- Review corrections: Explicitly qualify seed spawn context as synchronous; no inference that real threaded class transport was repaired.

## undefined_import_called_exits_zero_2026-08-17 — An import that exists nowhere, called off the executed path, exits 0

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/undefined_import_called_exits_zero_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:518
```
- Review rationale: Full report identifies off-path unresolved import, distinguishing on-path error and strict-JIT recommendation. Target warn_unprovided_use_names returns unit, skips opaque/group-unavailable cases and prints eprintln diagnostics without propagating an error. Therefore inspected owner still implements warning severity; a known-red guard does not repair it. Historical defect stays valid/open, with unknown approved root policy and current exit code untested.
- Review corrections: No label change; do not promote suggested severity policy to a known implemented solution.

## unit_spec_hangs_42_excluded_2026-08-27 — 42 unit-spec exclusions: measured timeout classification and partial optimization (2026-08-27)

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/unit_spec_hangs_42_excluded_2026-08-27.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/js/engine/interpreter_object.spl:164; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/js/engine/vm_object_store.spl:55
```
- Review rationale: Read retained report's full 40-spec measurement ledger and independent JS/JIT/crypto causes. Historical split is 24 bounded timeouts, eight completions and eight fast failures, not 40 permanent hangs. Target set_object_property synchronizes an ObjectStore property index; find_prop_slot uses it when complete with backward-scan fallback. The report's primary timer per-write global scan claim is consequently stale on that owner. This does not settle other families, JIT stack overflow or crypto causes, so aggregate current validity/remedy stay uncertain/unknown and open; no timing claim is revalidated.
- Review corrections: Accept conservative uncertainty rather than treating all exclusions as hangs or partial indexing as aggregate fix.

## unit_specs_that_never_parse_2026-09-13 — Unit specs that never parse — a whole file's examples vanish with one line of output

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/unit_specs_that_never_parse_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/hardware/rv32i/rv32_sv32_walker_spec.spl:103; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/parser_patterns.rs:87; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/parser_patterns.rs:284
```
- Review rationale: Read complete continuation report: 43 syntax repairs are historical and the capability-registry import failure is distinct. Current RV32 walker still binds val allow. Independently traced seed parse_pattern into parse_single_pattern: its many contextual keyword arms do not include Allow, unlike supported keywords converted to lowercase identifier patterns. This supports the residual parser defect, while full repaired population is not requalified. The report's statement that eleven consumers make a change invasive does not establish necessary architectural restructuring.
- Review corrections: Structural yes -> unknown: a token's existence and consumer count alone cannot prove cross-module contract restructuring is necessary.

## unregistered_extern_silent_nil_2026-08-01 — An unregistered `@extern fn` is not a link error — it is a silent nil, a silent 0, or a SIGILL (2026-08-01)

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_sffi.rs:603; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_sffi.rs:775; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_eval.rs:1157; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/mod.rs:636; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/95.interp/mir_interpreter.spl:1255; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/linker/native_binary/stubs.rs:335
```
- Review rationale: Independently read original syntax split and later diagnostic, strict-prefix, rejected dead-deletion and ratchet corrections. Current interp_call_handler detects terminal prefixed/unprefixed unbacked calls and report_unbacked_extern unconditionally exits 1, superseding the report's old warn-only default. Node::Extern registration and extern dispatch are distinct from bodyless decorator functions; native stub generator still contains zero-return fabrication but its presence alone does not prove hosted reachability. MIR intrinsic misses now record named errors. These mixed per-engine results support a valid historical family with unknown comprehensive remedy, not blanket present silent nil or full closure.
- Review corrections: Do not carry historical warn-only default into current handler claims; target fatal refusal is unconditional. Native generator presence is configuration-limited evidence.

## unresolved_type_declared_nowhere_family_2026-08-01 — lower_named_kind whitelist drift: cross-module struct fallback still reports unresolve...

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:NONE; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/types.spl:1328; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/types.spl:1406; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser.spl:1128
```
- Review rationale: Read class A/B corrections, user-selected aliases, generic erasure mechanism and signedness limit. Target lower_named_kind retains explicit signed/unsigned scalar mappings and owner-qualified alias lookup; parser generic tail now preserves named_generic_instance_register even for forward declarations rather than returning TYPE_ANY. Thus the old blanket name/argument erasure proof no longer applies. Existing support does not qualify all imported structs or cross-engine usize semantics, so current aggregate remains uncertain/open with unknown comprehensive remedy.
- Review corrections: Strengthen stale-claim correction: target generic tail preserves names/arguments even beyond explicitly imported/local bases. No blanket rewrite or full resolution warranted.

## untagged_specs_for_unbuilt_features_2026-09-20 — Untagged specs for functionality that was never built read as regressions

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/untagged_specs_for_unbuilt_features_2026-09-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/spec.spl:1100; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/std/parser/treesitter_node_spec.spl:32
```
- Review rationale: Full report separates missing APIs, a repaired wrong spec and deliberate red tripwires. Target public before_all executes hooks and after_all enqueues them, so two missing-API claims are obsolete. The current TreeSitter node spec still imports the described module and constructs mock Node values; that is intent, not implementation proof. Current roadmap/tag authority and all API exports were not established, supporting uncertain/unknown/open rather than authorizing skips or calling the tracker invalid.
- Review corrections: Accept conservative mixed current status; historical hook absence is false at target, but tagging/skip decisions remain unauthorised.

## unwired_extractions_audit_2026-08-11 — Deduplication extractions were authored and announced Resolved but never wired to consu...

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:NONE; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/cache/native_interface_slice.spl:252; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/cache/native_prelower_object_key.spl:190; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/arch/riscv64/sbi.spl:23
```
- Review rationale: Read complete eight-instance audit and its retractions: zero imports is not dead-code proof and moved RTL/SHA256 paths were falsely diagnosed. Independently found target interface_digest_of is now called by native_interface_whole_digest_v1 and native_prelower_dependency_digest_v1, contradicting the report's zero-caller claim; RISC-V SBI also imports shared constants. This meaningful successor/consumer investigation supports uncertainty for the aggregate, not deletion or invalidity. Remaining CSS/MCP/dependency traversal instances require individual owner traces before any whole-audit closure.
- Review corrections: Promote conservative uncertainty from unexamined after independently locating real new consumers; specifically correct old interface_digest_of zero-caller assertion. No aggregate unwired claim accepted.

## unwrap_family_treats_flat_nil_as_present_2026-09-13 — `unwrap_or` / `unwrap` treat a FLAT nil as a present value (2026-09-13)

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `no`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/unwrap_family_treats_flat_nil_as_present_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/objects.rs:521; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/objects.rs:569; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/objects.rs:609; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/objects.rs:701; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs:963; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_method/mod.rs:1724
```
- Review rationale: Full report and current runtime confirm flat nil is absent in rt_is_none but returned unchanged by three non-enum unwrap helper branches. However independently inspected current interpreter nested dispatcher excludes Value::Nil from bare-present fallback; direct Nil.unwrap_or now returns the argument in interpreter_method/mod.rs. Thus the first-pass blanket all-engine nil-passthrough claim is stale. Runtime flat-nil defect remains valid; native/shared helper guard is local, but complete paired nested/direct/trap remedy remains unknown pending contract and focused qualification.
- Review corrections: Correct first-pass claim that current flat nil reaches unconditional interpreter passthrough: nested route excludes nil and direct unwrap_or selects default. Preserve runtime defect and unknown complete remedy.

## unwrap_still_rebinds_to_poll_unwrap_at_closure_scale_2026-09-13 — `.unwrap()` still rebinds to `Poll.unwrap` at closure scale via a second route (2026-09-13)

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/unwrap_still_rebinds_to_poll_unwrap_at_closure_scale_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs:895; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs:942
```
- Review rationale: Read complete report including unchanged 208/109 after four repairs, null-hypothesis correction and later Linux 210-to-209 site change. Current resolve_call_target preserves bare enum helpers and qualified helpers require exact owner matching. These guards do not identify remaining indirect/closure emitters, and the report itself withdraws proof that all residual symbols are miscompiles. Current aggregate is uncertain/open; next evidence is one surviving receiver and actual Poll.unwrap body, not another unmotivated resolver guard.
- Review corrections: Do not claim 208 is current or all are bad; later report adds 209/109 Linux result and still lacks generic-helper versus Poll-specific adjudication.

## v_lane_suite_occlusion_spec_times_out_under_shared_wc_contention_2026-08-07 — compositor_occlusion_spec times out at the V-lane 600s floor under shared-WC contention

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/os/compositor/compositor_occlusion_spec.spl; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-render-perf-v-lane-suite.shs:40; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/09_report/ui/perf/render_perf_v_lane_promotion_suite_2026-08-06.md:656
```
- Review rationale: Read complete contention report and retained Run5 output: 10 specs passed and occlusion timed out without a verdict. Target runner floors occlusion at 600 and invokes no-cache/no-cover-check; absent verdict is RED. Load average cannot establish proportional slowdown or prove absence of regression, and the source comment is not present performance evidence. Accept uncertain current cause/status, preserve plan bound, and require a retained low-load current run or owner-approved scheduling work.
- Review corrections: Reject report's 'mathematically insufficient' inference from load-average ratios; retain historical timeout without inventing current reproduction or a known remedy.

## value_optional_payload_type_context_native_2026_10_16 — retain declared Value optional payload context across nested Some construction

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/value_optional_payload_type_context_native_2026_10_16.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/00.common/runtime_value_v1.spl:76; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/00.common/runtime_value_v1.spl:287; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/value_owner_constructor_native.spl:146
```
- Review rationale: Read complete candidate-only report and actual runtime_value_v1 owner. some/none/ok/err bind Value? locals then call top-level typed factories, all explicitly marked @workaround. The native probe checks real Option/Result presence, nil placement and contained Int59, but remains unrun. This is a source workaround preserving expected context, not evidence the compiler's nested-Some type-context defect has a known root remedy. Keep valid historical report open with unknown solution; exact MIR validation and native controls remain required within existing cycle budget.
- Review corrections: Reject first-pass known/no/fixed_pending_verification: report and owner explicitly label annotation workaround candidate; root solution and structural requirement remain unknown.

## verification_cache_invalidate_dependents_wildcard_symbol_2026-07-20 — Bug: `VerificationCache.invalidate_dependents` treats the file-level `"*"` symbol sentinel as a trackable dependency key, causing false-positive invalidation of unrelated proof units

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/verification_cache_invalidate_dependents_wildcard_symbol_2026-07-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/lib/std/src/verification/cache.spl:168; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/00_formal_verification/compiler/cache_correctness_spec.spl:129; history 48ec132b097
```
- Review rationale: Read full report and exact std successor. invalidate_dependents excludes '*' from both source-symbol matching and propagation while retaining source-file, Lean-module and dependency propagation. Regression creates two wildcard file units, verifies unrelated a survives and dependent b disappears. Target-bound 48ec132b097 diff adds precisely both guards, causally addressing report's fixed-point cascade without contract restructuring. Present source remedy is known; historical result does not qualify current runtime.
- Review corrections: Confirm migrated owner and known/no/fixed_pending_verification; no new spec run.

## vfs_l5_fat32core_open_faults_on_new_file_write_2026-08-31 — L5 blocker: `Fat32Core.open` faults on the first write of a NEW file (2026-08-31)

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/vfs_l5_fat32core_open_faults_on_new_file_write_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/common/boot/freestanding_value_registry_impl.h:149; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/fs_driver/fat32_dir_ops.spl:465; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/fs_driver/fat32_owned_io.spl:157
```
- Review rationale: Read full report through rejected receiver hypotheses, actual freestanding enum-unwrapping cause and subsequent L6 size persistence repair. Independently inspected target freestanding rt_unwrap_or_trap: it reads HEAP_ENUM header and returns Some/Ok payload without registry-membership gating. Current FAT32 write syncs grown size and directory helper patches bytes28..31 then invalidates dentries, while explicitly leaving lazy cluster-zero entries separate. This is a concrete present remedy for original L5 and follow-on create-file path. Retained OVMF nonce transcript is historical, not current artifact qualification.
- Review corrections: Structural yes -> no: header identity correction and directory-size helper preserve existing contracts; report explicitly avoids changing OpenFile/resolve_path. Original L5 is not lazy-allocation residual.

## vhdl_backend_block_temps_emit_process_variables_not_signals_2026-08-04 — VHDL backend emits block-level MIR temps as process variables (:=) not signals (<=)

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/02_integration/compiler/vhdl_backend_e2e_spec.spl; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/plugins/backend_vhdl/vhdl_entity_compile.spl:559; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/plugins/backend_vhdl/vhdl/vhdl_builder.spl:187; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/02_integration/compiler/vhdl_backend_e2e_spec.spl:294
```
- Review rationale: Read complete report including later renamed Ret repairs and their unrelated failures. Target needs_control_process selects Var/Temp assignments for sequential semantics; builder declares process variables and emits := separately from signal <=. Current E2E local-copy test still expects architecture signal x and concurrent tmp/x assignments. This is a genuine unresolved owner-contract disagreement, not evidence either operator alone is wrong. Keep uncertain/open and unknown remedy until declaration, lifetime and intended hardware semantics are reconciled; no generated VHDL or GHDL result asserted.
- Review corrections: Retain uncertainty; stale Ret repairs and historical failure totals do not resolve temp lifetime contract.

## vhdl_design_catalog_dict_to_i64_cast_2026-07-30 — A second pre-existing defect under the dict->i64 cast remains open after the cast fix

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/backend/vhdl_design_catalog_spec.spl; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/plugins/backend_vhdl/vhdl/vhdl_design_catalog.spl:168; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/plugins/backend_vhdl/vhdl/vhdl_design_catalog.spl:302; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/plugins/backend_vhdl/vhdl/vhdl_design_catalog.spl:867; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/backend/vhdl_design_catalog_spec.spl:54
```
- Review rationale: Read full cast repair and separate follow-on metadata failure, including second LLVM helper instance. Target catalog_symbol uses contains_key plus indexed read, confirming local cast remedy. Target catalog_function still resets metadata false/default at302 and sidecar path restores it at867; current test helper sets direct MIR metadata. Thus known cast correction does not supply a known remedy for the record's still-open metadata authority question. Keep historical validity and whole record open, with solution/structural requirement unknown pending sidecar-versus-direct owner decision.
- Review corrections: Known/yes -> unknown/unknown for the whole open record; cast itself is locally repaired. Correct stale212/740 anchors to current302/867.

## virtio_gpu_capset_qemu_smoke_needs_guest_probe_image_2026-08-08 — virtio-gpu capset QEMU smoke has no guest probe image, so the device path is never exer...

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:NONE; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-virtio-gpu-capset-qemu.shs:31; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/drivers/virtio/virtio_gpu_capset.spl:191; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/drivers/virtio/virtio_gpu_capset.spl:213
```
- Review rationale: Read full guest-image report. Current checker requires OVMF image, exact serial marker and nonzero capsets; missing image exits2. Device owner gpu_query_capset_info requires initialized negotiated control queue and actual response decoding. Scoped exact-target search across OS, embedded examples and build/OS scripts found only gpu_query_capsets definition, no probe marker producer/caller. This supports outstanding firmware-guest integration, not an invalid bug or pure-test qualification. Actual image identity and boot/query receipt remain missing; no necessary architectural restructuring is yet established.
- Review corrections: Structural yes -> unknown: missing integration artifact alone does not demonstrate a required contract/data-model change. Source query scope stated; no filesystem image absence invented.

## virtio_map_bar_capability_authority_2026-08-02 — Bug: VirtIO MapBar capability authority mismatch

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/virtio_map_bar_capability_authority_2026-08-02.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/ipc/syscall.spl:583; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/ipc/syscall.spl:795; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/ipc/syscall_device.spl:274; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/ipc/syscall_device_bar.spl:17; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/device/device_bar_syscall_policy.spl:29; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/drivers/virtio/virtio_gpu.spl:316
```
- Review rationale: The original raw-physical mapping and fixed DeviceBarMap(0,0,0,0) gate still exist in syscall 83. Independently traced the proposed replacement: the GPU now calls 88 with BDF/BAR/offset/length and 89 for rollback; the decoder checks tuple/window shape, and the transaction helper resolves the PCI window into the caller's VM and lifecycle ledger. But the actual syscall dispatcher has no 88/89 cases or handler reference and falls through to -1. Thus the report's latest claim of implemented live exact capability checks is not supported, while its unmigrated-caller claim is stale. The concrete remedy is to connect the tuple-scoped capability check, explicit VM transaction and owner lifecycle through the live ABI and retire the raw-physical authority bypass. This is an authority/ABI ownership change, not just adding a range check. Keep open until requested versus granted BAR, rollback and revoke semantics have kernel integration evidence; no execution was attempted.
- Review corrections: Confirmed migrated GPU callers, but provisional helpers are unreachable through the inspected live dispatcher. Do not promote pure resolver tests or report implementation claims to end-to-end authority proof.

## vulkan_8k_jit_retained_host_buf_sample_crash_2026-08-12 — Strict-JIT 8K retained host-buffer sample crashes on a retained u32 array read

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/fixtures/jit_class_u32_array_retained_read/main.spl; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/skia/backend/vulkan/backend.spl:481; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:2432; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_drawing_spec.spl:253; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/fixtures/jit_class_u32_array_retained_read/main.spl:10; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/fixtures/jit_vulkan_host_mirror_64_row_sample/main.spl:28; history 4051bc8c494c0ec96df33d3c2d48655311e8e23e bounded by c0b3ad911f4cb00c0f3550b05baa8d06347d17d0
```
- Review rationale: Read the report including its explicit retraction of GPU-hardware deferrals. Independently found the physical owner repair in Skia: class SkiaVulkanBackend, compatibility alias VulkanBackend, constructors and impl using the concrete owner. The c0-bound history diff 4051bc8c494 confirms this is the actual rename rather than a title-only fix claim. Engine2D also has bounded owner-local sample_host_mirror; its focused regression asserts the changed pixel after 210 mutations and rejects an invalid index. The generic full-8K array fixture and 64-row fixture are distinct reductions, not the full Vulkan workload. The concrete collision repair is present, but the report's aborted full workload and absent current receipt prevent closure or runtime success claims. The physical rename preserves the public alias and localizes field access; mandatory architectural restructuring is not established.
- Review corrections: Reject low-review structural=yes. A present owner rename and local sampler justify fixed_pending_verification, not an 8K parity PASS. Hardware absence was retracted; remaining full-workload evidence is pending.

## vulkan_engine2d_sequential_frames_flaky_moltenvk_2026-09-02 — Vulkan Engine2D: sequential multi-frame runs flaky under interpreted MoltenVK

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/vulkan_engine2d_sequential_frames_flaky_moltenvk_2026-09-02.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/ui_showcase/hosts/host_2d_gpu.spl:139; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:1228; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl:1597; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl:1630; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl:1712
```
- Review rationale: The report distinguishes the clear-triggered completion_unknown cascade, stale pixels from skipping clear, and intermittent JIT SIGBUS. Current host still clears only Metal. Source tracing reaches clear -> _dispatch_framebuffer_checked -> enqueue/flush/retry/resync logic: current helper rejects degenerate dispatches, proves idle before resync, avoids replay with lost siblings, and downgrades recovered -1 to 0. Therefore a claim that there has been no recovery work would also be stale, but these guarded branches do not establish the cause or repair of the original MoltenVK failure. clear still latches unknown completion on an unrecovered negative result, and subsequent draw methods return early. No complete sequential/screen-switch/stale-pixel or SIGBUS receipt was run. Keep the documented defect open with unknown solution and unknown structural need rather than treating a no-clear workaround or suspected fence lifetime as diagnosis.
- Review corrections: Reject low structural=yes: cross-frame scope and a suspected fence path do not prove required restructuring. Include existing guarded resync/retry logic; it is source evidence, not current MoltenVK verification.

## vulkan_feature_off_makes_gpu_benchmarks_silently_noop_2026-09-13 — `rt_vulkan_is_available()` returns true while the whole compute path is a stub

- Source receipt: `adjudication_v2_29`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fix_candidate`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/vulkan_feature_off_makes_gpu_benchmarks_silently_noop_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/Cargo.toml:33; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:3825; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2645; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:4374; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5339; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:5403; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/gpu.rs:760; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/vulkan_graphics_runtime_buffer.rs:233
```
- Review rationale: The default-empty feature manifest, loader-only interpreter probe and feature-off native zero stubs are present, but independently tracing the actual interpreter registration disproves the report's blanket claim that its allocator and dispatch all delegate to those stubs. The interpreter has its own dlopen buffer allocator, compute pipeline, dispatch and submit/wait implementation. A decisive mismatch nevertheless remains: registered rt_vulkan_copy_to_buffer_array calls the runtime adapter, which calls rt_vulkan_copy_to_buffer_raw; the feature-off raw implementation returns 0 while the probe can return true. Thus compiled capability is falsely advertised for the mixed upload/compute surface even though some compute functions work dynamically. A local feature/capability guard at the probe or a distinct truthful compute capability check is a concrete fix candidate for this defect; enabling the build feature alone is a workaround. No architectural change is required to make the advertised capability false when this required upload path is unavailable. Feature-on state compatibility and benchmark error behavior still need their own validation; nothing was run.
- Review corrections: Correct blanket 'whole compute path is stubbed': allocator/dispatch/submit have registered dlopen implementations. The upload adapter still reaches a feature-off zero stub, so validity remains supported. Replace structural=yes with no for the concrete local truthful-probe fix; mark fix_candidate, not implemented/fixed.

## vulkan_ffi_ledger_lost_under_spec_harness_2026-08-09 — VulkanFfi rejection ledger never accumulates under the spec harness but works under `run`

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/vulkan_ffi_ledger_lost_under_spec_harness_2026-08-09.md#L19-L124; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/gpu/engine2d/ffi_vulkan.spl#L51-L77; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/gpu/engine2d/ffi_vulkan_spec.spl#L73-L88
```
- Review rationale: Historical same-binary run/test comparison records a real lost-ledger defect and eliminates plain/trait mutator and consumed-return explanations. At target VulkanDynFfi (renamed from reported VulkanFfi) mutates both fields in _dyn_reject_bool and Dynamic init/shutdown call that helper; its spec asserts 0→1→2 with operation names and explicitly skips absent loaders. These declarations do not explain the harness loss; retain valid/unknown/untested.
- Review corrections: Correct malformed SHA in research report reference and current owner name VulkanDynFfi; no runtime fix inferred. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## vulkan_instance_init_fails_under_run_but_not_test_2026-08-25 — Vulkan instance init fails under `bin/simple run` but succeeds under `bin/simple test` (2026-08-25)

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/vulkan_instance_init_fails_under_run_but_not_test_2026-08-25.md#L1-L42; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu_lane/vulkan_lane_session.spl#L112-L120; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu_lane/vulkan_vm_executor.spl#L217-L232; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/vulkan_graphics_runtime_core.rs:441-486
```
- Review rationale: The report controls identical SPIR-V and shows run/test and probe-order differences on a Rust seed. Current probe maps every rt_vulkan_init failure to one skip string; the runtime owner distinguishes quarantine, enumeration, instance and device-selection errors under STATE.lock. Thus instance-init-failed is not a root diagnosis. Retain historical validity, unknown remedy/structure; current runner environment and deployed-artifact behavior remain unqualified.
- Review corrections: No proposed category changes; a fresh result is not part of this wave. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## vulkan_vm_lane_returns_exit0_after_cuda_lane_same_process_2026-08-25 — VulkanVmExecutor returns ok=true / exit=0 / 0 records when run after a CUDA lane in the same process (2026-08-25)

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/vulkan_vm_lane_returns_exit0_after_cuda_lane_same_process_2026-08-25.md#L1-L42; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu_lane/vulkan_lane_session.spl#L76-L110; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu_lane/vulkan_vm_executor.spl:96-119,258-297; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu_lane/cuda_lane_session.spl:322-338; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu_lane/vulkan_lane_session.spl:310-337
```
- Review rationale: The historical CUDA-then-Vulkan strict case returns silent success with no effects. Current Vulkan build_svmg_arena zeroes each fresh arena and initializes LOG capacity; teardown frees lane resources with pending-completion guards in both sessions. Vulkan run_source still emits ok=true after a full readback without validating a terminal sentinel, and non-timeout dispatch errors can also produce ok=true. This supports a live honesty gap, but does not identify the original cross-backend interference cause or prove a shared mailbox cursor; root solution remains unknown.
- Review corrections: Extend partial research to actual fresh-arena, result interpretation and both teardown paths; shared mailbox cause is only a suspect. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## vulkan_web_fullpage_cpu_fallback_demotion_2026-08-10 — Vulkan engine2d web lane reports source=cpu_fallback at 800x2600 but device_readback at

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/vulkan_web_fullpage_cpu_fallback_demotion_2026-08-10.md#L1-L94; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl#L1597-L1616; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl#L1063-L1068
```
- Review rationale: The full report rules out framebuffer size and records recovery from dispatch retry followed by begin_compute failure and empty fallback readback. Current checked dispatch rejects invalid arguments and uses batching; mark_cpu_fallback only records first reason and flag, not framebuffer population. This is consistent with an unresolved fallback gap, not proof of a leak or hard size cap. Hardware/resource cause and complete fallback recovery remain unknown; keep open untested.
- Review corrections: No correction to validity/action; do not label the prior bounded retry as complete resolution. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## w_mc_res_001_overfires_verb_only_heuristic_2026-08-07 — W-MC-RES-001 verb-only heuristic over-fires ~208 findings, cannot separate acquires from

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/w_mc_res_001_overfires_verb_only_heuristic_2026-08-07.md#L1-L227; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/35.semantics/lint/unwrapped_foreign_resource.spl#L153-L177; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/resource_registry.spl#L29-L92; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/90.tools/lint/rules/unwrapped_foreign_resource_rule.spl:1-6
```
- Review rationale: Historical critical-profile probes establish a live false-positive problem and a partial 208→160 return-type repair. Current predicate excludes only bool/array same-file declarations; its rule wrapper passes unit.content and unit.path, not parser resource metadata. The resource registry separately stores declarations/metadata. Residual integer values versus handles require semantic facts unavailable in that text interface; structural integration is justified, but no complete safe root remedy/current count is established.
- Review corrections: No correction to validity; keep the residual class open. The report’s historical counts are not a current lint run. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## web_backend_env_get_alias_unresolved_interpret_2026-07-07 — Interpreter: `env_get as web_backend_env_get` re-export alias unresolved — chromium WebRenderBackend facade crashes E1002

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_backend_env_get_alias_unresolved_interpret_2026-07-07.md#L1-L87; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/web_render_backend.spl#L18-L55; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/io/mod_stub.spl#L1-L8
```
- Review rationale: The report identifies E1002 through an aliased multi-hop env_get and explicitly offers de-aliasing as a bypass. Current facade imports env_get directly and calls it at the former failing helpers, but no interpreter alias-resolution remedy was established. Preserve historical validity and unknown root solution; a bypass alone does not support fixed_pending_verification for the tracked alias defect.
- Review corrections: Reject research fixed_pending_verification: current facade de-aliasing is a workaround, not an independently established general resolver fix. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## web_block_vertical_advance_12pct_2026-09-12 — Block vertical advance over-measured ~12 % — cause still NOT isolated (2026-09-12)

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_block_vertical_advance_12pct_2026-09-12.md#L1-L72; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/css.spl#L33-L43; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/dom.spl#L645-L654
```
- Review rationale: The full report excludes fixed-height block advance, paragraph normal height, explicit line height and adjacent-margin collapse using separate controls; catalog composition remains unidentified. Current DOM parser implements normal/multiplier/length branches and CSS facade returns style unchanged, which cannot identify heading/list defaults or the catalog's accumulated drift. Accept valid historical defect with unknown root and structure; no percentage adjustment or runtime resolution is justified.
- Review corrections: No category correction; the proposed percentage is only a symptom and cannot justify a metric adjustment. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## web_cpu_vulkan_twin_pixel_divergence_unbudgeted_2026-09-13 — CPU and Vulkan web-renderer twins diverge by ~29% of pixels, and no budget is pinned

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_cpu_vulkan_twin_pixel_divergence_unbudgeted_2026-09-13.md#L1-L97; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl#L3052-L3070; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/02_integration/ui/web_showcase/catalog_vulkan_twin_spec.spl#L20-L28; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/gpu/engine2d_shadow_rect_twin_formula_spec.spl#L1-L90; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:2960-3050; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_emu_adv.spl:277-335; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/shaders/shadow_rect.comp; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/02_integration/ui/web_showcase/catalog_vulkan_twin_spec.spl:130-131
```
- Review rationale: Historical measurements establish real GPU divergence and later zero differences after replacing flat-shadow treatment. Target device path builds exactly the shared three-box-blur profiles and uploads them to shadow_rect.comp; its kernel multiplies x/y coverage, applies shadow alpha and blends channels, matching the host formula. Catalog spec asserts mismatch_pct_x100<=50 and max_delta<=8. This supports a bounded present remedy and fixed_pending_verification, not current parity execution.
- Review corrections: Strengthen research beyond fallback function names: independently inspect active device profile/kernel and executable budget assertions; current GPU parity remains untested. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## web_css_package_authority_adapter_2026-07-27 — generate_package_authoritative_css emitted literal n and dropped traffic-light ::before

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_css_package_authority_adapter_2026-07-27.md#L1-L53; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/ui.web/html_css.spl#L1903-L1925; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/ui.web/html_css.spl#L1951-L1954; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bug_db.sdn#L1383; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/ui.web/html_css.spl:1916-1925,1951-1954
```
- Review rationale: Full report separates two source defects from outstanding live rendering evidence. Current generate_package_authoritative_css appends newline escapes (not literal backslash sequences), and traffic-light pseudo-elements define content, absolute positioning, inset and display while visual values remain package variables. These directly address the reported local generation errors. Accept known/no/fixed_pending_verification, with no parser, pixel or event qualification.
- Review corrections: No category correction. Source owner is `src/app/ui.web/html_css.spl`, not the queue’s recorded renderer facade; runtime proof remains outstanding. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## web_draw_ir_8k_frame_switch_native_build_timeout_2026-08-11 — Web/DrawIR 8K frame-switch evidence cannot reach native execution — 2026-08-11

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_draw_ir_8k_frame_switch_native_build_timeout_2026-08-11.md#L1-L73; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/05_perf/graphics_2d/bench_web_draw_ir_8k_frame_switch.spl#L1-L95; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/compositor/compositor_engine2d.spl#L648-L696; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/hosted/hosted_browser_frame_switch.spl#L1-L30
```
- Review rationale: Report documents native/JIT pre-execution failures and claims a scalar receipt extraction, but target compositor revision cache returns the full cached Engine2dDrawIrAdvResult and the hosted wrapper references receipt API names absent from the inspected compositor owner. Benchmark sets FRAMES=5 and calls that unresolved receipt method, so it cannot substantiate the reported 200-call receipt contract. Accept valid unresolved evidence blocker with unknown root remedy; do not admit an 8K latency result. Report states its three-cycle cap exhausted; no new execution attempted.
- Review corrections: Reject present receipt-path completion; exact target benchmark/owner conflicts with report partial-fix narrative. Scope absence statement to inspected owner rather than global tree. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## web_render_backend_api_spec_perf_2026-06-05 — Web render backend API spec exceeds the test runner's per-spec perf threshold

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bug_db.sdn#L1389; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/ui/web_render_backend_api_spec.spl#L30-L359; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/ui/web_render_pixel_backend.spl#L123-L160; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_render_backend_api_spec_perf_2026-06-05.md
```
- Review rationale: Original report is a performance warning with 11 passing cases and 71354ms, not a functional failure. Current spec still spans adapter rendering and transport/provenance/cache behavior; current pixel owner creates/renders/shuts down Engine2D and checks completeness, while cached requests can bypass or reuse separately. These are plausible costs but not profiling evidence. Retain valid historical performance issue, unknown remedy/structure and current untested.
- Review corrections: No category correction; historical elapsed time cannot establish present reproducibility or justify a split/optimization without a current profile. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## web_showcase_4k_frame_time_unbudgeted_2026-09-13 — The 4K web showcase lane pins no frame-time budget, and measured cost is not monotonic in pixel count

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_showcase_4k_frame_time_unbudgeted_2026-09-13.md#L1-L56; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/02_integration/ui/web_showcase/overview_4k_render_spec.spl#L59-L102
```
- Review rationale: Report records one 4K measurement and smaller non-monotonic timings, explicitly lacking an approved frame-time contract. Current 4K test captures elapsed_ms but asserts only pixel count, nonblank output, no CPU fallback and one readback. This confirms the missing timing gate without establishing a portable limit or present speed; retain valid/unknown/keep_open pending owner-defined host budget and qualified measurement.
- Review corrections: No category correction; avoid inventing a universal timing limit from one host or treating past duration as current reproduction. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## web_showcase_vector_font_evidence_style_budget_truncation_2026-08-01 — CSS style pass truncates on wall-clock budget so the vector-font marker node keeps

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_showcase_vector_font_evidence_style_budget_truncation_2026-08-01.md#L1-L219; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl#L437-L443; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl#L65-L88; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl#L2141-L2179; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bug_db.sdn#L1400
```
- Review rationale: Full report corrects its initial face-reparse attribution: face-cache and metrics-cache receipts differ, and distinct strings still incur expensive measurement. Current style loop still breaks on deadline leaving defaults, while result types capture degradation and reject incomplete evidence. This is partial fail-closed protection, not completion of late marker styling or a performance fix. Accept valid/unknown/keep_open; report heading closure and font-identity anecdotes do not supersede the remaining mechanism.
- Review corrections: No category correction; treat the current fail-closed signal as a partial evidence-gate repair, not full style completion or performance resolution. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## web_software_oracle_blanks_text_on_budget_exhaustion_2026-08-04 — Software web-render oracle silently blanks all text when its wall-clock budget is

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fix_candidate`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_software_oracle_blanks_text_on_budget_exhaustion_2026-08-04.md#L1-L75; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl#L2138-L2179; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl#L2191-L2205; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl#L2322-L2323
```
- Review rationale: Report isolates intermittent blank software pixels to exhausted paint budget, not CPU configuration. Current result preserves render_degraded/reason and a presentability helper can reject it, but public _software_pixels still returns result.pixels unconditionally. The local remedy is to apply the existing presentability decision before releasing pixel-only output and make incomplete output fail explicitly; this does not require changing the result data model. Accept known/no/fix_candidate for this bounded honesty gap; current timing and caller compatibility must be qualified.
- Review corrections: Keep fix_candidate narrowly for enforcing the existing degraded-result gate in pixel-only publication; do not imply callers have been migrated or budget performance repaired. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## web_style_producer_4s_per_node_interpreted_lane_2026-07-29 — Web style producer costs ~4s per DOM node on the interpreted lane, blocking the showcase

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_style_producer_4s_per_node_interpreted_lane_2026-07-29.md#L1-L1342; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl#L7-L15; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl#L437-L443; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl#L841-L852
```
- Review rationale: Report's early 4s/node figure is superseded by declaration batching/dispatch, glyph caching, changed node counts and later compile-bound attempts; later phase instrumentation did not settle current style-versus-paint cost. Current owner has cascade memo, presentational-attribute fast rejection, and uncached inline apply with a documented zero-hit memo experiment; deadline truncation remains. These establish historical validity and partial work but not current dominant cost, root remedy or necessary architecture. Keep open unknown; broad bracket-slice survey is a separate unresolved follow-up.
- Review corrections: Correct any inference that the early ~4s/node value is current or that the whole issue is resolved by the declaration merge/cache. No timing category can be promoted from source inspection alone. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## web_tls_helper_imports_and_sha256_alias_2026_10_10 — Web TLS consumers lack canonical helper imports and SHA256 alias

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_tls_helper_imports_and_sha256_alias_2026_10_10.md#L1-L22; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/tls/canonical_sha256_alias_spec.spl#L1-L20; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/fixtures/lib/tls_canonical_sha256_alias/main.spl#L1-L18; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/tls/utilities.spl#L24-L25; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/tls/record.spl#L1-L62; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/tls/cipher.spl#L1-L312; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/tls/_TlsUtilities/hex_encoding.spl#L383-L402
```
- Review rationale: Report proposes canonical TLS helper imports plus preserving tls_sha256 while exporting sha256. Target utilities implements the alias, but record.spl imports only len/byte_at/slice while calling i64_to_hex_byte/u16_be_hex/hex_len/hex_slice, all exported by the utility owner. Thus alias presence alone does not establish complete repair of the named contract or Web closure. Keep valid/unknown/keep_open pending complete consumer owner review and qualified fixture/closure execution.
- Review corrections: Retain unknown for combined closure issue; canonical alias exists but report source-complete wording exceeds checked consumer imports. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## webfw_signing_wrong_digest_and_csrf_not_session_bound_2026-08-18 — web_framework signing: digest does not match HMAC-SHA256, and CSRF tokens are NOT session-bound

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/webfw_signing_wrong_digest_and_csrf_not_session_bound_2026-08-18.md#L1-L92; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/web_framework/session.spl#L698-L707; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/web_framework/csrf_integration.spl#L34-L53; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/crypto/hmac.spl#L12-L54; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/nogc_sync_mut/web_framework/session_csrf_signing_spec.spl#L55-L112
```
- Review rationale: Report explicitly says the byte-HMAC plus uniquely named hex helper was already among three bodies producing identical wrong outputs; source presence is therefore not a later repair. Target compute_signature and csrf_token_for_session still use that form, and the latter includes csrf:{session_id}; byte-HMAC owner consumes all data bytes. External digest/session distinction assertions remain meaningful. Keep valid/unknown: runtime reachability/dispatch, not digest expectation adjustment, is the unresolved question.
- Review corrections: Correct implication that current byte-HMAC shape newly bypasses the defect: the report already tested this exact shape unsuccessfully. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## wildcard_import_c_backend_stubs_function_to_int_2026-07-30 — use compiler.backend.backend.c_backend_stubs.* poisons the session with cannot convert

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wildcard_import_c_backend_stubs_function_to_int_2026-07-30.md#L1-L306; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/value_impl.rs#L126-L155; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_single.spl#L1435-L1479; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/feature/usage/wasm_compile_spec.spl
```
- Review rationale: Full report narrows wildcard-triggered post-example Function→int failure across six backend modules without identifying a caller; separate placeholder-template source fix was explicitly unrelated and unqualified on deployed binary. Target Value::as_int retains the matching fallback and optional backtrace, and runner counts nonzero asserted child exits as failure. Those semantics support keeping the historical defect open, not weakening runner rejection or treating per-spec bare imports as a root fix.
- Review corrections: No correction; per-spec bare imports remain mitigation only. Do not describe the exact collision or root registry fix as known. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## window_record_encode_declared_nowhere_2026-08-04 — `window_record_encode` is imported by the SPM client but defined nowhere; its spec only length-compares two self-generated encodings

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `fix_candidate`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/window_record_encode_declared_nowhere_2026-08-04.md#L1-L86; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/win_fs/window_record.spl#L71-L86; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/simple_process_manager/wm_spm_client.spl#L152-L160; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/simple_process_manager/spm_service.spl#L53-L107; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/common/win_fs/window_record_encode_spec.spl#L14-L39; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/02_integration/app/simple_process_manager/spm_service_spec.spl#L81-L99
```
- Review rationale: Original absent encoder is now present and client delegates to it, but report also requires actual SpmService wire compatibility. Target encoder emits gen and no acl, whereas decoder recognizes generation and acl and registration checks ACL coverage; generation therefore defaults and ACL identity is lost. Semicolons in app/title can create extra fields. Existing encoder is not evidence of a correct contract. Accept valid fix_candidate with unknown complete schema/remedy; do not call the historical missing function invalid.
- Review corrections: Scope delimiter concern precisely: semicolons split fields; equals inside a value is preserved by first-equals parsing. Missing gen/generation agreement and ACL remain concrete. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## windows_bootstrap_max_path_262_2026-08-30 — Windows bootstrap silently exceeds MAX_PATH; `cl.exe` fails with exit 1 and no diagnostic

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_bootstrap_max_path_262_2026-08-30.md#L1-L96; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-authority-wiring.shs#L292-L350; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/scripts/bootstrap_windows_cargo_path_budget_test.shs#L17-L45; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/scripts/bootstrap_windows_cargo_path_budget_test.shs#L129-L165
```
- Review rationale: Report's long -Fo path failure has a present causal remedy: selector validates full fingerprint/config key, uses shallow Windows build/c/<12hex-config-key>, converts to native spelling and rejects prefixes above 120 bytes. Regression encodes original object shapes and boundary cases. This changes cache placement/identity policy rather than just shortening one invocation; known structural remedy is supported, current Windows execution untested. Historical full-fingerprint path and Unix legacy-target narrative no longer exactly describe target.
- Review corrections: Correct report/research stale details: current Windows path is config-keyed, content fingerprint is validated but not path-keyed; Unix default now uses sibling rust-cargo-target-<key>, not unchanged authority-root/target. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## windows_mcp_native_build_blocked_at_hir_entry_2026-09-01 — Windows: MCP native build reaches HIR entry, then aborts — MIR error count still unobtainable

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_mcp_native_build_blocked_at_hir_entry_2026-09-01.md#L1-L60; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/types.spl; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_tldr_registration.spl; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/types.spl:678-685; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_tldr_registration.spl:79-120
```
- Review rationale: Full report records HIR-entry bool.symbols failure after 100 surface units and separately a Windows worker spawn/wait failure. Target HirLowering constructor assigns SymbolTable.new(), and TLDR registration uses self.symbols for lookup/definition; neither supplies evidence of the historical bool receiver's producer. This meaningful owner check supports historical validity but no causal fix. Keep open unknown; entry count zero cannot replace the unobserved MIR census or clear downstream enum-len behavior.
- Review corrections: The historical report itself warns against treating a zero entry-point count as the MIR count or as clearance. Current source reading does not prove whether this exact error reproduces at the assessed SHA. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## windows_msvc_stage2_receiver_gate_runtime_c_uncompilable_2026-09-02 — Windows MSVC: Stage 2 admission blocked — cl.exe cannot compile runtime.c

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_msvc_stage2_receiver_gate_runtime_c_uncompilable_2026-09-02.md#L1-L90; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/tools.rs#L352-L360; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/tools.rs#L680-L700; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/tools.rs#L850-L875; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/tools.rs#L2235-L2260; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime.h:316; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/platform/platform_win.h:488; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/platform/unix_common.h:319
```
- Review rationale: Later report sections explicitly wire both MSVC C11 flags and retain no end-to-end admission claim. Target runtime.h, Windows and Unix rt_mmap signatures now all accept tagged path_value; tools.rs selects both flags by compiler binary and applies them in runtime compile commands. These causally address reported ABI/flag omissions, supporting known fixed_pending_verification. Full stage admission still needs a current Windows receipt; no structural redesign is demonstrated by compatibility corrections within existing ABI/tool invocation contracts.
- Review corrections: Correct yes→no: inspected fixes restore existing ABI/compiler contracts with bounded compatibility changes; report explicitly contains later wired-flags correction. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## windows_msvc_stage2_rejected_struct_receiver_route_threads_2026-09-01 — Windows MSVC Stage 2 builds and links, then is REJECTED by the struct-receiver probe

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_msvc_stage2_rejected_struct_receiver_route_threads_2026-09-01.md#L1-L110; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh#L2700-L2735; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/group_native_thread_capability.spl#L459-L480; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:7422-7437; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/llvm/functions.rs:2715-2755; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/llvm/emitter.rs:1387-1415; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:4895-4928; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/llvm/instructions.rs:315-355
```
- Review rationale: Later report refutes initial argv/bool hypotheses with object-code evidence: erased to_i64 bypassed parse and string digit order compared tagged addresses. Target Rust LLVM functions/emitter and pure-Simple unresolved lowering call rt_to_int_dynamic; runtime parses heap strings and otherwise preserves the value. LLVM ordering dispatches tagged operands through rt_native_cmp. Those are concrete cross-codegen/runtime remedies; accept known structural fixed_pending_verification, with historical route-matrix success distinct from whole Stage2 admission.
- Review corrections: Replace partial route-only evidence with independently checked actual numeric-conversion and ordering remedy owners; do not retain refuted argv hypothesis. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## windows_native_build_main_resolves_to_image_base_2026-09-01 — Windows native-build: every produced binary calls `main` at the image base (0xC0000005)

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_native_build_main_resolves_to_image_base_2026-09-01.md#L1-L100; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/llvm_native_link_hosted_support.spl#L125-L224; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/llvm_native_link_orchestrator.spl#L320-L345; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/llvm_native_link_orchestrator.spl:570-601
```
- Review rationale: Report's PE debugger evidence establishes main executing RVA zero and later notes shim code absent from the historical image. Target compiles a main shim and explicitly appends entry_obj_path in both stage4 and ordinary all_objects construction. This is stronger than research's generation-only check, but source list inclusion does not prove the deployed compiler preserves it or final linker resolves main correctly. Accept valid/unknown/keep_open pending exact Windows object/link-map and execution evidence.
- Review corrections: Correct research gap: entry object is explicitly appended to current link object list; current artifact/linker resolution still untested. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## windows_path_duality_native_vs_shell_tmp_2026-09-18 — Windows path duality: native file APIs, raw rt_ externs, and the POSIX shell see three different files for /tmp paths

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_path_duality_native_vs_shell_tmp_2026-09-18.md#L1-L55; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/io/file_ops.spl; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime.c; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/file_ops.spl:224-226,294; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/fs/host_path.spl:73-106
```
- Review rationale: Full report corrects three namespaces to native versus MSYS/%TEMP%, and says partial mapping was reverted. Current GC file_ops is only a facade; actual no-GC owner routes publication and hashes through host_path_native. That converter handles /d drive syntax and separators but does not map /tmp to %TEMP%. Thus repaired publish bypass does not establish a uniform native/shell tmp convention or total caller coverage. Accept historical validity with unknown complete remedy/structure and keep open.
- Review corrections: Trace facade to real no-GC owner; preserve report's two-namespace correction, and avoid claiming exhaustive raw-call audit. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## windows_phase3_blocked_planner_admission_producer_requires_in_repo_build_root_2026-09-02 — Windows Phase 3 blocked: planner-admission-v2 producer refuses any bootstrap output outside `<repo>/build/`

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_phase3_blocked_planner_admission_producer_requires_in_repo_build_root_2026-09-02.md#L1-L60; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs#L116-L150; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh#L411-L448; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs:174-188; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/lib/bootstrap-stage3/authority.shs:912-970; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/resume-stage3-from-admitted.sh:120-129,879
```
- Review rationale: Both original hardcodings are addressed: producer canonicalizes output through physical allowlisted-root validation and binds admission_file residency to that declared output, then hashes receipt/candidate authority. Validator rejects traversal, symlink leaves and noncanonical roots. Resume additionally selects Windows .exe/.lib names and requested thread count. This is a concrete provenance-preserving cross-script remedy, supporting known/yes/fixed_pending_verification; it does not admit the historical candidate or prove current Windows Phase3 execution.
- Review corrections: Extend research beyond first output-root guard to second admission-residency guard and physical allowlist owner; no guard weakening or current admission inferred. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## windows_production_dynamic_backend_provider_incomplete_2026-10-05 — Windows production dynamic backend providers are incomplete

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_production_dynamic_backend_provider_incomplete_2026-10-05.md#L1-L100; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_backend_plugin.c#L130-L168; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend_plugin/transport.spl#L130-L190; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend_plugin/dynamic_loader.spl#L35-L66; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/mir_serialization.spl#L14-L49; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend_plugin/loader.spl:40-70; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_backend_plugin.c:184-220
```
- Review rationale: Current transport now carries bounded backend/target/CPU/features/optimization/MIR digest fields, correcting report item3. Dynamic loader still projects request fields into descriptor/receipt; C bridge checks ABI/size/vtable, not complete semantic metadata. Active serializer includes functions, collection explanations and optional enum declarations but omits other full-module fields cited by the report. These inspected unresolved contracts support valid/unknown/keep_open without a global claim that no production provider exists.
- Review corrections: Correct stale transport-loss assertion: configuration is encoded at target. Correct functions-only wording: explanations and enum declarations also serialize; full-module semantics and foreign metadata admission remain incomplete. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## windows_runtime_object_cache_2026-10-05 — Windows runtime objects are rebuilt for unchanged compilation inputs

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_runtime_object_cache_2026-10-05.md#L1-L50; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/runtime_compiler.spl#L760-L780; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/runtime_compiler.spl#L900-L960; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/runtime_object_cache_windows.spl; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/runtime_object_cache_windows.spl:18-46,74-148
```
- Review rationale: Report is explicitly an authored unqualified cache implementation, not a measured 0.1s improvement. Target runtime caller gates Windows clang-cl caching outside strict admission, hashes compiler/adjacent DLLs, preprocesses a private .i, keys actual bytes plus semantic context/expanded plan/environment, compiles that same file and rechecks bytes/plan; publication rechecks toolchain. This supports a concrete structural cache remedy pending native equivalence/invalidation/concurrency and time/RSS qualification; no current speed or full publication-safety proof is asserted.
- Review corrections: Strengthen wiring-only proposal by checking actual preprocessed-input identity/compile/publication flow; retain report's explicit native verification limits. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## windows_scv_inventory_cold_init_untracked_walk_slow_2026-09-13 — Windows SCV cold initialization retains digest events and canonicalizes facets once, but repeated untracked walking still lacks RSS/wall proof

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_scv_inventory_cold_init_untracked_walk_slow_2026-09-13.md#L1-L100; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/compiler_entrypoint/inventory_events.spl#L162-L180; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/compiler_entrypoint/inventory_events.spl#L374-L410; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/compiler_entrypoint/inventory_events.spl:182-228
```
- Review rationale: Full report keeps untracked-walk cost open after streaming/facet dedup and corrects the native-hashing claim. Target cold init still invokes git --cached --others under 300s, while event construction filters non-compilable paths then retains digests/events instead of every file's text. This addresses memory shape and some work, but not costly discovery itself. Accept valid/unknown/keep_open; no current Windows RSS/wall evidence or selected complete discovery remedy exists.
- Review corrections: Downgrade known/yes/fixed_pending_verification for the combined issue: source streaming is partial, deadline increase is mitigation, and untracked-walk root remedy remains unselected. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## windows_stripped_seed_binary_blinds_symbol_guards_2026-09-02 — Windows: the stripped `bin/simple.exe` blinds every symbol-table guard

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_stripped_seed_binary_blinds_symbol_guards_2026-09-02.md#L1-L90; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/extern-backing-census.shs; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-no-unresolved-runtime-symbols.shs#L190-L230
```
- Review rationale: Report distinguishes false-red suppression from restored symbol coverage. Target census still uses nm defined symbols, errors below floor100 and enumerates Linux shared-library paths; sibling guard errors on no readable symbol table. These guards correctly refuse vacuity but do not provide PE/Windows CRT evidence. Accept historical validity with unknown complete remedy/structure: unstripped artifact/export parsing and platform source are alternatives needing a concrete supported contract and Windows receipt.
- Review corrections: Reject known/yes based only on proposed alternatives: non-vacuity floor is present, but complete Windows symbol evidence path has not been established. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## wine_vm_module_family_destroyed_by_tree_wipe_2026-08-04 — wine_vm module family lost to a tree wipe and partly rebuilt by guess, so contents are

- Source receipt: `adjudication_v2_30`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wine_vm_module_family_destroyed_by_tree_wipe_2026-08-04.md#L1-L145; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/wine_vm_adapter.spl; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/wine_seh_frame.spl; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/wine_thread_adapter.spl; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/wine_vm_adapter.spl:102-146; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/wine_seh_frame.spl:32-52; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wine_vm_module_family_destroyed_by_tree_wipe_2026-08-04.md:147-280
```
- Review rationale: Read later repair pass: report advances from 45 failing specs to 26, with two unresolved evidence-token clusters; earlier counts are stale. Target VM commit is restored to three arguments, preserves reservation size and returns region; SEH validates thread/process, stack and handler bounds before a modeled dispatch. Restoration is real partial progress, not whole-family behavioral resolution. Accept valid/unknown/keep_open pending authority for remaining evidence expectations; neither missing-token history nor current modeled code makes live specs invalid.
- Review corrections: Correct research's first-pass-only 45/62 residual to report's later 26 failing specs/26 failures. Reject whole-record fixed_pending_verification based on restoration/presence alone. All source reads independently bound to full c0 target; historical execution is not current reproduction.

## wm_glass_qemu_evidence_contract_p1_2026-07-27 — WM glass QEMU x86/ARM evidence rows lack frozen-source manifest and parity receipts, fail

- Source receipt: `adjudication_v2_31`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wm_glass_qemu_evidence_contract_p1_2026-07-27.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-simpleos-wm-fullscreen-evidence.shs:88-108; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/lib/simpleos-wm-fullscreen/build.shs:45-69; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-simpleos-arm64-qmp-input-evidence.shs:12-39
```
- Review rationale: The full report retains several rejected and unintegrated frozen-admission/BRR2 candidates; no rejected candidate establishes a current live row. The x86 entry delegates to build.shs, where an explicit kernel passes ELF validation then clears KERNEL_ADMISSION and records external-elf-validated, while normal cached kernels undergo admission-field checks. This directly supports the historical external-artifact binding concern. ARM names frozen build manifests and admission helpers, but that is not a source-matched guest receipt set. No reviewed remedy closes the complete source/order/parity/theme/resource contract.
- Review corrections: Reject research structural=yes as unproven necessity: the report proposes cross-owner alternatives, but this pass establishes an admission bypass and unqualified contract, not a mandatory architecture change. Wrapper variable declarations alone were insufficient; the actual build branch was inspected. Queue unknown structure retained.

## wm_guest_css_var_unresolved_blocks_material_admission_2026-08-09 — Guest renders theme sheet with var() UNRESOLVED, failing two material-admission terms not

- Source receipt: `adjudication_v2_31`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wm_guest_css_var_unresolved_blocks_material_admission_2026-08-09.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_css_rules.spl:32-124; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_css_rules.spl:381-405; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_css_rules.spl:831-901; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core_types.spl:52-123; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/text_index_of_on_substring_receiver_reported_bool_2026-08-09.md:105-143
```
- Review rationale: Historical guest evidence has 49 unresolved variables, props=0 and agreeing true starts_with predicates; it refutes the earlier single-layer and starts_with diagnoses. Target preserves unresolved var source text instead of empty splicing. Crucially, props is the end of collect/join/reparse: the extraction owner feeds CssVarResolutionState.new, whose colon search now uses find_from; comments record index_of=0 versus find_from=11 on the same nonempty line. The follow-up report localizes failure to reparse after a 1365-character property pool, although its discriminating probe was still pending there. This is a present workaround and stronger localization, not a proven compiler root repair or guest admission.
- Review corrections: Correct research attribution of props=0 to the root collector: zero final prop_count does not prove zero collected text. The current source contains later stage receipts and a find_from workaround. Keep underlying solution unknown; separate historical mcopy/disk and source-change admission blockers.

## wm_lane_boundary_7_new_violations_2026-08-08 — check-wm-lane-boundary.shs reports 7 NEW portable-lane violations; nothing runs this gate

- Source receipt: `adjudication_v2_31`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wm_lane_boundary_7_new_violations_2026-08-08.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-wm-lane-boundary.shs:40-98; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/check/wm_lane_boundary_check.spl:73-83; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/check/wm_lane_boundary_check.spl:123-153; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/90.tools/lint/_LintMain/wm_lane_boundary_lints.spl:101-169; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/90.tools/lint/_LintMain/wm_lane_boundary_lints.spl:225-268; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/wm_showcase/session.spl:51-72
```
- Review rationale: Report records seven initial findings and later claims eleven; its later listed NEW VIOLATION lines themselves exceed that count, so neither number is a current oracle. The wrapper runs the canonical lint and compares path:line:code against baseline. Target rule explicitly admits app.wm_showcase_host, browser/engine2d intra-lane imports and rt_u32s_from_raw; session imports now use those facades. Exact-target searches of .github and pre-push-conflict-tree-guard.shs find no direct checker invocation. Historical boundary/gate drift is valid, but neither the surviving violation set nor required architecture repair follows from obsolete imports.
- Review corrections: Research structural=yes downgraded to unknown. Existing target exemptions/facades contradict treating all old reported imports as current violations. Preserve missing direct wiring finding with its bounded search scope; do not endorse rebaselining or assert a current count.

## wm_metal_glass_multi_receipt_opacity_2026-07-27 — Metal glass: inactive-opacity offscreen is gpu_only=false so device-glass rejects it

- Source receipt: `adjudication_v2_31`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wm_metal_glass_multi_receipt_opacity_2026-07-27.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:465-470; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:1159-1177; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/draw_ir_target_metal.spl:76-86; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:2653-2666; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/compositor/host_compositor_core.spl:111-174; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/02_integration/rendering/macos_metal_glass_receipts_native.spl:32-101; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/os/compositor/host_compositor_entry_spec.spl:441-568
```
- Review rationale: Verified persistent device_identity assigned from the Metal session and passed through device-glass execution. The real host validator independently derives ordered requested IDs and checks every receipt against result handle/device/source/checksum, counts and fulfillment; it is consumed by host_wm_draw_ir_result_valid. DrawIR returns zero dispatch with ordered unfulfilled receipts for subopaque Metal parent sampling, avoiding a falsely claimed mirror-backed frame. The strict native fixture fails without Metal and checks active pixels plus both opacity-930 controls. These are causal source remedies for identity/receipt/honesty defects across the receipt contract; they do not implement subopaque GPU delta support.
- Review corrections: Accept the proposed known source remedy only after checking the host receipt owner and strict fixture, not backend declarations alone. Source-fixed does not mean inactive Metal now renders: explicit rejection remains required. Historical admission failures are not Metal test execution.

## wm_native_regression_gate_blocked_2026-07-29 — Capped full WM native source closure never retried after ot_layout_shaper Unexpected

- Source receipt: `adjudication_v2_31`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wm_native_regression_gate_blocked_2026-07-29.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/skia/feature/shaper/ot_layout_shaper.spl:222-250; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl:685-714; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/fixtures/compiler/native_trait_optional_struct_return.spl:7-33
```
- Review rationale: Full chronology supersedes the opening never-retried claim: Phase-3 full closure and later nonblack native capture occurred historically, followed by geometry and close-verification failures. Missing-image input invalidated an intermediate pixel-return diagnosis; corrected VBox oracle became y=91/375 and width=478, while scalar cursor experiments were reverted. Later source-current compiler attempts reached runtime-provider/link blockage and then a pre-object runaway. Target shaper conditions are normalized, fld_base_sym is assigned from the lowered expression, and the optional trait fixture still exercises optional receiver/return dispatch. These facts do not identify a single current failing native gate.
- Review corrections: Queue uncertain validity promoted to valid historical multi-stage blocker after full chronology; no claim that the old parser or fld_base_sym symptom remains current. Retain unknown remedy/structure, and do not reapply reverted pixel/cursor workarounds.

## wm_scene_web_lane_layout_scrambled_2026-07-03 — backdrop-filter blur unimplemented so WM glass shows sharp detail instead of frosted

- Source receipt: `adjudication_v2_31`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wm_scene_web_lane_layout_scrambled_2026-07-03.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_primitives.spl:160-175; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_primitives.spl:271-290; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_metal_msl.spl:439-455; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl:101-134; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:1061-1098; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl:134-219; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:647-771; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl:837; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/draw_ir_glass_material.spl:137-193; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/draw_ir_glass_material.spl:270-327
```
- Review rationale: The corrected report attributes apparent scrambling to alpha composition and retains blur/per-window latency residuals. Software row painting uses blend_opacity and Metal filled rectangles call blend_src_over. Research incorrectly treated solid_admitted as the CPU material path: cpu_admitted accepts a parsed backdrop, foundation admits blur with bounded radius 4, paint emits material capability, DrawIR calls the glass renderer, and its CPU path samples framebuffer pixels, performs horizontal/vertical blur and composites them. Thus blanket backdrop-unimplemented is stale for the admitted material route; arbitrary CSS/Chrome parity and the original scene timeout are still unqualified.
- Review corrections: Research known solution downgraded to unknown for the complete still-open row: alpha repair does not solve the remaining scene/latency scope. Correct the false empty-backdrop CPU claim and absence-of-execution claim. Historical validity retained; implemented bounded blur is not proof of general CSS parity or exact-scene fix.

## wm_web_standards_showcase_child_frame_timeout_2026-08-06 — wm_web_standards_showcase_gui host gets a real verdict — and it is FAIL (child-frame-timeout), not a hang

- Source receipt: `adjudication_v2_31`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wm_web_standards_showcase_child_frame_timeout_2026-08-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/06_io/ui/wm_web_standards_showcase_gui.spl:394-437; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/06_io/ui/wm_web_standards_showcase_gui.spl:510-537; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/06_io/ui/web_standards_showcase_gui.spl:41-79; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl:95; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl:1473-1526; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl:128-155
```
- Review rationale: Historical runs distinguish the example watchdog from a real application child-frame-timeout verdict. Current host disables the child example watchdog, waits separately for bridge (300s) and frame (180s), then kills a child with no valid frame. Producer writes the bridge before the expensive HTML render and writes the frame afterward. The explicit resolved_backend field is present in all four current constructors, including the moved cache constructor in simple_web_engine2d_renderer. This addresses the recorded field-inference prerequisite but does not prove the compiler uses a fast path or that rendering finishes inside the deadline.
- Review corrections: Queue uncertain validity promoted to valid historical failure; preserve unknown overall remedy. Correct moved constructor reference and distinguish a produced FAIL verdict from a process hang. Source field declarations do not establish current fallback elimination.

## x64_freestanding_push_byte_reassign_byte_packed — u8.to_i64() mis-dispatches to VfsFileSize.to_i64() — frontend method-name collision

- Source receipt: `adjudication_v2_31`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/x64_freestanding_push_byte_reassign_byte_packed.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/ssh_session_channel.spl:24-41; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/ssh_session_channel.spl:652-665; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/ssh_packet.spl:79-90; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/ssh_cipher.spl:220-230; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/services/vfs/vfs_boot_state.spl:76-80; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/35.semantics/resolve_strategies.spl:30-84; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/35.semantics/resolve_strategies.spl:155-160; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:4825-4865
```
- Review rationale: Report disassembly attributes historical u8-to-i64 conversion to VfsFileSize.to_i64, superseding the packed-array theory. Contrary to research, _build_channel_data_stable still exists in extracted ssh_session_channel, uses payload.push on the byte, and remains called by the live SCP send sequence. Its comment still repeats the superseded packed-array explanation. VfsFileSize.to_i64 and a separate cipher byte conversion remain. Current semantic lookup is receiver-symbol-specific and MIR has numeric conversion fallback, but this inspection does not prove the original full-closure artifact reaches that intended dispatch instead of another lowering path. The push form is a workaround, not the compiler root fix.
- Review corrections: Correct research claim that the old helper is gone; it moved and remains active. Distinguish corrected report opening from contradictory stale tail/source comments. Do not infer a root fix from either helper refactoring or numeric conversion fallback alone.

## x64_freestanding_text_char_at_starts_with — x86_64 freestanding starts_with mis-decodes; residual after char_at and from_byte_array

- Source receipt: `adjudication_v2_31`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/x64_freestanding_text_char_at_starts_with.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:902-924; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:8756-8765; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/ssh_session_channel.spl:429-475; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/apps/sshd/sshd.spl:108-139
```
- Review rationale: Corrected report separates expected char_at heap-tagged text, an older byte-array store repair, and historical deep-frame starts_with false/control-flow corruption; the FAT spawn-reader blocker is separate. Target char_at creates a one-byte RuntimeString and starts_with compares decoded bytes, consistent with the corrected API contract. The extracted deep SSH dispatch tests raw payload slash and defers execution using pending command fields; the shallow owner tokenizes later. This preserves the workaround and avoids the originally failing call. Neither straightforward C logic nor shallow success proves correct deep-call ABI/stack behavior.
- Review corrections: Retain valid historical residual; reject char_at heap-handle invalidity as a reason to close the whole row. Research assertion that the deep defect has not been fixed is narrowed to no root fix established by this review; current execution is untested.

## zerokind_is_a_corrupt_aggregate_2026-09-03 — E-MIR-TYPE-ZeroKind is a CORRUPT AGGREGATE, not an unset field

- Source receipt: `adjudication_v2_31`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/zerokind_is_a_corrupt_aggregate_2026-09-03.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/llvm/functions/objects.rs:214-260; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/codegen/llvm/functions/objects.rs:311-340; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/statements.spl:298-345; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/function_lowering.spl:1106-1129
```
- Review rationale: Full report evolves from invalid-kind/span observations through tuple nil-type-slot count laws to seed-built Optional<aggregate> materialization and post-fix historical ZeroKind=0. The decisive target code is the FINAL select(src_is_valid, tagged, src_tagged): nil/special sources retain their original value rather than becoming allocated all-zero aggregates. The earlier load-source guard alone would not repair nil semantics. This bounded LLVM copy correction preserves the existing ABI; target MIR now separately diagnoses invalid kind transport, and tuple lowering has changed since report line anchors. Historical later HIR name-resolution and interrupted builds do not negate this narrow remedy or establish full bootstrap success.
- Review corrections: Accept known/no/fixed_pending_verification only for nil Optional aggregate-copy materialization. Correct research focus on selecting zero destination for safe loads: returning src_tagged is the causal fix. Do not generalize to every ZeroKind/transport failure or call the report an unset-field defect.
