# V4 lane 02 accepted evidence

Accepted classifications in V4: 160. Assessment target: `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`.

- 157 accepted records are inherited field-for-field from V3; their detailed evidence is preserved in [V3 lane 02 evidence](../evidence_v3/lane02_accepted.md).

- 3 additional accepted records are detailed below.

## freestanding_text_local_recompare_flips_material_admission_2026-08-10 — freestanding x86_64 text local re-comparison flips WM material admission; layers 1-2 only

- Source receipt: `first_half_final_triage`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/freestanding_text_local_recompare_flips_material_admission_2026-08-10.md;c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/text_layout/font_renderer.spl:2438-2463;4e1d05ba67a49ca5c40618e7a5f4ccc387818bca; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/text_layout/font_renderer.spl:2436-2537; history 88aac2ffe28 and ae55a746719 (-L reset-font-atlas ancestry)
```
- Review rationale: The historical allocation exhaustion is supported by the late report, but the old in-place-zeroing remedy is not the target reset body. Line history shows the restoring tree already allocating a fresh atlas and the later transplant adding ownership state. More importantly, the live _switch_font_atlas parks outgoing pixel arrays under their font key, restores incoming arrays wholesale, removes the active park slot, and resets only on a miss or explicit PARK=0 control. Blindly reinstating old zero-in-place logic could overwrite arrays retained for the outgoing owner. This is a materially different ownership path, so neither the prior reuse patch nor the remaining allocation line alone proves current repair or failure. Unknown remedy is the supported classification; source-matched allocator/park lifetime and original recompare qualification remain future diagnosis work.
- Review corrections: Removed the assumed presence/applicability of 4e1d05 reuse logic. Current park ownership explains why the old local fix cannot simply be replayed; no runtime or fixed claim.

## impl_to_free_fn_refactor_family_still_incomplete_2026-08-08 — impl-to-free-fn refactor left ~40 zero-definition call sites in live compiler passes

- Source receipt: `first_half_final_triage`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: src/compiler/00.common/predicate_parser.spl:121-129; src/compiler/15.blocks/blocks/easy.spl:103-123; doc/08_tracking/bug/impl_to_free_fn_refactor_family_still_incomplete_2026-08-08.md:405-523; research_v2_09.csv#impl_to_free_fn_refactor_family_still_incomplete_2026-08-08; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/desugar/desugar_async.spl:37-63; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/90.tools/desugar_async.spl:32-58; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/15.blocks/blocks/definition.spl:51-70; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/15.blocks/blocks/registry.spl:15-29,190-202; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/lib/std/src/spec/formatter/markdown.spl:10,164; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:798-827; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/common/impl_to_free_fn_class_a_call_sites_spec.spl:117-120
```
- Review rationale: Reconciled all twelve late-report Class A hits: two response_text examples, two parser examples, pattern_trim, and two blk_lexer_mode examples are documentation, not executable unresolved calls; markdown imports exist as path_file_exists; all four named Vulkan helpers have real guarded bodies and engine imports. This invalidates the twelve-current-broken-sites census, not the historical refactor damage. The report also tracks a broader historical family and eight Class C stdlib/missing-module sites; those are not closed by repairing the census. A global mechanically known remedy or complete current-clean claim is unsupported, so retain valid/unknown/untested and keep_open without replaying the false positives.
- Review corrections: The late twelve-site Class A count is not an active-call inventory. Corrected documentation and import-alias false positives; no invalid closure of the historical family.

## impl_to_free_fn_refactor_family_sweep_2026-08-07 — `impl X:` -> free-function refactor wreckage: family sweep (2026-08-07)

- Source receipt: `first_half_final_triage`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: src/compiler/35.semantics/macro_check/template.spl:39-56,168-205; doc/08_tracking/bug/impl_to_free_fn_refactor_family_sweep_2026-08-07.md:77-187; research_v2_09.csv#impl_to_free_fn_refactor_family_sweep_2026-08-07; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/35.semantics/macro_check/hygiene.spl:203-265; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/35.semantics/macro_check/mod.spl:147-188; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/capability_tracker.spl:41-85; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/15.blocks/blocks/builder.spl:412-428; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/40.mono/monomorphize/tracker.spl:86-110; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/exhaustiveness_validator.spl:116; target absence of src/compiler/70.backend/backend/common/expression_evaluator.spl
```
- Review rationale: The twenty-three-site statement is a historical census, not a target repair plan. Template and macro owners use real member operations; hygiene uses contains_key/index plus explicit struct writeback, macro lookup uses guarded indexing, capability tracking takes the length of an array of InstructionSupport, builder appends examples, and tracker explicitly snapshots metadata before adding dependencies. Thus the old Dict.len hazard is not established by the actual capability receiver. The expression evaluator path no longer exists at target; no semantic-successor or total family repair claim is made. These concrete corrections support keeping the real historical damage valid while withdrawing a universal rewrite remedy. The broader free-function residual list still needs per-owner diagnosis before any repair proposal.
- Review corrections: Do not reuse the outdated 23/8 census or universal dot-call rewrite. Current inspected owners preserve different mutation/snapshot contracts; unknown aggregate solution is deliberate, not an all-fixed conclusion.
