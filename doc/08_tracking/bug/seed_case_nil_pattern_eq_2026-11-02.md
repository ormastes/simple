# seed_case_nil_pattern_eq_2026-11-02

**Severity:** P0 (stage2_next native-build worker crash, 0xC0000005)
**Status:** FIXED in seed (PR #5882); all 6 `80.driver` `@workaround` comment tags retired (`case None:` retained per safe-code `case nil:` ban).

## Symptom
A stage2_next (seed-built from release f5b32bda67c) `native-build` of hello dies right after
`phase=load_sources` with `native-build worker terminated with Windows native status 0xC0000005`.
I attached lldb to the worker (`stage2.exe run src/app/cli/native_build_worker.spl ...`). It faults at
`compiler__driver__driver_build__incremental__native_build_cache_scope_key+372`, which is
`movq (%rsi),%rax` with rsi = 0 (nil 3 & ~7).

## Root cause
The Rust seed (`hir/lower/expr/control.rs`) lowered a `case nil:` literal pattern as an
equality. For a `text?` subject this became `rt_string_eq(subject, nil)`, and that returns 0 for nil vs nil.
So the nil arm never matches, the match falls through and yields nil, and
`canon.features` dereferences null. `case None:` takes the dedicated `rt_is_none` path and is correct.

## Fix
- Seed: a nil literal pattern now lowers to `rt_is_none`, at top level and nested (PR #5882). Unit test:
  `test_nil_literal_pattern_on_optional_text_uses_is_none`.
- Source workaround (tagged `@workaround bug=seed_case_nil_pattern_eq_2026-11-02`): `case nil:` was
  changed to `case None:` at the 6 sites in `src/compiler/80.driver/driver_build/`. The remaining sites (1527 sites in 352
  files) are being rewritten by a separate lane.

## Removal
Remove the tags after stage2 is rebuilt with a seed that contains #5882.

## WA-S1 partial retirement 2026-11-26
- Retired stale `# @workaround bug=seed_case_nil_pattern_eq_2026-11-02` marker in `src/compiler/80.driver/driver_build/file_fiber_tldr_bridge_v1.spl` while keeping `case None:` intact (safe across frozen seeds and Stage 3).
- Kept `src/compiler/80.driver/driver_build/incremental.spl` (`incremental_digest_tag_v1` and `incremental_digest_untag_v1`) unchanged (`DEFERRED-CROSS-LANE`) because both function bodies are SHA-256 pinned in `src/verification/cache_protocol/source_bindings.txt` and enforced by `scripts/check/check-cache-formal-source-binding.shs`.
- Regression spec: `test/01_unit/compiler/80.driver/wa_src_lane1_workarounds_spec.spl`

## W8-1 retirement 2026-11-27
- Retired the remaining 3 stale `# @workaround bug=seed_case_nil_pattern_eq_2026-11-02` comment tags in `src/compiler/80.driver/driver_build/incremental.spl` (`incremental_digest_tag_v1` and `incremental_digest_untag_v1`) and `src/compiler/80.driver/driver_build/native_link_receipt_v1.spl` (`_toolchain_digests_v1`), while keeping `case None:` intact across all 6 `driver_build` sites (safe across pre-#5882/post-#5882 seeds and Stage 3, and compliant with S-11 safe-code `case nil:` policy).
- Verified PR #5882 seed fix (`test_nil_literal_pattern_on_optional_text_uses_is_none` at `src/compiler_rust/compiler/src/hir/lower/tests/control_flow_tests.rs:1497`) is present at HEAD.
- Re-pinned `incremental_digest_tag_v1`, `incremental_digest_untag_v1`, and `_toolchain_digests_v1` in `src/verification/cache_protocol/source_bindings.txt` with formal model review addendum in `src/verification/cache_protocol/seed_case_none_workaround_review_2026-11-02.txt`.
- Tracking shard: `doc/08_tracking/bug/db/seed_case_nil_pattern_eq_2026-11-02.sdn` (`status=fixed`).
- Verified specs (`--mode=interpreter`): `test/01_unit/compiler/80.driver/seed_case_nil_wa_retirement_spec.spl` (3/3), `test/01_unit/compiler/driver/build_cache_digest_tag_spec.spl` (3/3), `test/01_unit/compiler/driver/native_link_toolchain_key_spec.spl` (2/2), `test/01_unit/compiler/semantics/robust_nil_pattern_spec.spl` (4/4).
