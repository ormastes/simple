# Frozen Stage 2 `if val x = dict.get(k)` binds Option box instead of text payload (`_tls_end` AV at `result_err_layout_identity+0x2c`)

- **ID:** `stage2_if_val_text_option_transport_tls_end_2026-11-04`
- **Date:** 2026-11-04
- **Status:** `ROOT-FIXED+STAGE2-GATED` — current tip MIR lowering handles `Dict<i64, text>.get(k)` and `text?` `if val` interpolation via `rt_strcat_tagged` without `rt_value_as_int_wide` or `rt_raw_i64_to_string`; the `# @workaround bug=stage2_if_val_text_option_transport_tls_end_2026-11-04` guard in `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1590` remains Stage-2-gated until the frozen Stage 2 compiler seed is superseded.

## Symptom

When compiled by the frozen Stage 2 binary, `if val stable_owner = self.array_element_struct_syms.get(base_local.id)` inside `MirLowering.remember_array_index_projection_provenance` could bind the `Option` box rather than the unwrapped `text` payload. Passing `stable_owner` into `result_err_layout_identity` then interpolated garbage text and triggered an access violation (`s4e e0011 _tls_end AV`, frame `result_err_layout_identity+0x2c`).

## Workaround

Commit `dc662dde275` replaced the `if val` binding at `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1590-1592` with an eager null-coalescing unwrap into a bare `text`:

```simple
# @workaround bug=stage2_if_val_text_option_transport_tls_end_2026-11-04 reason=frozen stage2 can bind the Option box (not the text payload) for `if val x = dict.get(k)`; result_err_layout_identity then interpolates a garbage text (s4e e0011 _tls_end AV, frame result_err_layout_identity+0x2c). Unwrap with ?? into a bare text first.
val stable_owner: text = self.array_element_struct_syms.get(base_local.id) ?? ""
if stable_owner != "":
```

## Verification & Retirement

- Pinned by `test/01_unit/compiler/50.mir/wa_src_lane5_workaround_audit_spec.spl` (verifies `Dict<i64, text>.get(k)` and `text?` `if val` interpolation lower cleanly without `rt_value_as_int_wide` / `rt_raw_i64_to_string` while retaining the Stage 2 guard in `expr_dispatch.spl:1590`).
- Retirement condition: supersede the frozen Stage 2 seed with a build containing the current `50.mir` `if val` / `Option<text>` transport fix and verify Stage 3 MIR lowering passes without the `?? ""` guard.
