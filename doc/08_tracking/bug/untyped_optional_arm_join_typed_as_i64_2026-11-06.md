# untyped_optional_arm_join_typed_as_i64_2026-11-06 (P1)

Status: open (P1)

## Bug
An UNTYPED value-position `if`/`elif`/`match` binding whose arms mix `nil`,
`T?` and `T` (`val t = match ..: Some(HirType(..)) | _ => nil`,
`var v = if c: LocalId else: LocalId?`) got no Optional type at the MIR merge:
the slot kept the first arm's MIR type (i64 / struct / void) and none of the
`option_value_locals` / runtime-value marks that an annotated `T?` binding gets.
Downstream the raw word took plain-T paths: `push(h)` boxed it through
`rt_value_int_wide` (pointer << 3, int-tagged), or a raw Option word reached a
plain-T slot. Site work-arounds: #7066, #7069, #7224 (switch_operators_calls
`var v = if ..: LocalId else: LocalId?`), #7268 (statements.spl
`try_register_local_tuple_type`, `val elem_hir_type = match .. Some(HirType(..)) / nil`).

## Root cause
`src/compiler/50.mir`: the merge join of every untyped if/match
(`lower_if`, `lower_if_chain`, `lower_enum_match`, `emit_switch_dispatch`,
`emit_if_chain_dispatch`, `lower_guarded_scalar_match`) never produced `T?`:
1. `mir_merge_arm_types` / the match `inferred_ty` keep the first arm's MIR type.
2. `remember_merged_optional_arm_type` refused any `nil` arm outside `unsafe:`
   (d87ef84a4db, stale since ERR-01 rev 3: `nil` is the canonical `T?` absence
   in safe code), refused mixed `T` / `T?` arms (`hir_types_equal(T, T?)` false),
   and even when it adopted `T?` it set only the HIR type, not the option /
   runtime-value marks or the i64 word MIR type.
3. The int-literal match dispatchers (`emit_switch_dispatch`,
   `emit_if_chain_dispatch`, `lower_guarded_scalar_match`) had no arm-identity
   join at all.

## Fix
`join_untyped_optional_arms` (mir_lowering_stmts.spl), called at all six
merges when there is no expected type: if any arm is `nil`/`None` or `T?` and
every value arm agrees on the payload `T` (`T?` arms unwrapped), the slot is
`T?`: MIR type i64, HIR `Optional(T)`, option + runtime-value marks. When a
bare `T` arm is present the merged word is normalised by
`normalize_option_handle` (handle unchanged, sentinel 3 -> None, other word
-> Some). Ambiguous joins (untyped arm, disagreeing payloads, bare scalar /
generic `T`) keep the old behaviour, and under `SIMPLE_SAFETY_PROFILE=robust|critical`
are a fatal `E-OPT-JOIN` type error instead of a guess.

## Evidence
Fixtures (C:/dev/p3new/s3sanity/root/test/s3sanity/): `oj_match`, `oj_ifvar`,
`oj_mixed`, `oj_ifonly`, controls `oj_plain`, `oj_matcht`.

Native BEFORE, copy of s3_fable50.exe (`s3_ojcopy.exe`, run_case_dir.ps1):
- `oj_plain` (no optional join, control): `rc=0 stdout=[PASS oj_plain]`.
- `oj_ifonly` (`val t = if ..: Some(HirT(..)) else: nil`; `if val h = t: out.push(h)`):
  COMPILE-FAIL `E-BACKEND-LLVM-CONST-TYPE: integer constant cannot define void`
  in `__simple_main` (merge temp typed void from the Some arm, nil const copied in).
- `oj_match`, `oj_ifvar`, `oj_mixed`: compiler AV 0xC0000005 in
  `mir_lower:first_module`; the annotated control `oj_matcht` AVs the same way,
  so that AV is a separate match-literal crash and is NOT counted as evidence here.

Interpreter (seed bin/simple.exe run): `oj_match` PASS, `oj_ifvar` PASS,
`oj_mixed` rc=32 with `s=103079215125` (a pointer-sized word summed as an int —
the same family on the seed's lane).

MIR unit spec `test/01_unit/compiler/50.mir/untyped_optional_arm_join_spec.spl`:
before the fix 2/9 pass (the two pass vacuously), after 9/9; the
`enum_subject_owner_recovery_spec` safe-`nil` row flipped to the ERR-01 rev 3
expectation and passes 11/11.

Native AFTER: pending a stage3 rebuilt with this change (phase-3 lead folds the
edited hot files into the next leaf; see C:/dev/p3new/s3new/fable_milestones.md).

## Similar-pattern sweep
`sh scripts/check/check-untyped-optional-arm-join.shs` (advisory census over
src/compiler): 345 untyped if/match bindings with `nil`/`Some(`/`None` arms,
all now typed by the root join (ambiguous ones are robust-mode errors). List:

```
src/compiler/00.common/_Attributes/decl_attrs.spl:791: val align_arg = if attr.args.len() > 0: extract_int_arg(attr.args[0]) else: nil
src/compiler/00.common/cache_contract/canonical_cache_codec_v1.spl:993: val envelope = match decoded.value:
src/compiler/00.common/cache_contract/canonical_cache_codec_v1.spl:1124: val envelope = match decoded.value:
src/compiler/00.common/cache_contract/canonical_cache_codec_v1.spl:1140: val effect = match _effect_from_tag_v1(effect_tag):
src/compiler/00.common/cache_contract/canonical_cache_codec_v1.spl:1151: val replay = match _replay_from_tag_v1(replay_tag):
src/compiler/20.hir/generated/hir_codec.spl:194: val ev0 = if raw1 == "\\N": nil else: flat_pool_unescape(raw1)
src/compiler/20.hir/generated/hir_codec.spl:198: val f_has_os = if raw2 == "N": nil else: raw2 == "1"
src/compiler/20.hir/generated/hir_codec.spl:202: val f_os = if raw3 == "\\N": nil else: flat_pool_unescape(raw3)
src/compiler/20.hir/generated/hir_codec.spl:204: val f_has_abi = if raw4 == "N": nil else: raw4 == "1"
src/compiler/20.hir/generated/hir_codec.spl:208: val f_abi = if raw5 == "\\N": nil else: flat_pool_unescape(raw5)
src/compiler/20.hir/generated/hir_codec.spl:210: val f_has_backend = if raw6 == "N": nil else: raw6 == "1"
src/compiler/20.hir/generated/hir_codec.spl:214: val f_backend = if raw7 == "\\N": nil else: flat_pool_unescape(raw7)
src/compiler/20.hir/generated/hir_codec.spl:246: val f_version = if raw1 == "N": nil else: flat_pool_parse_i64(raw1)
src/compiler/20.hir/generated/hir_codec.spl:334: val f_id = if raw0 == "N": nil else: flat_pool_parse_i64(raw0)
src/compiler/20.hir/generated/hir_codec.spl:340: val f_id = if raw1 == "N": nil else: flat_pool_parse_i64(raw1)
src/compiler/20.hir/generated/hir_codec.spl:465: val f_value = if raw0 == "N": nil else: flat_pool_parse_i64(raw0)
src/compiler/20.hir/generated/hir_codec.spl:476: val ov2 = if raw3 == "N": nil else: flat_pool_parse_i64(raw3)
src/compiler/20.hir/generated/hir_codec.spl:481: val ov4 = if raw5 == "N": nil else: flat_pool_parse_i64(raw5)
src/compiler/20.hir/generated/hir_codec.spl:492: val f_id = if raw6 == "N": nil else: flat_pool_parse_i64(raw6)
src/compiler/20.hir/generated/hir_codec.spl:567: val f_driver_class = if raw0 == "N": nil else: flat_pool_parse_i64(raw0)
src/compiler/20.hir/generated/hir_codec.spl:571: val f_vendor = if raw1 == "N": nil else: flat_pool_parse_i64(raw1)
src/compiler/20.hir/generated/hir_codec.spl:579: val ev2 = if raw3 == "N": nil else: flat_pool_parse_i64(raw3)
src/compiler/20.hir/generated/hir_codec.spl:731: val f_is_export_c = if raw0 == "N": nil else: raw0 == "1"
src/compiler/20.hir/generated/hir_codec.spl:791: val f_is_entry = if raw0 == "N": nil else: raw0 == "1"
src/compiler/20.hir/generated/hir_codec.spl:795: val f_is_naked = if raw1 == "N": nil else: raw1 == "1"
src/compiler/20.hir/generated/hir_codec.spl:799: val f_is_noreturn = if raw2 == "N": nil else: raw2 == "1"
src/compiler/20.hir/generated/hir_codec.spl:803: val f_is_inline = if raw3 == "N": nil else: raw3 == "1"
src/compiler/20.hir/generated/hir_codec.spl:809: val ov4 = if raw5 == "\\N": nil else: flat_pool_unescape(raw5)
src/compiler/20.hir/generated/hir_codec.spl:812: val f_is_interrupt = if raw6 == "N": nil else: raw6 == "1"
src/compiler/20.hir/generated/hir_codec.spl:816: val f_is_boot = if raw7 == "N": nil else: raw7 == "1"
src/compiler/20.hir/generated/hir_codec.spl:820: val f_is_alloc = if raw8 == "N": nil else: raw8 == "1"
src/compiler/20.hir/generated/hir_codec.spl:824: val f_is_no_alloc = if raw9 == "N": nil else: raw9 == "1"
src/compiler/20.hir/generated/hir_codec.spl:828: val f_is_gpu_kernel = if raw10 == "N": nil else: raw10 == "1"
src/compiler/20.hir/generated/hir_codec.spl:836: val f_is_simd = if raw13 == "N": nil else: raw13 == "1"
src/compiler/20.hir/generated/hir_codec.spl:840: val f_has_fast_math = if raw14 == "N": nil else: raw14 == "1"
src/compiler/20.hir/generated/hir_codec.spl:844: val f_simd_enable = if raw15 == "N": nil else: raw15 == "1"
src/compiler/20.hir/generated/hir_codec.spl:848: val f_simd_disable = if raw16 == "N": nil else: raw16 == "1"
src/compiler/20.hir/generated/hir_codec.spl:852: val f_simd_prefer_scalable = if raw17 == "N": nil else: raw17 == "1"
src/compiler/20.hir/generated/hir_codec.spl:859: val f_unroll_factor = if raw18 == "N": nil else: flat_pool_parse_i64(raw18)
src/compiler/20.hir/generated/hir_codec.spl:863: val f_pipeline_ii = if raw19 == "N": nil else: flat_pool_parse_i64(raw19)
src/compiler/20.hir/generated/hir_codec.spl:867: val f_memory_banks = if raw20 == "N": nil else: flat_pool_parse_i64(raw20)
src/compiler/20.hir/generated/hir_codec.spl:871: val f_is_rt_hal = if raw21 == "N": nil else: raw21 == "1"
src/compiler/20.hir/generated/hir_codec.spl:875: val f_rt_hal_compare_c = if raw22 == "N": nil else: raw22 == "1"
src/compiler/20.hir/generated/hir_codec.spl:879: val f_rt_hal_compare_rust = if raw23 == "N": nil else: raw23 == "1"
src/compiler/20.hir/generated/hir_codec.spl:885: val f_is_volatile = if raw25 == "N": nil else: raw25 == "1"
src/compiler/20.hir/generated/hir_codec.spl:889: val f_is_no_reorder = if raw26 == "N": nil else: raw26 == "1"
src/compiler/20.hir/generated/hir_codec.spl:893: val f_align = if raw27 == "N": nil else: flat_pool_parse_i64(raw27)
src/compiler/20.hir/generated/hir_codec.spl:897: val f_is_global = if raw28 == "N": nil else: raw28 == "1"
src/compiler/20.hir/generated/hir_codec.spl:903: val f_is_comdat_instance = if raw30 == "N": nil else: raw30 == "1"
src/compiler/20.hir/generated/hir_codec.spl:937: val f_priority = if raw3 == "N": nil else: flat_pool_parse_i64(raw3)
src/compiler/20.hir/generated/hir_codec.spl:1017: val f_is_volatile = if raw1 == "N": nil else: raw1 == "1"
src/compiler/20.hir/generated/hir_codec.spl:1034: val ev3 = if raw4 == "\\N": nil else: flat_pool_unescape(raw4)
src/compiler/20.hir/generated/hir_codec.spl:1042: val ev5 = if raw6 == "\\N": nil else: flat_pool_unescape(raw6)
src/compiler/20.hir/generated/hir_codec.spl:1050: val ev7 = if raw8 == "\\N": nil else: flat_pool_unescape(raw8)
src/compiler/20.hir/generated/hir_codec.spl:1170: val f_has_spec = if raw0 == "N": nil else: raw0 == "1"
src/compiler/20.hir/generated/hir_codec.spl:1177: val f_is_wildcard = if raw1 == "N": nil else: raw1 == "1"
src/compiler/20.hir/generated/hir_codec.spl:1181: val f_has_asm_body = if raw2 == "N": nil else: raw2 == "1"
src/compiler/20.hir/generated/hir_codec.spl:1188: val f_is_compile_error = if raw3 == "N": nil else: raw3 == "1"
src/compiler/20.hir/generated/hir_codec.spl:1302: val f_has_default = if raw2 == "N": nil else: raw2 == "1"
src/compiler/20.hir/generated/hir_codec.spl:1593: val f_total_bits = if raw2 == "N": nil else: flat_pool_parse_i64(raw2)
src/compiler/20.hir/generated/hir_codec.spl:1600: val f_is_public = if raw3 == "N": nil else: raw3 == "1"
src/compiler/20.hir/generated/hir_codec.spl:1604: val f_has_doc_comment = if raw4 == "N": nil else: raw4 == "1"
src/compiler/20.hir/generated/hir_codec.spl:1608: val f_doc_comment = if raw5 == "\\N": nil else: flat_pool_unescape(raw5)
src/compiler/20.hir/generated/hir_codec.spl:1655: val f_has_type_ = if raw1 == "N": nil else: raw1 == "1"
src/compiler/20.hir/generated/hir_codec.spl:1662: val f_bit_width = if raw2 == "N": nil else: flat_pool_parse_i64(raw2)
src/compiler/20.hir/generated/hir_codec.spl:1666: val f_bit_offset = if raw3 == "N": nil else: flat_pool_parse_i64(raw3)
src/compiler/20.hir/generated/hir_codec.spl:1670: val f_is_reserved = if raw4 == "N": nil else: raw4 == "1"
src/compiler/20.hir/generated/hir_codec.spl:1724: val f_has = if raw1 == "N": nil else: raw1 == "1"
src/compiler/20.hir/generated/hir_codec.spl:1738: val ev2 = if raw3 == "\\N": nil else: flat_pool_unescape(raw3)
src/compiler/20.hir/generated/hir_codec.spl:1770: val f_has_name = if raw0 == "N": nil else: raw0 == "1"
src/compiler/20.hir/generated/hir_codec.spl:1774: val f_name = if raw1 == "\\N": nil else: flat_pool_unescape(raw1)
src/compiler/20.hir/generated/hir_codec.spl:1825: val f_has_pattern = if raw0 == "N": nil else: raw0 == "1"
src/compiler/20.hir/generated/hir_codec.spl:1832: val f_has_type_ = if raw1 == "N": nil else: raw1 == "1"
src/compiler/20.hir/generated/hir_codec.spl:1983: val dk3 = if raw4 == "\\N": nil else: flat_pool_unescape(raw4)
src/compiler/20.hir/generated/hir_codec.spl:1994: val f_is_public = if raw5 == "N": nil else: raw5 == "1"
src/compiler/20.hir/generated/hir_codec.spl:1998: val f_has_doc_comment = if raw6 == "N": nil else: raw6 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2002: val f_doc_comment = if raw7 == "\\N": nil else: flat_pool_unescape(raw7)
src/compiler/20.hir/generated/hir_codec.spl:2007: val f_has_layout_attr = if raw8 == "N": nil else: raw8 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2014: val f_has_export_attr = if raw9 == "N": nil else: raw9 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2021: val f_has_platform_attr = if raw10 == "N": nil else: raw10 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2025: val f_platform_has_error = if raw11 == "N": nil else: raw11 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2029: val f_platform_has_warning = if raw12 == "N": nil else: raw12 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2035: val f_platform_diagnostic_line = if raw14 == "N": nil else: flat_pool_parse_i64(raw14)
src/compiler/20.hir/generated/hir_codec.spl:2039: val f_is_generic_template = if raw15 == "N": nil else: raw15 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2043: val f_has_specialization_of = if raw16 == "N": nil else: raw16 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2047: val f_specialization_of = if raw17 == "\\N": nil else: flat_pool_unescape(raw17)
src/compiler/20.hir/generated/hir_codec.spl:2053: val dk18 = if raw19 == "\\N": nil else: flat_pool_unescape(raw19)
src/compiler/20.hir/generated/hir_codec.spl:2065: val ev20 = if raw21 == "\\N": nil else: flat_pool_unescape(raw21)
src/compiler/20.hir/generated/hir_codec.spl:2069: val f_cfg_group = if raw22 == "N": nil else: flat_pool_parse_i64(raw22)
src/compiler/20.hir/generated/hir_codec.spl:2073: val f_cfg_arm = if raw23 == "N": nil else: flat_pool_parse_i64(raw23)
src/compiler/20.hir/generated/hir_codec.spl:2262: val f_is_mutable = if raw1 == "N": nil else: raw1 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2269: val f_is_public = if raw2 == "N": nil else: raw2 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2273: val f_is_volatile = if raw3 == "N": nil else: raw3 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2277: val f_has_fixed_address = if raw4 == "N": nil else: raw4 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2281: val f_fixed_address = if raw5 == "N": nil else: flat_pool_parse_i64(raw5)
src/compiler/20.hir/generated/hir_codec.spl:2289: val ev6 = if raw7 == "\\N": nil else: flat_pool_unescape(raw7)
src/compiler/20.hir/generated/hir_codec.spl:2293: val f_cfg_group = if raw8 == "N": nil else: flat_pool_parse_i64(raw8)
src/compiler/20.hir/generated/hir_codec.spl:2297: val f_cfg_arm = if raw9 == "N": nil else: flat_pool_parse_i64(raw9)
src/compiler/20.hir/generated/hir_codec.spl:2628: val f_is_public = if raw4 == "N": nil else: raw4 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2632: val f_has_doc_comment = if raw5 == "N": nil else: raw5 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2636: val f_doc_comment = if raw6 == "\\N": nil else: flat_pool_unescape(raw6)
src/compiler/20.hir/generated/hir_codec.spl:2641: val f_is_generic_template = if raw7 == "N": nil else: raw7 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2645: val f_has_specialization_of = if raw8 == "N": nil else: raw8 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2649: val f_specialization_of = if raw9 == "\\N": nil else: flat_pool_unescape(raw9)
src/compiler/20.hir/generated/hir_codec.spl:2655: val dk10 = if raw11 == "\\N": nil else: flat_pool_unescape(raw11)
src/compiler/20.hir/generated/hir_codec.spl:2672: val f_complete_open = if raw13 == "N": nil else: raw13 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2676: val f_dyn_open = if raw14 == "N": nil else: raw14 == "1"
src/compiler/20.hir/generated/hir_codec.spl:2684: val ev15 = if raw16 == "\\N": nil else: flat_pool_unescape(raw16)
src/compiler/20.hir/generated/hir_codec.spl:2688: val f_cfg_group = if raw17 == "N": nil else: flat_pool_parse_i64(raw17)
src/compiler/20.hir/generated/hir_codec.spl:2692: val f_cfg_arm = if raw18 == "N": nil else: flat_pool_parse_i64(raw18)
src/compiler/20.hir/generated/hir_codec.spl:2750: val pa1 = if raw2 == "\\N": nil else: flat_pool_unescape(raw2)
src/compiler/20.hir/generated/hir_codec.spl:2796: val f_has_type_ = if raw0 == "N": nil else: raw0 == "1"
src/compiler/20.hir/generated/hir_codec.spl:3674: val f_value = if raw0 == "N": nil else: flat_pool_parse_i64(raw0)
src/compiler/20.hir/generated/hir_codec.spl:3680: val ov1 = if raw2 == "\\N": nil else: flat_pool_unescape(raw2)
src/compiler/20.hir/generated/hir_codec.spl:3688: val ov3 = if raw4 == "\\N": nil else: flat_pool_unescape(raw4)
src/compiler/20.hir/generated/hir_codec.spl:3875: val f_index = if raw21 == "N": nil else: flat_pool_parse_i64(raw21)
src/compiler/20.hir/generated/hir_codec.spl:4057: val ov33 = if raw34 == "\\N": nil else: flat_pool_unescape(raw34)
src/compiler/20.hir/generated/hir_codec.spl:4070: val ov35 = if raw36 == "\\N": nil else: flat_pool_unescape(raw36)
src/compiler/20.hir/generated/hir_codec.spl:4086: val ov37 = if raw38 == "\\N": nil else: flat_pool_unescape(raw38)
src/compiler/20.hir/generated/hir_codec.spl:4133: val f_lane_code = if raw42 == "N": nil else: flat_pool_parse_i64(raw42)
src/compiler/20.hir/generated/hir_codec.spl:4137: val f_payload_size = if raw43 == "N": nil else: flat_pool_parse_i64(raw43)
src/compiler/20.hir/generated/hir_codec.spl:4176: val ov47 = if raw48 == "\\N": nil else: flat_pool_unescape(raw48)
src/compiler/20.hir/generated/hir_codec.spl:4211: val pa50 = if raw51 == "\\N": nil else: flat_pool_unescape(raw51)
src/compiler/20.hir/generated/hir_codec.spl:4397: val ov65 = if raw66 == "\\N": nil else: flat_pool_unescape(raw66)
src/compiler/20.hir/generated/hir_codec.spl:4412: val ev67 = if raw68 == "\\N": nil else: flat_pool_unescape(raw68)
src/compiler/20.hir/generated/hir_codec.spl:4594: val f_has_default = if raw1 == "N": nil else: raw1 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4604: val f_is_public = if raw2 == "N": nil else: raw2 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4608: val f_is_volatile = if raw3 == "N": nil else: raw3 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4612: val f_has_bits_attr = if raw4 == "N": nil else: raw4 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4616: val f_bits_width = if raw5 == "N": nil else: flat_pool_parse_i64(raw5)
src/compiler/20.hir/generated/hir_codec.spl:4620: val f_has_fixed_address = if raw6 == "N": nil else: raw6 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4624: val f_fixed_address = if raw7 == "N": nil else: flat_pool_parse_i64(raw7)
src/compiler/20.hir/generated/hir_codec.spl:4807: val f_is_async = if raw4 == "N": nil else: raw4 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4811: val f_is_static = if raw5 == "N": nil else: raw5 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4815: val f_is_public = if raw6 == "N": nil else: raw6 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4819: val f_is_method = if raw7 == "N": nil else: raw7 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4823: val f_is_mutable = if raw8 == "N": nil else: raw8 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4827: val f_is_const = if raw9 == "N": nil else: raw9 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4831: val f_is_extern = if raw10 == "N": nil else: raw10 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4838: val f_has_export_attr = if raw11 == "N": nil else: raw11 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4845: val f_has_driver_manifest_attr = if raw12 == "N": nil else: raw12 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4852: val f_has_suspension = if raw13 == "N": nil else: raw13 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4856: val f_has_vhdl_metadata = if raw14 == "N": nil else: raw14 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4863: val f_has_doc_comment = if raw15 == "N": nil else: raw15 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4867: val f_doc_comment = if raw16 == "\\N": nil else: flat_pool_unescape(raw16)
src/compiler/20.hir/generated/hir_codec.spl:4872: val f_is_gpu_kernel = if raw17 == "N": nil else: raw17 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4886: val f_is_generic_template = if raw21 == "N": nil else: raw21 == "1"
src/compiler/20.hir/generated/hir_codec.spl:4894: val ev22 = if raw23 == "\\N": nil else: flat_pool_unescape(raw23)
src/compiler/20.hir/generated/hir_codec.spl:4898: val f_cfg_group = if raw24 == "N": nil else: flat_pool_parse_i64(raw24)
src/compiler/20.hir/generated/hir_codec.spl:4902: val f_cfg_arm = if raw25 == "N": nil else: flat_pool_parse_i64(raw25)
src/compiler/20.hir/generated/hir_codec.spl:4906: val f_extern_runtime_value_abi = if raw26 == "N": nil else: flat_pool_parse_i64(raw26)
src/compiler/20.hir/generated/hir_codec.spl:5061: val f_has_trait_ = if raw0 == "N": nil else: raw0 == "1"
src/compiler/20.hir/generated/hir_codec.spl:5090: val dk3 = if raw4 == "\\N": nil else: flat_pool_unescape(raw4)
src/compiler/20.hir/generated/hir_codec.spl:5102: val dk5 = if raw6 == "\\N": nil else: flat_pool_unescape(raw6)
src/compiler/20.hir/generated/hir_codec.spl:5104: val dv5 = if raw7 == "\\N": nil else: flat_pool_unescape(raw7)
src/compiler/20.hir/generated/hir_codec.spl:5113: val dk8 = if raw9 == "\\N": nil else: flat_pool_unescape(raw9)
src/compiler/20.hir/generated/hir_codec.spl:5115: val dv8 = if raw10 == "N": nil else: raw10 == "1"
src/compiler/20.hir/generated/hir_codec.spl:5124: val dk11 = if raw12 == "\\N": nil else: flat_pool_unescape(raw12)
src/compiler/20.hir/generated/hir_codec.spl:5126: val dv11 = if raw13 == "N": nil else: raw13 == "1"
src/compiler/20.hir/generated/hir_codec.spl:5144: val ev15 = if raw16 == "\\N": nil else: flat_pool_unescape(raw16)
src/compiler/20.hir/generated/hir_codec.spl:5148: val f_cfg_group = if raw17 == "N": nil else: flat_pool_parse_i64(raw17)
src/compiler/20.hir/generated/hir_codec.spl:5152: val f_cfg_arm = if raw18 == "N": nil else: flat_pool_parse_i64(raw18)
src/compiler/20.hir/generated/hir_codec.spl:5200: val f_is_lazy = if raw2 == "N": nil else: raw2 == "1"
src/compiler/20.hir/generated/hir_codec.spl:5241: val ov1 = if raw2 == "\\N": nil else: flat_pool_unescape(raw2)
src/compiler/20.hir/generated/hir_codec.spl:5281: val f_has_format = if raw0 == "N": nil else: raw0 == "1"
src/compiler/20.hir/generated/hir_codec.spl:5285: val f_format = if raw1 == "\\N": nil else: flat_pool_unescape(raw1)
src/compiler/20.hir/generated/hir_codec.spl:5335: val f_has_guard = if raw0 == "N": nil else: raw0 == "1"
src/compiler/20.hir/generated/hir_codec.spl:5654: val ev3 = if raw4 == "\\N": nil else: flat_pool_unescape(raw4)
src/compiler/20.hir/generated/hir_codec.spl:5692: val dk7 = if raw8 == "\\N": nil else: flat_pool_unescape(raw8)
src/compiler/20.hir/generated/hir_codec.spl:5694: val dv7 = if raw9 == "\\N": nil else: flat_pool_unescape(raw9)
src/compiler/20.hir/generated/hir_codec.spl:5703: val dk10 = if raw11 == "\\N": nil else: flat_pool_unescape(raw11)
src/compiler/20.hir/generated/hir_codec.spl:5705: val dv10 = if raw12 == "\\N": nil else: flat_pool_unescape(raw12)
src/compiler/20.hir/generated/hir_codec.spl:5846: val ev25 = if raw26 == "\\N": nil else: flat_pool_unescape(raw26)
src/compiler/20.hir/generated/hir_codec.spl:5869: val f_nogc_strict = if raw29 == "N": nil else: raw29 == "1"
src/compiler/20.hir/generated/hir_codec.spl:5873: val f_nogc_param_effects_checked = if raw30 == "N": nil else: raw30 == "1"
src/compiler/20.hir/generated/hir_codec.spl:5881: val ev31 = if raw32 == "N": nil else: flat_pool_parse_i64(raw32)
src/compiler/20.hir/generated/hir_codec.spl:5893: val ev34 = if raw35 == "\\N": nil else: flat_pool_unescape(raw35)
src/compiler/20.hir/generated/hir_codec.spl:5951: val f_has_default = if raw1 == "N": nil else: raw1 == "1"
src/compiler/20.hir/generated/hir_codec.spl:5961: val f_is_mutable = if raw2 == "N": nil else: raw2 == "1"
src/compiler/20.hir/generated/hir_codec.spl:6002: val f_has_type_ = if raw0 == "N": nil else: raw0 == "1"
src/compiler/20.hir/generated/hir_codec.spl:6208: val pa4 = if raw5 == "\\N": nil else: flat_pool_unescape(raw5)
src/compiler/20.hir/generated/hir_codec.spl:6358: val pa1 = if raw2 == "\\N": nil else: flat_pool_unescape(raw2)
src/compiler/20.hir/generated/hir_codec.spl:6398: val f_has_message = if raw0 == "N": nil else: raw0 == "1"
src/compiler/20.hir/generated/hir_codec.spl:6402: val f_message = if raw1 == "\\N": nil else: flat_pool_unescape(raw1)
src/compiler/20.hir/generated/hir_codec.spl:6679: val f_is_public = if raw3 == "N": nil else: raw3 == "1"
src/compiler/20.hir/generated/hir_codec.spl:6683: val f_has_doc_comment = if raw4 == "N": nil else: raw4 == "1"
src/compiler/20.hir/generated/hir_codec.spl:6687: val f_doc_comment = if raw5 == "\\N": nil else: flat_pool_unescape(raw5)
src/compiler/20.hir/generated/hir_codec.spl:6692: val f_has_layout_attr = if raw6 == "N": nil else: raw6 == "1"
src/compiler/20.hir/generated/hir_codec.spl:6699: val f_has_platform_attr = if raw7 == "N": nil else: raw7 == "1"
src/compiler/20.hir/generated/hir_codec.spl:6703: val f_platform_has_error = if raw8 == "N": nil else: raw8 == "1"
src/compiler/20.hir/generated/hir_codec.spl:6707: val f_platform_has_warning = if raw9 == "N": nil else: raw9 == "1"
src/compiler/20.hir/generated/hir_codec.spl:6713: val f_platform_diagnostic_line = if raw11 == "N": nil else: flat_pool_parse_i64(raw11)
src/compiler/20.hir/generated/hir_codec.spl:6717: val f_is_generic_template = if raw12 == "N": nil else: raw12 == "1"
src/compiler/20.hir/generated/hir_codec.spl:6721: val f_has_specialization_of = if raw13 == "N": nil else: raw13 == "1"
src/compiler/20.hir/generated/hir_codec.spl:6725: val f_specialization_of = if raw14 == "\\N": nil else: flat_pool_unescape(raw14)
src/compiler/20.hir/generated/hir_codec.spl:6731: val dk15 = if raw16 == "\\N": nil else: flat_pool_unescape(raw16)
src/compiler/20.hir/generated/hir_codec.spl:6743: val ev17 = if raw18 == "\\N": nil else: flat_pool_unescape(raw18)
src/compiler/20.hir/generated/hir_codec.spl:6747: val f_cfg_group = if raw19 == "N": nil else: flat_pool_parse_i64(raw19)
src/compiler/20.hir/generated/hir_codec.spl:6751: val f_cfg_arm = if raw20 == "N": nil else: flat_pool_parse_i64(raw20)
src/compiler/20.hir/generated/hir_codec.spl:6842: val f_is_public = if raw2 == "N": nil else: raw2 == "1"
src/compiler/20.hir/generated/hir_codec.spl:6846: val f_is_mutable = if raw3 == "N": nil else: raw3 == "1"
src/compiler/20.hir/generated/hir_codec.spl:6852: val ov4 = if raw5 == "\\N": nil else: flat_pool_unescape(raw5)
src/compiler/20.hir/generated/hir_codec.spl:6855: val f_builtin_method_tag = if raw6 == "N": nil else: flat_pool_parse_i64(raw6)
src/compiler/20.hir/generated/hir_codec.spl:6859: val f_generic_param_count = if raw7 == "N": nil else: flat_pool_parse_i64(raw7)
src/compiler/20.hir/generated/hir_codec.spl:7030: val f_is_public = if raw7 == "N": nil else: raw7 == "1"
src/compiler/20.hir/generated/hir_codec.spl:7034: val f_has_doc_comment = if raw8 == "N": nil else: raw8 == "1"
src/compiler/20.hir/generated/hir_codec.spl:7038: val f_doc_comment = if raw9 == "\\N": nil else: flat_pool_unescape(raw9)
src/compiler/20.hir/generated/hir_codec.spl:7043: val f_is_generic_template = if raw10 == "N": nil else: raw10 == "1"
src/compiler/20.hir/generated/hir_codec.spl:7047: val f_has_specialization_of = if raw11 == "N": nil else: raw11 == "1"
src/compiler/20.hir/generated/hir_codec.spl:7051: val f_specialization_of = if raw12 == "\\N": nil else: flat_pool_unescape(raw12)
src/compiler/20.hir/generated/hir_codec.spl:7057: val dk13 = if raw14 == "\\N": nil else: flat_pool_unescape(raw14)
src/compiler/20.hir/generated/hir_codec.spl:7069: val ev15 = if raw16 == "\\N": nil else: flat_pool_unescape(raw16)
src/compiler/20.hir/generated/hir_codec.spl:7073: val f_cfg_group = if raw17 == "N": nil else: flat_pool_parse_i64(raw17)
src/compiler/20.hir/generated/hir_codec.spl:7077: val f_cfg_arm = if raw18 == "N": nil else: flat_pool_parse_i64(raw18)
src/compiler/20.hir/generated/hir_codec.spl:7437: val f_bits = if raw0 == "N": nil else: flat_pool_parse_i64(raw0)
src/compiler/20.hir/generated/hir_codec.spl:7452: val f_bits = if raw2 == "N": nil else: flat_pool_parse_i64(raw2)
src/compiler/20.hir/generated/hir_codec.spl:7482: val ov4 = if raw5 == "N": nil else: flat_pool_parse_i64(raw5)
src/compiler/20.hir/generated/hir_codec.spl:7633: val f_id = if raw15 == "N": nil else: flat_pool_parse_i64(raw15)
src/compiler/20.hir/generated/hir_codec.spl:7637: val f_level = if raw16 == "N": nil else: flat_pool_parse_i64(raw16)
src/compiler/20.hir/generated/hir_codec.spl:7760: val f_has_default = if raw2 == "N": nil else: raw2 == "1"
src/compiler/20.hir/generated/hir_codec.spl:7867: val f_has_discriminant = if raw1 == "N": nil else: raw1 == "1"
src/compiler/20.hir/generated/hir_codec.spl:7977: val f_has_target = if raw0 == "N": nil else: raw0 == "1"
src/compiler/20.hir/generated/hir_codec.spl:8015: val f_has_explicit_align = if raw0 == "N": nil else: raw0 == "1"
src/compiler/20.hir/generated/hir_codec.spl:8019: val f_explicit_align = if raw1 == "N": nil else: flat_pool_parse_i64(raw1)
src/compiler/20.hir/generated/hir_codec.spl:8023: val f_is_packed = if raw2 == "N": nil else: raw2 == "1"
src/compiler/20.hir/generated/hir_codec.spl:8027: val f_is_preserve_order = if raw3 == "N": nil else: raw3 == "1"
src/compiler/20.hir/generated/hir_codec.spl:8031: val f_is_compactq = if raw4 == "N": nil else: raw4 == "1"
src/compiler/20.hir/generated/hir_codec.spl:8341: val dk1 = if raw2 == "\\N": nil else: flat_pool_unescape(raw2)
src/compiler/20.hir/generated/hir_codec.spl:8366: val f_id = if raw0 == "N": nil else: flat_pool_parse_i64(raw0)
src/compiler/20.hir/generated/hir_codec.spl:8436: val f_start = if raw0 == "N": nil else: flat_pool_parse_i64(raw0)
src/compiler/20.hir/generated/hir_codec.spl:8440: val f_end = if raw1 == "N": nil else: flat_pool_parse_i64(raw1)
src/compiler/20.hir/generated/hir_codec.spl:8444: val f_line = if raw2 == "N": nil else: flat_pool_parse_i64(raw2)
src/compiler/20.hir/generated/hir_codec.spl:8448: val f_col = if raw3 == "N": nil else: flat_pool_parse_i64(raw3)
src/compiler/20.hir/generated/hir_codec.spl:8454: val f_length = if raw5 == "N": nil else: flat_pool_parse_i64(raw5)
src/compiler/20.hir/generated/hir_codec.spl:8473: val f_id = if raw0 == "N": nil else: flat_pool_parse_i64(raw0)
src/compiler/20.hir/generated/hir_codec.spl:8679: val dk0 = if raw1 == "N": nil else: flat_pool_parse_i64(raw1)
src/compiler/20.hir/generated/hir_codec.spl:8691: val dk2 = if raw3 == "N": nil else: flat_pool_parse_i64(raw3)
src/compiler/20.hir/generated/hir_codec.spl:8702: val f_next_symbol_id = if raw4 == "N": nil else: flat_pool_parse_i64(raw4)
src/compiler/20.hir/generated/hir_codec.spl:8706: val f_next_scope_id = if raw5 == "N": nil else: flat_pool_parse_i64(raw5)
src/compiler/20.hir/generated/hir_codec.spl:8714: val dk6 = if raw7 == "\\N": nil else: flat_pool_unescape(raw7)
src/compiler/20.hir/generated/hir_codec.spl:8716: val dv6 = if raw8 == "\\N": nil else: flat_pool_unescape(raw8)
src/compiler/20.hir/generated/hir_codec.spl:8725: val dk9 = if raw10 == "\\N": nil else: flat_pool_unescape(raw10)
src/compiler/20.hir/generated/hir_codec.spl:8727: val dv9 = if raw11 == "\\N": nil else: flat_pool_unescape(raw11)
src/compiler/20.hir/generated/hir_codec.spl:8736: val dk12 = if raw13 == "\\N": nil else: flat_pool_unescape(raw13)
src/compiler/20.hir/generated/hir_codec.spl:8750: val dk15 = if raw16 == "\\N": nil else: flat_pool_unescape(raw16)
src/compiler/20.hir/generated/hir_codec.spl:8764: val dk18 = if raw19 == "\\N": nil else: flat_pool_unescape(raw19)
src/compiler/20.hir/generated/hir_codec.spl:8778: val dk21 = if raw22 == "\\N": nil else: flat_pool_unescape(raw22)
src/compiler/20.hir/generated/hir_codec.spl:8792: val dk24 = if raw25 == "\\N": nil else: flat_pool_unescape(raw25)
src/compiler/20.hir/generated/hir_codec.spl:8806: val dk27 = if raw28 == "\\N": nil else: flat_pool_unescape(raw28)
src/compiler/20.hir/generated/hir_codec.spl:8820: val dk30 = if raw31 == "N": nil else: flat_pool_parse_i64(raw31)
src/compiler/20.hir/generated/hir_codec.spl:8822: val dv30 = if raw32 == "\\N": nil else: flat_pool_unescape(raw32)
src/compiler/20.hir/generated/hir_codec.spl:9238: val f_has_reset = if raw2 == "N": nil else: raw2 == "1"
src/compiler/20.hir/generated/hir_codec.spl:9250: val f_is_valid = if raw4 == "N": nil else: raw4 == "1"
src/compiler/20.hir/generated/hir_codec.spl:9258: val ev5 = if raw6 == "\\N": nil else: flat_pool_unescape(raw6)
src/compiler/20.hir/generated/hir_codec.spl:9327: val f_is_hardware = if raw0 == "N": nil else: raw0 == "1"
src/compiler/20.hir/generated/hir_codec.spl:9340: val f_has_clocked = if raw2 == "N": nil else: raw2 == "1"
src/compiler/20.hir/generated/hir_codec.spl:9356: val f_flatten_struct_output = if raw4 == "N": nil else: raw4 == "1"
src/compiler/20.hir/hir_lowering/_Expressions/block_and_asm_lowering.spl:330: val hir_output = match constraint.output_value:
src/compiler/20.hir/hir_lowering/_Expressions/expression_components.spl:907: val kind = match p.kind:
src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl:824: val kind = match expr_kind_value:
src/compiler/20.hir/hir_lowering/_Items/module_declarations_bootstrap.spl:157: val mod_name = if self.module_filename != "": Some(self.module_filename) else: nil
src/compiler/20.hir/hir_lowering/_Items/trait_impl_lowering.spl:507: val default_type = if at.has_default:
src/compiler/20.hir/hir_lowering/statements.spl:264: val elem_hir_type = match elem.kind:
src/compiler/20.hir/hir_lowering/statements.spl:378: val vr_init = match stmt_kind_value:
src/compiler/20.hir/hir_lowering/statements.spl:698: val vr_type = match stmt_kind_value:
src/compiler/20.hir/hir_lowering/statements.spl:717: var vr_sym_type = if vr_has_annotation: Some(vr_hir_type) else: nil
src/compiler/25.traits/trait_solver.spl:476: val actual = match actual_type:
src/compiler/30.types/type_infer/inference_expr_calls.spl:33: val expected_params = match resolved_callee.kind:
src/compiler/35.semantics/resolve.spl:389: val resolved_value = match block.value:
src/compiler/35.semantics/resolve.spl:441: val kind = match expr.kind:
src/compiler/35.semantics/resolve_strategies.spl:370: val type_sym_id = match receiver.kind:
src/compiler/35.semantics/unsafe.spl:197: val t = match type_:
src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:8343: val default_binding = if has_default_binding: Some(default_binding_value) else: nil
src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1971: val result = if self.current_has_vhdl_metadata:
src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:6500: val declared = if fi < field_hir_types.len(): Some(field_hir_types[fi]) else: nil
src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:6585: val declared = if fi < field_hir_types.len(): Some(field_hir_types[fi]) else: nil
src/compiler/50.mir/hir_declaration_summary_v1.spl:143: val exported = if declaration.has_export_attr: Some(declaration.export_attr) else: nil
src/compiler/50.mir/mir_data.spl:357: var fn_ = match self.current_function:
src/compiler/50.mir/mir_lowering_stmts.spl:1604: val struct_copy = if struct_is_place_iso or initializer_is_short:
src/compiler/50.mir/mir_lowering_stmts.spl:1983: val array_copy2 = if has_init: self.maybe_copy_array_value(init_local, effective_type, init_is_place) else: nil
src/compiler/60.mir_opt/mir_opt/_AutoVectorize/recipe.spl:412: val output_base = if output_base_id < 0:
src/compiler/60.mir_opt/mir_opt/_AutoVectorize/recipe.spl:570: val accumulator_dest = if accumulator_dest_id < 0:
src/compiler/60.mir_opt/mir_opt/_AutoVectorize/recipe.spl:651: val accumulator_dest = if accumulator_dest_id < 0:
src/compiler/60.mir_opt/mir_opt/_AutoVectorize/recipe.spl:655: val output_base = if output_base_id < 0:
src/compiler/60.mir_opt/mir_opt/_Inline/driver.spl:379: val callee_by_id = match self.extract_func_symbol_id(callee_op):
src/compiler/60.mir_opt/mir_opt/auto_vectorize_analysis.spl:506: val loop_info = match block.terminator:
src/compiler/60.mir_opt/optimizer_manifest.spl:715: val manifest_schema_version = match version_opt:
src/compiler/70.backend/backend/_VhdlProcess/process_codegen.spl:153: val async_reset = if domain.reset_synchrony == VhdlResetSynchrony.Async: domain.reset_signal else: nil
src/compiler/70.backend/backend/llvm_backend.spl:112: val cpu_compat = match target:
src/compiler/70.backend/backend/llvm_target.spl:249: var env_result = match detected_host_os:
src/compiler/70.backend/backend/llvm_target.spl:278: val arm_env = if os_result == "linux": Some("gnueabihf") else: env_result
src/compiler/70.backend/backend/vhdl/vhdl_call_lowering.spl:725: val callee = if self.hardware_call_uses_port_map(func, operand): self.direct_hardware_callee(operand) else: nil
src/compiler/70.backend/backend/vhdl/vhdl_call_lowering.spl:788: val callee = if self.hardware_call_uses_port_map(func, operand): self.direct_hardware_callee(operand) else: nil
src/compiler/70.backend/backend/vhdl/vhdl_call_lowering.spl:816: val callee = if self.hardware_call_uses_port_map(func, operand): self.direct_hardware_callee(operand) else: nil
src/compiler/70.backend/build_native.spl:300: val use_llvm_backend = match config.backend:
src/compiler/70.backend/linker/elf/elf_operation_bindings.spl:285: val read_operation = if source_slot >= 0: providers[source_slot].read_bytes else: nil
src/compiler/70.backend/svmg_lowering.spl:544: val target_sym = match target.kind:
src/compiler/80.driver/action_graph/artifact_owner_recovery.spl:23: var coordinator = match route.execution.coordinator:
src/compiler/80.driver/action_graph/artifact_owner_recovery.spl:50: val lease = match entry.lease:
src/compiler/80.driver/action_graph/artifact_owner_recovery.spl:72: val result_present = match current.result:
src/compiler/80.driver/action_graph/artifact_owner_recovery.spl:105: var coordinator = match route.execution.coordinator:
src/compiler/80.driver/action_graph/artifact_owner_recovery.spl:115: val current_lease = match entry.lease:
src/compiler/80.driver/action_graph/artifact_service_bridge.spl:107: val publication_supplied = match publication_lease:
src/compiler/80.driver/action_graph/grouped_execution_adapter.spl:48: val coordinator = match state.route.execution.coordinator:
src/compiler/80.driver/action_graph/grouped_execution_adapter.spl:92: val coordinator = match state.route.execution.coordinator:
src/compiler/80.driver/action_graph/grouped_execution_adapter.spl:113: val previous_attempts = match state.dispatches[index]:
src/compiler/80.driver/action_graph/grouped_execution_adapter.spl:149: val dispatch = match state.dispatches[index]:
src/compiler/80.driver/action_graph/grouped_execution_adapter.spl:191: val dispatch = match state.dispatches[index]:
src/compiler/80.driver/cache/reference/reverse_reference_atomic_generation_v2.spl:365: val candidate = match staged.candidate:
src/compiler/80.driver/cache/reference/reverse_reference_coordinator_v1.spl:1144: val old_digest = match old_reads:
src/compiler/80.driver/cache/summary/summary_store_v1.spl:307: val next = if complete: nil else: Some(_token_v1(auth, snapshot, logical_directory, index, 0, max_entries))
src/compiler/80.driver/cache/summary/summary_store_v1.spl:366: val next = if complete: nil else: Some(_token_v1(auth, snapshot, path, end, max_bytes, max_entries))
src/compiler/80.driver/driver_aot_native_output.spl:919: val raw_target = if target == "": nil else: Some(target)
src/compiler/80.driver/driver_frozen_semantic_prerequisites_v1.spl:324: val consumer = if observe_owners: Some(owner_observation) else: nil
src/compiler/80.driver/driver_hir_pipeline_lowering.spl:807: val cache_result = if archive_input == nil and parser_binding != "": hir_cache_load_in_owned_scope(transaction_cache_key, parser_binding, "", self.ctx.options.library_mode) else: nil
src/compiler/80.driver/driver_tldr_import_route_v1.spl:86: val supported = if body_contract: nil else: module_surface_tldr_stub_source_v1(rows)
src/compiler/80.driver/driver_tldr_import_route_v1.spl:90: val interface_text = if supported == nil: nil else: tldr_frozen_span_projection_v1(contents[index])
src/compiler/80.driver/smf/runtime_std_package_set.spl:387: val kind = match member.name:
src/compiler/90.tools/api_surface.spl:141: val param_text = match param.type_name:
src/compiler/90.tools/api_surface.spl:148: val ret = match sig.return_type:
src/compiler/90.tools/context_pack.spl:101: val param_text = match param.type_name:
src/compiler/90.tools/context_pack.spl:108: val ret = match sig.return_type:
src/compiler/90.tools/lint/rules/nil_outside_unsafe_rule.spl:147: val quotes = if has_quote: nil_lint_triple_quote_count(line) else: 0
src/compiler/90.tools/lint/rules/nil_outside_unsafe_rule.spl:154: val unquoted = if quotes > 0: nil_lint_blank_triple_spans(line) else: line
src/compiler/90.tools/query_api.spl:223: val symbol = match symbol_opt:
src/compiler/90.tools/query_api.spl:238: val symbol = match symbol_opt:
src/compiler/90.tools/query_api.spl:331: val symbol = match symbol_opt:
src/compiler/90.tools/query_api.spl:461: val symbol = match symbol_opt:
src/compiler/90.tools/query_api.spl:496: val symbol = match symbol_opt:
src/compiler/90.tools/query_api.spl:512: val symbol = match symbol_opt:
src/compiler/90.tools/query_api.spl:554: val symbol = match symbol_opt:
src/compiler/90.tools/query_api.spl:635: val symbol = match symbol_opt:
src/compiler/90.tools/verify/mcdc_scenario_exclusion.spl:265: val decision_text = if bound_form: _mcdc_exclusion_field(parts[1], "decision") else: nil
src/compiler/90.tools/verify/mcdc_scenario_exclusion.spl:266: val source_text = if bound_form: _mcdc_exclusion_field(parts[2], "source") else: nil
src/compiler/90.tools/verify/mcdc_scenario_exclusion.spl:267: val mask_text = if bound_form: _mcdc_exclusion_field(parts[3], "conditions") else: nil
src/compiler/90.tools/verify/mcdc_scenario_exclusion.spl:268: val count_text = if bound_form: _mcdc_exclusion_field(parts[4], "condition-count") else: nil
src/compiler/90.tools/verify/mcdc_scenario_exclusion.spl:271: val capability = if bound_form: _mcdc_exclusion_field(parts[7], "capability") else: nil
src/compiler/90.tools/verify/mcdc_scenario_exclusion.spl:313: val decision = if bound_form: _mcdc_exclusion_u64(decision_text ?? "") else: nil
src/compiler/90.tools/verify/mcdc_scenario_exclusion.spl:314: val source_digest = if bound_form: _mcdc_exclusion_u64(source_text ?? "") else: nil
src/compiler/90.tools/verify/mcdc_scenario_exclusion.spl:315: val condition_mask = if bound_form: _mcdc_exclusion_u64(mask_text ?? "") else: nil
src/compiler/90.tools/verify/mcdc_scenario_exclusion.spl:316: val condition_count = if bound_form: _mcdc_exclusion_positive_count(count_text ?? "") else: nil
src/compiler/99.loader/module_loader_compat.spl:1825: val addr = match address:
src/compiler/99.loader/module_resolver/manifest.spl:92: val source = match file_read_opt(init_path):
src/compiler/99.loader/module_resolver/resolution.spl:608: val source = match file_read_opt(file_path):
src/compiler/99.loader/module_resolver/var_resolution.spl:258: var value = match var_lookup_override(sources, g.name):
```
