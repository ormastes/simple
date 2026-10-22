# Cache codec and TLD MIR lowering gaps

Status: OPEN. Canonical ID: `native_cache_contract_mir_lowering_gaps_2026_10_11`. GitHub: https://github.com/ormastes/simple/issues/3054.

C36 a9b actual canonical-cache-codec and physical-tld entries reach MIR then fail on Array.copy receiver, wrongly retained record operator owner and section iteration collection owner. Ranges are separately tracked by #3014; no root compiler repair proved.

Typed copies retain sort isolation; scalar equality helpers and explicitly typed indexed section iteration retain declared owners. Reviewed source only; all changed native/spec/runtime results PENDING.

Source `eaeb016d40994b5f4dae73d26f48fcad0c8bd661` maps to local integration `680ac1c8d07f091d364de13f1c26fefe11d7a78f`; no release landing claimed. Source base is frozen C37c9cb8d6ac95ab64c95dc74c46772d2c60002271e.

Evidence: `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/manual-c34-failure-representatives-c36/canonical-cache-codec/result.json` and sibling `physical-tld/result.json`, historical C36producer5315/sourcea9b. Existing #3014 range bug also covers the checked byte/dependency copy helpers, whose callers validate nonnegative half-open bounds. They are not general slicing implementations.

Removal: Repair native array copy dispatch and aggregate-field scalar/iterator owner propagation; restore original copy/field comparisons/section loops only after both actual entries pass HIR/MIR/object and byte/bounds/sorting/order regressions execute. Keep OPEN; no automatic retirement/admission. For #3014, original range forms and malformed/UTF8/page/section bounds also need qualified native controls. Neither issue is closed by this workaround.

Regressions: `test/01_unit/compiler/cache/cache_contract_codec_spec.spl` and `test/01_unit/compiler/cache/package_init_tld_physical_binding_v1_spec.spl`; unexecuted.
