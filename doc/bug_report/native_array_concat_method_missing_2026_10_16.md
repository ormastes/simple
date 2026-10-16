# Native array concat method missing (2026-10-16)

Status: pending bug database admission; source workaround UNEXECUTED.

Actual retained pure-Simple producer SHA256 a174b8e70b0a0ea4531db2ac5b8553f216590a7fbad0567cd9e40fd8e4630994, Windows LLVM23.1.3/MSVC, authority final attempt3 reports unresolved method concat at original src/compiler/80.driver/cache/package_archive_cache.spl415. Both dependencies_all and input.dependency_interface_digests are declared [text]. Evidence: external phase3-validation-20261016/authority-attempt3-failure-table.md. Source reference before workaround:61f6c6472ada76bed468ca22dc138cd9d4f728b3.

Current Pure-Simple method_calls_literals.spl3964 recognizes merge, and4392 recognizes merge/extend, not concat. The earlier comment mentioning the seed merge|concat|extend arm describes another implementation, not actual dispatch support here. Native array .concat method support remains an unfixed feature/owner gap; this patch does not implement it.

Workaround replaces only this call with dependencies_all = dependencies_all + input.dependency_interface_digests. Frontend desugar/collection_desugar.spl236.. rewrites assignment x=x+other to merge, with native lower_unresolved_array_merge emitting rt_array_extend_i64(dst,src,-1) and receiver writeback (method_calls_literals.spl1349..). The non-desugared array Add path also exists in expr_dispatch.spl4155.. as rt_array_concat. These are source-supported routes, not an execution claim.

Observational equivalence here depends on local ownership: dependencies_all is a fresh [text] accumulator inside each package iteration, not published before accumulation; input dependencies remain read-only. Append preserves dependency order and duplicates, including empty arrays. No validation or failure branch is changed. Do not generalize an in-place merge substitution to aliased receivers.

Existing coverage references (UNEXECUTED for this candidate): test/01_unit/compiler/cache/package_archive_cache_spec.spl and package_archive_manifest_roundtrip_spec.spl. No speculative fixture or compiler retry was added. Qualification must verify ordered duplicate/empty dependencies and unchanged input arrays with the actual producer. Actual concat owner repair commit is unknown; optional recover token omitted. Original source reference above is not a repair or automatic checkout instruction.
