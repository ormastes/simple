# Reviewable Cranelift 80-worker timeout retry proposal — NOT launched

Fresh user authorization is required: the prior additional Cranelift attempt was consumed and the session's bounded repair cap remains in force. Root may ask while the separate sequential LLVM attempt runs, but this script must not execute concurrently with LLVM because the user requested backend sequencing.

Exact script: C:/Users/user/.simple/runtime/propose-cranelift80-timeout1200-retry.sh --authorized-retry
The script passes syntax validation only; no retry/build/test was launched.

Inputs fixed: C:/dev/simple-windows-phase2 HEAD1ffaf797bab1b6747d4e24856ed6c1af990e178e; validated producer receipt evidence/cranelift-resume/windows-materialized-links.1ffaf797.env; MSVC LLVM23.1.1; same private build/bootstrap-cranelift80 output;80buildjobs and80testworkers; SIMPLE_NO_STUB_FALLBACK1; finite SIMPLE_NATIVE_FILE_TIMEOUT1200 plus independent whole-producer7200seconds/log128MB WindowsJobObject guard. Unique attempt logs preserve failed attempt4.

## Cache cohort analysis

Failed attempt reports compiled995,reused0,failed123;995objects physically persist. Current .bootstrap-cache-binding names phase=stage2,entry=bootstrap-main,producer_sha25690e2a8ddaa1915b384bae2c1c7da1cd4c67e3bfde5d271aa72e5cdb246ec68c3,inputs_sha25673c93cf02af45374c91394ab79504af630e39abce3ff68315f9a7813641c3e56. Inner scope is scope-37e51c496ff7919b.

Inspection: bootstrap-from-scratch.sh bootstrap_cache_context_payload hashes source/runtime/tool snapshots and bootstrap_cache_release_options_v1 plus frontend/HIR persistence policy. The Stage2 options vector does not include per-file timeout. Rust native_project/mod.rs cache_scope_segment hashes producerbytes+lane; object_cache_key hashes content,entry,backend,mangle,prefix,optlevel,CPU/SIMDtier,producer,lane; timeout is absent. Therefore a300->1200 timeout-only change SHOULD retain the existing cache cohort when frozen source/producer/runtime/tool bytes and source root remain identical.

The Stage2 invocation transcript args SHA DOES include --timeout, so new args provenance is mandatory. Canonical wrapper must derive the new transcript; never rewrite the binding stamp or reuse old admission receipt. No object hit can be claimed until next real native-build reports reused/rebuilt counts; cache-owner refusal must be reported, not bypassed. Rust seed rebuilding or shared-tool changes can alter producer/toolidentity and legitimately lose reuse. Keep all995objects even on refusal.

Acceptance: same authorized compatible incremental attempt reports actual reuse; Stage2 realcompilerproduced then strictsanity/admission/current command lineage; full CLI+runner and real backend-native interpreter/loader/compiler-core/HIR/MIR executables with positive testcounts and complete inventories. Existing explicit-entry collector filter bugs can still block qualification and require reviewed pure-Simple repair, never vacuous PASS.