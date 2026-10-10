# Items 5 and 6 release continuation (2026-10-10)

Status: IN PROGRESS. No full Item 5/6 verification PASS or release landing.

## Compiler admission repair

At work branch `f25b700f050`, a production source-closure helper call through a function value was replaced with a direct call. A core from the prior rejected candidate showed PC 0 at the helper's `blr x7` and `x7=0`. See [the focused callback bug](../../08_tracking/bug/source_root_resolution_callback_native_null_2026-10-10.md).

The first post-fix bootstrap stopped at its Stage 2 cache binding because source identity had changed. A second run explicitly invalidated that incompatible Stage 2 cache, rebuilt 1,222 modules, passed the previously crashing module-path-naming sanity, and published pure-Simple Stage 2 parent sanity/provenance receipts. Candidate SHA-256: `5f03d7ca69b935133656c07a0eb0154b8095a73609d25669005e2c62e5d09032`. The outer bootstrap stopped before compiler tests: delegated seed spec rows require four explicit MC/DC waiver fields. No waiver was invented. Evidence: `build/mini_builds/item56_stage2_fallback_fix_invalidate_20261010/bootstrap.log`, `.simple/storage/build/bootstrap/stage2/aarch64-unknown-linux-gnu/stage2-sanity.receipt`, and `stage2-provenance.receipt`.

## Item 6 focused action-key probe

Three bounded attempts used that exact Stage 2 candidate and `SIMPLE_NO_STUB_FALLBACK=1`:
1. Cranelift with compiler and full library source roots reached AOT; imported global declarations in process-observation modules were rejected, and the worker aborted (exit 122).
2. Cranelift with only compiler source root could not resolve required `std.nogc_sync_mut.sffi.fs` from the frozen source inventory (exit 1).
3. LLVM with compiler and full library roots emitted invalid IR in `package_module_index_validate_v1`: `%l633 = add ptr 3, 0` at the retained `message.module.ll` line 8147 (exit 1).

Logs are under `build/mini_builds/item6_semantic_action_probe_{current,closure,llvm}_20261010/`. These failures do not show the semantic v2 key is wrong; they prevent the native fixture from executing. This session's three probe verify/fix cycles are exhausted. Production cold/warm behavior and time/RSS still lack evidence.

## Item 5 closure audit

The kernel closure manifest now classifies five bootstrap admission fixture files as P-static in both projections. The checker self-test passed (11 fixtures). The actual checker moved from five unclassified files to zero unclassified out of 2,237, then reported 3 K0-to-P, 7 K1-to-P, and 11 kernel-to-app/OS import violations. Those dependency violations and all optional-provider runtime, matched-size, startup/RSS, and cutover gates remain open.

Both direct environment access audit modes passed after the compiler change. This is narrower than release verification. The work branch remains isolated and unlanded.

## Full-CLI verification availability

The required core runtime smoke was attempted once with the Stage 2 candidate. It exited 1 at its first `-c` case: `error: unknown command '-c'`. The candidate help lists only `compile` and `native-build`; it is a bootstrap compiler, so this result is a tool-scope mismatch, not a language runtime failure. Full compiler/lib/MCP/LSP checks and MCP native smoke need a deployed full CLI and servers. GitHub authentication was absent when checked, so the branch remains local only.

## 2026-10-10 declaration-only and native publication follow-up

Commit `ddb1507c8eb` adds a guarded objectless native path for empty and plain struct-only source units. The rebuilt pure-Simple Stage 2 binary (SHA-256 `c535be7321e80a4857413fa1c690008b3172b157e87eac8a860edd98c6772082`) compiled 1,222 units and passed parent sanity/provenance. The outer bootstrap again stopped before compiler tests because delegated MC/DC-off rows have no explicit waiver.

The focused LLVM CAS fixture now builds and links 40 objects; the earlier `MIR module has no functions or static data` failure is cleared. Its executable initially rejected omitted trailing constructor defaults (`legacy-variant-unexpected`). Explicit fields made validation `ok`, but initial publication still exits 1 because native `sha256_text` returns the empty-input digest for nonempty strings and the 260-byte index. The publisher leaves `CURRENT` absent. See [the bug](../../08_tracking/bug/package_index_native_publication_blockers_2026-10-10.md). Three focused verify/fix cycles are exhausted for this session; no CAS PASS, production performance cohort, or release PASS is claimed. Direct-env working/staged audits passed, and `doc/06_spec` has zero `*_spec.spl` files.

## 2026-10-10 VHDL ownership projection alignment

The `_VhdlProcess/**` implementation directory was already P-static in the kernel-plugin-fabric `rules:` projection, but the closure checker's `entries:` projection fell through to K1. Both files implement VHDL backend methods and directly import the VHDL plugin. Aligning the first projection to P_STATIC changed the authoritative closure census from 3 K0-to-P, 7 K1-to-P, and 11 kernel-to-app/OS violations to 3, 0, and 11 respectively, with 2,237 classified and zero unclassified. Baseline and post-change logs: `build/mini_builds/item5_kernel_closure_{baseline,vhdl_aligned}_20261010.log`. The remaining 14 violations and all dynamic loading, size, startup, RSS, and release gates stay open.

## 2026-10-10 canonical loader generation-state cleanup

The canonical `moduleloader_replace_live` path no longer constructs temporary `os.smf.smf_generation` state. `CandidateMapping` was created false and unconditionally marked relocation/import-valid immediately after the real `moduleloader_apply_relocations` success; its readiness failure was unreachable. `LifecycleManager` mutations were local and never retained, and the retired `GenerationState` result was unused. The code now uses the existing relocation result and resource lifecycle as its authority and preserves the former verbose generation text. This removes the canonical loader's direct OS generation import without introducing a new runtime owner.

The kernel closure checker changed from 3 K0-to-P, 0 K1-to-P, 11 kernel-to-app/OS to 3, 0, 10 (2,237 classified, zero unclassified). Evidence: `build/mini_builds/item5_kernel_closure_loader_state_20261010.log`. The existing `test/01_unit/compiler/loader/loader_canonical_ownership_spec.spl` expects the canonical module to omit that import and the discarded manager construction; executable test evidence remains pending a full CLI.

### Stage 2 evidence for loader cleanup

The no-stub Stage 2 rebuild from commit `7452acac2da` compiled 1,222 source units with zero failed, then passed parent sanity and pure-Simple provenance. Its source snapshot is `99e33cc5fef1f8b5119a26fb0b8dbca2fa7bf5a260e0a80edda47c4f0360361e`; the resulting bootstrap executable SHA-256 remains `c535be7321e80a4857413fa1c690008b3172b157e87eac8a860edd98c6772082`. The unchanged executable hash means this does not prove the edited hot-reload branch executed. The outer compiler-test matrix again stopped before tests at the missing explicit MC/DC-off delegation waiver. Log: `build/mini_builds/item5_loader_state_stage2_20261010/build.log`; admission receipts remain under `.simple/storage/build/bootstrap/stage2/aarch64-unknown-linux-gnu/`. Full loader runtime, optional-provider, and time/RSS qualification remain open.

## 2026-10-10 native text conversion isolation

A six-module LLVM/core-C native probe isolated the Item 6 empty SHA result before hashing: `"producer".len() == 8` and its first byte is 112, but `text_to_utf8_bytes("producer").len() == 0`. Both byte SHA paths produce the correct nonempty digest. A guarded fallback in the sanctioned `std.common.text_bytes` facade copies `byte_at` into one sized byte array only on this invalid runtime result. The post-fix native probe exits 0 and prints `PASS sha256_text_native_probe` for ASCII, UTF-8, alias conversion, pure/fast byte hashes, and text hash. See [the runtime ABI bug](../../08_tracking/bug/native_text_to_bytes_empty_2026-10-10.md).

This proves the narrow conversion and hash path. It does not prove the full CAS publisher, its persistence invariants, a full compile cohort, or the fallback's time/RSS cost. The underlying native ABI defect remains open.

## 2026-10-10 bounded Item 5/6 continuation

The imported enum-payload owner alias now clears the earlier 42 HIR errors across the 1009-module JIT probe. Its native build fails later at monomorphization with 63 unresolved generic calls after about 616 seconds; no JIT, size, startup, or RSS verdict follows. Item 6's second-generation CAS fixture advances CURRENT but fails native readback; the warm-revert recovery source passes HIR/mono in isolation and fails MIR before execution. The structural index bytes and exact receipts are in the Item 5 HIR and Item 6 native publication/warm inventory bug notes. These are bounded defect repairs, not release qualification. The paired normalized sum for time and memory cannot be evaluated without executable baseline and candidate cohorts; collect both once runtime gates pass.

## 2026-10-11 native CAS readback

The Item 6 second-generation native CAS scenario now passes using bounded byte decimal parsing. The parser also rejects padded, oversized, and nonnumeric frame lengths in the same no-stub native fixture. The repair reduces repeated substring copying, but no matched p95/RSS cohort is available; the joint normalized-sum verdict remains unclaimed. Full entrypoint and warm recovery gates are still open.

## 2026-10-11 imported generic current-source probe

The isolated native HIR probe imports the edited monomorphizer and asserts exact owner-qualified generic call names. Its first build exposed a stale `Module` import in the unit harness; the parser owner now exports `ParserModule`. Its second build reached 300/300 HIR modules but refused seven generic transient-owner promotions on indexed inner values. Exact declared type arguments on those seven calls let the third build reach monomorphization with 9 generic functions, 60 call sites, 38 specializations, and zero unresolved calls. The pure-Simple Stage 2 native-build worker then terminated with signal 11 in MIR lowering before link or probe execution. The three-cycle cap is exhausted; no native Item 5 or paired size/startup/RSS claim follows. See [the worker crash record](../../08_tracking/bug/item5_mono_hir_probe_mir_worker_crash_2026-10-11.md).

## 2026-10-11 warm recovery graph handoff

Source review identified that the existing warm-drift cold inventory retry did not authorize entrypoint graph reconstruction: admission could still refuse the stale complete graph, and the driver ignored rebuild-pending state. A successful bounded retry now sets an internal authority bit; admission selects the existing cold-rebuild-pending transition without replacing CURRENT, and the driver consumes that pending marker via SOSIX. Regression fixture assertions distinguish recovery from normal warm and explicit cold authority. Native recovery and paired time/RSS remain unverified; see [the recovery record](../../08_tracking/bug/scv_warm_inventory_misses_revert_to_head_2026-10-10.md).

## 2026-10-11 cleanup and focused recovery evidence

The isolated task worktree remained clean at entry. Reproducible bootstrap temporary Rust toolchain bytes, old Cargo target, SCV snapshots, mini-build outputs, and phase snapshots were removed after checking no task process used them. The older /tmp/simple-release-implementation-20261010 checkout remains because it owns the active worktree Git metadata. A saved core from the earlier callback crash was removed after its backtrace matched the existing bug record. Free disk space rose from 6.33 GiB to 16.75 GiB during cleanup, including concurrent host changes.

One focused Stage 2 compile --format=smf of the warm-revert fixture passed HIR and monomorphization for 135 modules but failed in MIR on reached library code before output. The existing fixture is now asserted from the source-authority unit spec. Full native recovery, production graph rebuild, and paired time/RSS remain unverified; no release landing follows.

## 2026-10-11 refreshed Stage 2 and dynlib symbol boundary

With disk preflight at 25 GiB, the Cranelift Stage 2 trust-root lane rebuilt 1,222 modules after explicit stage2 cache invalidation. The pure-Simple candidate SHA-256 e0e5a6cd522d6ee86b0dbb8e7cdd88cad21b3daa39d18b65b2ce163867e0eb06 has sanity and provenance receipts. The outer bootstrap stopped at compiler-test delegation because MC/DC-off rows lack an explicit waiver; no full verification PASS follows.

A four-module Item 5 native probe compiled and linked through LLVM codegen up to lld. Imported free generic symbols no longer appear bare, but the dynlib lifetime object references unmaterialized Mutex.lock and Mutex.try_lock methods. A qualified-display-first monomorphizer lookup and symbol-collision unit regression are now source candidates; this exact repair is unverified until a new compiler is built. Cranelift codegen rejected the same two dynlib owner modules before link. Full optional-provider, size/startup/RSS, and Item 6 production gates remain open.

## 2026-10-11 linker pack provider entry classification

The shared linker-pack ABI entry source exports the provider's C query and invoke functions and has no compiler source importer. Both kernel closure projections now classify only this entry source as P-dyn, leaving shared linker contracts in K1. The closure checker moved from 3 K0-to-P, 0 K1-to-P, 9 kernel-to-app/OS violations to 3, 0, 8 with 2,238 classified and zero unclassified. This is a source partition correction; a rebuilt binary/link map and provider load test are still required before claiming a size or loading gain. The remaining violations and all Item 5 size/startup/RSS gates remain open.
