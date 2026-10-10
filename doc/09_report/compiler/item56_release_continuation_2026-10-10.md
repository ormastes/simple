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
