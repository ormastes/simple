# FreeBSD Phase 2 rebuilds compiler across Cargo runtime variants

**Status:** Open; performance evidence only. Frozen source was `9fe3f03bfa9d10ae4f07b059c922e201eee17c73`. No build, test, or performance fix was run for this report.

## Observed cost

The third FreeBSD LLVM retry reused the configuration-keyed Cargo target `rust-cargo-target-b0bc74082134`, yet `rust-seed-build` recompiled `simple-runtime` and `simple-compiler`. That seed invocation completed successfully in **57m17s**. The following `rust-native-all-build` again compiled both crates. Its additional elapsed cost was not measured; seed success alone was not Phase 2 admission.

The archived compiler fingerprint JSONs show **19 changed dependency fingerprints** across the seed retry, while `simple-compiler` features stayed `default, inkwell, llvm`. The runtime dependency value changed `7973414321336279884 → 10786999531376880813`. During native-all, the runtime fingerprint returned to `7973414321336279884`; its JSON includes `native-all-provider`, and live `rustc` arguments still show the same compiler feature set. This establishes a runtime dependency variant switch and repeated compiler compilation. It does **not** establish Cargo's sole dirty reason: no Cargo fingerprint diagnostic trace was collected, and other dependencies also changed on the retry.

Evidence is retained under `/home/yoon/dev/simple-freebsd-phase2-qemu-20261003/build/freebsd/phase2-run-20261003/fingerprint-failure/`: `cache-retry-perf.md`, `cargo-fingerprints/{old-simple-compiler.json,new-simple-compiler.json,native-all-runtime.json,compiler-dependency-delta.json,native-all-compiler-procstat.txt}`. The third-retry manager log is one directory above as `final-attempt-llvm-manager.log`. These are local evidence files, not immutable CI artifacts.

## Source boundary and investigation

At frozen `9fe3`, `scripts/bootstrap/bootstrap-from-scratch.sh` runs seed and native-all as **separate** Cargo commands. Its comment explains why a single combined package build is unsafe today: Cargo feature unification can remove the seed's `rt_cli_run_file` definition. It also builds runtime last with LTO off so the authority archive contains machine-code symbol definitions. `src/compiler_rust/native_all/Cargo.toml` enables `simple-runtime/native-all-provider`; `driver/Cargo.toml` does not. These source facts agree with the observed variant switch, without proving every invalidation in the 19-dependency delta.

Investigate Cargo dirty-reason logs and per-command unit graphs on a later authorized run. Compare either a feature-compatible multi-output build **that preserves seed symbols and the LTO-off archive**, or separate per-variant Cargo targets. For separate targets, account for disk use and include the variant in the authority/cache key before reuse. Keep source, runtime, compiler, and admission identities distinct. No cached artifact should be treated as current-source proof without the existing authority checks.

Related prior analysis: [x86 authority tuple recompilation](x86_bootstrap_rust_authority_tuple_recompilation_cost_2026-08-22.md) and [general Cargo fingerprint thrashing](cargo_wasm_driver_test_thiserror_probe_fingerprint_thrash_2026-08-06.md). This report records the newly measured FreeBSD retry and its `native-all-provider` fingerprint switch.
