# native-build object cache never hits across runs: pid-valued env in scope identity

Symptom: 204-module probe, two unchanged reruns, identical args/env: 0 hits (90/90 checked
modules mismatched), and each run created a new scope dir (native-after6 holds three `s...` dirs).

Cause: `native_build_module_environment_snapshot_fingerprint_v1`
(src/compiler/80.driver/cache/native_build_environment_identity.spl, projection loop ~L205-250)
folds every present `SIMPLE_*` var. The CLI sets `SIMPLE_ICE_DIR`
(`ice_boundary_claim_run`, driver_ice_boundary.spl:207, value `<pid>_<hash>`) and
`SIMPLE_NATIVE_BUILD_WARM_CLOSURE_CANDIDATE` (native_build_warm_receipt.spl:764,
`candidate-<pid>.receipt`) per run. The digest feeds `options_identity` and
`driver_native_build_cache_scope` (driver_aot_native_output.spl:~2200), so the scope
directory and every witness changed per pid. The library path
(`bootstrap_library_environment_snapshot_v1`) has the same flaw.

Fix: both names are excluded from the module projection and from the library delivery list.
Both only select evidence/candidate file locations; no codegen effect. The complete capture
still records them. Other pid-varying inputs in the identity (checked): MIR shard/queue and
profile/snapshot sinks were already excluded; TMPDIR/TMP/TEMP are nonsemantic and not folded
(only SEMANTIC list non-SIMPLE names are); HOME is not captured. Remaining SIMPLE_* values
set by the CLI are constants.

Spec: test/01_unit/compiler/driver/native_module_environment_projection_spec.spl
(UNEXECUTED). Not verified end to end: needs a redeployed producer and a rerun probe.
