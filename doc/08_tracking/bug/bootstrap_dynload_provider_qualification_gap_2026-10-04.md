# Bootstrap dynload provider qualification gap

Status: OPEN. Production provider packaging/load verification is incomplete.
Canonical derived bug-database reconciliation: pending; this report alone is
not a successful database refresh or a backend qualification receipt.

## Observed boundary

The Windows bootstrap candidate derived from `07d01763de6` contains the
versioned provider ABI, runtime bridge, loader, built-in adapters and dynamic
provider fixtures. Owned-source searches for `simple_backend_plugin_v1` found
the declaration/lookup/fixture entry points, but did not locate an actual LLVM
or Cranelift production provider export/build target. This search is discovery
evidence, not proof that no generated export can exist.

The repaired Rust seed explicitly rejects dynload packaging with
`E-SEED-NATIVE-BUILD-MODE-DYNLOAD-UNSUPPORTED`. Its single output is a bootstrap
prerequisite; it cannot qualify the requested dynamic backend artifacts.

In `src/app/cli/bootstrap_focused_native_build.spl`,
`run_exact_stage3_focused_capsule` requires the `dynload` mode string, while
`run_focused_native_build_plan` validates it and calls
`aot_native_project_with_backend_fixed` without a mode/packaging argument.
Acceptance of this string is therefore insufficient evidence of a loaded
backend provider. Stage 4's explicit one-binary full-CLI route is a separate,
intentional product mode and is not itself this defect.

## Required repair and proof

Follow the selected contract in
`doc/03_plan/versioned_codegen_backend_plugin.md`; do not invent a second ABI.
Locate or implement each real provider build target, retain the checked
library/session lease, and verify descriptor, target, MIR ABI and capabilities.
Compile and run representative output through both loaded providers, including
the six compiler/interpreter/loader test binaries and their actual registries.
Bind artifact/cache receipts to provider identity and bytes. Missing providers
must remain explicit failures, without a silent built-in backend substitution.

Continue independent local bootstrap diagnosis with truthful single-artifact
lineage while this work remains open. Do not rename that result dynload, claim
provider reuse from a mode flag, or treat fixture DLL success as a production
backend qualification.
