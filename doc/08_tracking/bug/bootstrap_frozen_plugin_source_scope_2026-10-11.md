# BUG-BOOTSTRAP-FROZEN-PLUGIN-SCOPE-20261011

Status: OPEN — constructor correction authored; newly built producer and native
bootstrap qualification pending. This is distinct from SCV scope bug #3094.

GitHub: https://github.com/ormastes/simple/issues/3100

Canonical Stage2 from source `352182ec6bc36359207da9fe99bed559c2caf8de` passed
canonical CUDA source admission, then exited 1 during HIR. Its two diagnostics:

- `plugins.backend_registry.full_static_backend_registry`, imported by
  `src/app/cli/bootstrap_main.spl`.
- `plugins.backend_vhdl.driver.driver_aot_vhdl_output`, imported by
  `src/compiler/80.driver/driver_aot_pipeline.spl`.

The actual source snapshot was
`scv-revision-v1-5fa830fdc896be8152d2153a2653127f5548cca1b23c5ad94843809bafd3f571`.
Both source files exist in the checkout, but neither exists in that snapshot or
its `SCV_COMPILE_INVENTORY`. The selected `cuda_static` composition file is
present in both, so disabling CUDA or weakening admission does not address this
failure.

Evidence under `/home/yoon/dev/simple-release-phase3-20261011`:

- `build/bootstrap-parent-reuse-3521/logs/aarch64-unknown-linux-gnu/stage2-native-build.log`
- `build/bootstrap-parent-reuse-3521/stage3/aarch64-unknown-linux-gnu/stage2-command.transcript`

The canonical constructor already declares
`plugin_policy_source_root=${repo_root}/src/plugins`. Three of its seven native
source vectors include it; the four K1 Stage2/Stage3 transcript and execution
vectors omit it. Explicit source roots determine the frozen snapshot selection,
so the compiler cannot resolve those imports from the admitted snapshot.

Repair: include that same canonical plugin root after the selected CUDA and
compiler/app/lib roots in the four affected vectors. Preserve existing K1 and
CUDA precedence and all manifest/platform policy selection. This admits the
plugin source family through normal `src` inventory records; dependency closure
still chooses imported modules. It does not make arbitrary build roots trusted,
force CUDA off, or select the default static CUDA owner ahead of an overlay.

Source-only controls validate all seven actual source vectors and reject missing
plugin roots or precedence inversion. A real Git/SCV snapshot fixture for all
three CUDA modes is authored but UNEXECUTED. The recorded native failure is not
claimed fixed until a new changed-input bootstrap attempt qualifies it.
