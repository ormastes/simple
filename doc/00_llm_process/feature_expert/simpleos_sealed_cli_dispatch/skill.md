# Feature expert: SimpleOS sealed CLI dispatch

The default non-debug CLI lane enters `run_os_sealed_v1` in
`src/os/_QemuRunner/os_build_run.spl`. Keep kernel/file-wrapper admission before
preparation. `src/os/qemu_cli_plan_v1.spl` owns preparation, retains the sealed
plan in `QemuCliInspectOutcomeV1`, and dispatches exact argv through the bounded
process facade. Never execute inspection display strings.

Contract tests: `test/01_unit/os/qemu_cli_dispatch_v1_spec.spl`.
Resume/evidence authority: `doc/03_plan/sys_test/simpleos_sealed_cli_dispatch.md`.
Operator guide: `doc/07_guide/platform/simpleos/sealed_cli_dispatch.md`.

State is TEST_BLOCKED pending admitted self-hosted execution, docgen and live
CLI evidence. No native-host/guest/release evidence was produced. Unmigrated named/GUI
lanes and all broader platform requirements remain active; preserve the
selected `simple_platform_unification` requirements. Root owns final review
and release/main admission. Do not substitute a Rust seed for these gates.

Guest memory/CPU overrides are owned by `os.qemu_launch_resources_v1`, also
re-exported by the legacy runner. Sealed lane constructors take an optional
sixth CPU-count argument and parity argv includes `-smp`. Keep the default-six
and named-lane parity fixtures synchronized; the previous projection omitted
SMP and mishandled GiB fixture parsing. The CLI also explicitly imports the
runner's re-exported `qemu_default_arch` helper.

The four shapes selected by `qemu_cli_named_lane_supported_v1` now enter
`run_scenario_sealed_v1` through the CLI. `scenario_sealed_run_supported_v1`
delegates to that existing authority; do not maintain another lane list in
production. Existing media/filesystem admission remains ahead of preparation.
The execution owner retains the plan until exact dispatch and preserves
scenario timeout/exit semantics. Other named run/headless/test callers remain
legacy. `qemu_named_dispatch_v1_spec.spl` covers the selection boundary and
unsupported sealed-run refusal; executable evidence remains blocked.
