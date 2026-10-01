# SimpleOS sealed CLI dispatch — bounded item 1 slice

Source baseline: `bf28063b843526d1212a760deaed623367a569e5`.
Owner: item1_astra_impl. Merge owner and final reviewer: root.
Status: implementation handoff; **TEST_BLOCKED**, not feature completion.

## Acceptance criteria

- AC-D1 / REQ-001,014,016: default non-debug `simple os run` consumes the
  same prepared `QemuLaunchPlanV1` as inspection, with unchanged argv order.
- AC-D2 / REQ-014,016: rejected or invalid seals never reach process execution;
  timeouts outside 1..600000 ms are rejected before spawn.
- AC-D3 / REQ-001: edits to returned command copies leave the seal unchanged.
- AC-D4: preserve the kernel-existence and filesystem-wrapper admission guards,
  serial/stderr handling, target exit classification, and existing timeout.
- AC-D5: run the focused specs, existing plan parity specs, rebuilt CLI smoke,
  docgen, lint and duplication gates on an admitted self-hosted runner.
- AC-D6: update the manual, operator guide, architecture/detail-design and
  feature/layer expert knowledge; keep blocked rows and umbrella scope active.
- AC-D7 / REQ-014,022: inspection and execution retain explicit guest memory
  and CPU overrides, including the established ten-core default; malformed or
  overflowing values cannot become a different admissible machine plan.

## TDD record

The new `test/01_unit/os/qemu_cli_dispatch_v1_spec.spl` was written before the
production dispatch functions. Its required symbol was absent at that point.
The checkout has neither `bin/release` nor `build/bootstrap/stage4`, and root's
runtime inventory has no admitted replacement. Thus no executable red result
was obtained: **RED TEST_BLOCKED**. Source absence is not a red test execution.
Implementation proceeded as authorized; green execution and docgen remain
blocked. No Rust-seed fallback or heavy bootstrap was started for this slice.

## Exact resume commands

Substitute the provenance-admitted Stage 4 executable for `<runtime>`; retain
its path, SHA-256, source identity and stdout/stderr receipts before execution.

```text
<runtime> test test/01_unit/os/qemu_cli_dispatch_v1_spec.spl --mode=interpreter
<runtime> test test/01_unit/os/qemu_cli_plan_v1_spec.spl --mode=interpreter
<runtime> test test/01_unit/os/qemu_machine_plan_v1_spec.spl --mode=interpreter
<runtime> test test/01_unit/os/qemu_lane_projection_v1_spec.spl --mode=interpreter
<runtime> test test/01_unit/os/qemu_named_nvme_plan_v1_spec.spl --mode=interpreter
<runtime> test test/01_unit/os/qemu_launch_resources_v1_spec.spl --mode=interpreter
<runtime> test test/01_unit/os/cli_spec.spl --mode=interpreter
<runtime> spipe-docgen test/01_unit/os/qemu_cli_dispatch_v1_spec.spl --output doc/06_spec --no-index
<runtime> spipe-docgen test/01_unit/os/qemu_launch_resources_v1_spec.spl --output doc/06_spec --no-index
<runtime> spipe-docgen test/01_unit/os/qemu_lane_projection_v1_spec.spl --output doc/06_spec --no-index
<runtime> spipe-docgen test/01_unit/os/qemu_named_nvme_plan_v1_spec.spl --output doc/06_spec --no-index
<runtime> spipe-docgen test/01_unit/os/cli_spec.spl --output doc/06_spec --no-index
<runtime> lint src/os/cli.spl src/os/qemu_cli_plan_v1.spl src/os/qemu_launch_resources_v1.spl src/os/port/qemu_machine_plan_v1.spl src/os/_QemuRunner/os_build_run.spl src/os/_QemuRunner/runner_targets.spl src/os/qemu_runner.spl
<runtime> duplicate-check src/os --mode token --min-lines 5
<runtime> os run --arch=x86_64 --show-plan
<runtime> os run --arch=x86_64
```

Run the acceptance agent's host-process fixture as a separate test; fixture
execution proves process dispatch, never QEMU boot or guest functionality.
Interpreter evidence must include the authenticated executed-assertion result;
a plain exit-zero file summary is insufficient. Retain generated captures and
review the manual for complete/zero-stub generation. Three fix cycles maximum;
do not repeat unchanged green checks.

## Authority and remaining scope

`qemu_cli_inspect_plan_v1` retains the plan it rendered. The new
`qemu_cli_dispatch_plan_v1` validates admission/seal and calls the shared
bounded process facade. `run_os_sealed_v1` chooses this path after the existing
artifact guards. No shell-display string is executed.

Unmigrated named scenarios, GUI/debug options, test runners, source-target runner
selection, shell/bootstrap, machine-backend replacement, image profiles,
parser/environment/loader convergence, and immutable release qualification
remain active item 1 requirements. This slice closes no umbrella REQ on its
own. Release/main application remains blocked on intensive checks.

Review found a pre-existing parity drift: the established runner had acquired
`-smp` (ten cores by default) and explicit memory/CPU overrides while the sealed
projection had not. The resource owner is now `os.qemu_launch_resources_v1`,
re-exported by the legacy runner. Both planners use bounded resource parsing;
lane constructors accept an optional sixth `cpu_count` argument. Default-six
and named-lane parity specs were updated. This source review is not executed
parity evidence. The adjacent missing CLI import/export of `qemu_default_arch`
is also repaired, with a facade regression in `cli_spec.spl`.

Static checks already observed: owned diff whitespace clean, no executable
`*_spec.spl` under `doc/06_spec`, and working/staged direct-env guards PASS.
They do not replace any blocked runtime gate or permit promotion.

## Named dispatch continuation (2026-10-01)

Owner: item1_continue; merge owner/final reviewer: root. The four named shapes
already represented by the inspection authority now select
`run_scenario_sealed_v1` from the CLI. The runner retains the prepared plan and
dispatches it through `qemu_cli_dispatch_plan_v1`, preserving media preparation,
filesystem admission, timeout, serial reporting and exit classification. An
unsupported direct sealed-run request rejects before media preparation; any
preparation/dispatch rejection on a supported shape has no legacy fallback.
The x86_32 executable policy remains fail closed; this change does not assert
that host resolution or guest execution succeeds.

New acceptance criteria: AC-N1 selects all four represented shapes through the
existing authority; AC-N2 rejects an unrepresented GUI sealed run; AC-N3
executes each admitted named lane through its inspected argv with existing
exit/timeout behavior. The focused spec covers AC-N1/N2. Existing named parity
and host-process acceptance plus rebuilt CLI fixtures are required for AC-N3.

The spec was authored before its two production symbols. Runtime RED/GREEN
and generated-manual review remain **TEST_BLOCKED** because the shared tree
has no admitted self-hosted runner. No source-only PASS, seed execution,
commit, release or main admission is claimed.

Additional resume commands (once only per unchanged acceptance criterion):

```text
<runtime> test test/01_unit/os/qemu_named_dispatch_v1_spec.spl --mode=interpreter
<runtime> spipe-docgen test/01_unit/os/qemu_named_dispatch_v1_spec.spl --output doc/06_spec --no-index
<runtime> sspec-maintain scan test/01_unit/os/qemu_named_dispatch_v1_spec.spl
```

Run rebuilt CLI inspection/run fixtures for the four supported shapes on
qualified Linux/Windows hosts, retaining exact argv and process receipts.
Host-process fixture execution remains distinct from guest boot evidence.

## Real CLI route and compiler-selection acceptance

`test/03_system/os/feature/qemu_sealed_cli_route_acceptance_spec.spl` now
specifies actual full-CLI inspection and execution for the default x86_64
route and all four represented named routes. It requires canonical full-CLI
provenance, real kernels/media, production artifact admission and real QEMU
host admission. Process results and guest serial checks remain distinct;
missing prerequisites fail `MissingEvidence`. This closes the authored-test
gap in AC-N3, not its runtime evidence gap. Existing host-fixture tests remain
the separate ordered-child-argv observation.

Writing this gate exposed a production seed-precedence bug at the OS compiler
selector. The isolated fix reuses the existing compiler capability contract
from clean C-tree commit `ca713ba9e0c7b5f5ee0858550a64d6c38244409a` and delegates
provenance/discovery to canonical deployed-runtime and Stage4 owners. It
preserves explicit `SIMPLE_BINARY`/`SIMPLE_BIN` precedence, refuses invalid
explicit candidates and pins the native-build process. Installed seeds need
not be removed. See
`doc/08_tracking/bug/simpleos_explicit_compiler_seed_precedence_2026-10-01.md`.

New focused selection tests were authored before the new admission facade.
Existing backend canary unit scenarios preceded the restoration of their
missing production helpers. All runtime RED/GREEN, host lanes and docgen
remain **TEST_BLOCKED**; source inspection is not executed evidence.

```text
<runtime> test test/01_unit/os/qemu_compiler_selection_v1_spec.spl --mode=interpreter
<runtime> test test/01_unit/os/simpleos_compiler_admission_spec.spl --mode=interpreter
<runtime> test test/03_system/os/feature/qemu_sealed_cli_route_acceptance_spec.spl --mode=interpreter
<runtime> spipe-docgen test/01_unit/os/qemu_compiler_selection_v1_spec.spl --output doc/06_spec --no-index
<runtime> spipe-docgen test/03_system/os/feature/qemu_sealed_cli_route_acceptance_spec.spl --output doc/06_spec --no-index
<runtime> sspec-maintain scan test/01_unit/os/qemu_compiler_selection_v1_spec.spl
<runtime> sspec-maintain scan test/03_system/os/feature/qemu_sealed_cli_route_acceptance_spec.spl
```
