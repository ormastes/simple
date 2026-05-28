# SimpleOS Driver and Platform Guide Index

## Purpose

This index connects the recent SimpleOS driver, desktop, and game-platform work to the plans and tests that maintainers should use.

## Entry Points

| Area | Design/plan | Primary tests |
| --- | --- | --- |
| x86_64 desktop driver completion | `doc/03_plan/sys_test/x86_64_desktop_driver_completion.md` | `test/system/simpleos/driver_acceleration_perf_spec.spl`, `test/system/simpleos/display_dma_contract_spec.spl` |
| Driver safety and performance boundary | `doc/05_design/hardware_driver_safety_and_performance_2026-04-15.md`, `doc/05_design/driver_api_heavy_path.md` | driver sys-tests and perf tests under `test/system` and `test/perf` |
| SimpleOS production backlog | `doc/plans/simple_os_production_remaining_goal_2026-05-13.md` | `test/integration/simpleos_self_host_spec.spl`, OS boot/sys tests |
| Game compatibility platform | SimpleOS production plan and Wine/process-session specs | Wine/process/session tests under `test/lib/common` and `test/os/kernel/wine` |
| Scheduler process isolation | `doc/05_design/scheduler_process_isolation.md`, `doc/05_design/scheduler_process_isolation_duplication_analysis.md` | `test/unit/os/scheduler_isolation_spec.spl` |

## Verification Commands

Run focused checks before broad OS checks:

```bash
bin/simple check src/os/kernel src/os/services src/os/lib
bin/simple test test/system/simpleos/driver_acceleration_perf_spec.spl --mode=interpreter --clean
bin/simple test test/system/simpleos/display_dma_contract_spec.spl --mode=interpreter --clean
bin/simple test test/unit/os/scheduler_isolation_spec.spl --mode=interpreter --clean
```

For compatibility-platform work, select the specific Wine/process-session tests touched by the change:

```bash
bin/simple test test/lib/common/wine_process_session_cpu_preflight_spec.spl --mode=interpreter --clean
bin/simple test test/os/kernel/wine/kernel_thread_primitives_spec.spl --mode=interpreter --clean
```

## Documentation Rules

Each new SimpleOS driver/platform feature must document:

- the kernel or user-space ownership boundary,
- the hardware dependency, if any,
- the authoritative test command,
- known unsupported devices or emulation-only paths,
- and whether the code is policy, mechanism, or compatibility glue.

Keep detailed architecture in design docs. Keep this guide as the routing index.
