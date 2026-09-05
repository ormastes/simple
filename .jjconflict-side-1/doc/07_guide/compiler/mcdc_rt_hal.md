# MC/DC and RT/HAL Evidence Guide

This guide describes the operational evidence boundary for MC/DC instrumentation
and `@rt(hal)` comparison. It does not turn source inspection or a generated
manual into a passing runtime claim.

## MC/DC modes

Use one explicit mode per compilation: static off (the default), static on, or
dynamically loaded. Static off must lower without probe state, calls, allocation,
or dispatch. Static on records through bounded owner-local storage. Dynamic mode
keeps its inactive path dormant; activation and unload are cold lifecycle work.
Preserve evaluation order, evaluation count, and short-circuit behavior in every
mode.

Normal and stricter coverage gates require exact covered/required equality after
only narrow, stable, reviewed exclusions. A rounded percentage, a missing pair,
or a blocked environment is never coverage.

## RT and provider boundary

`@rt(hal)` is mission-critical by default unless a declaration explicitly selects
a different assurance profile. A critical transitive closure rejects unproved
allocation, blocking, recursion, dispatch, logging, synchronization, and loader
work. Migration diagnostics stage the implicit default from warning to error.

Pure Simple owns the result and any irreversible effect. C and Rust providers
receive the canonical bounded request or replay trace and compare typed output;
they do not execute a second physical effect. Provider admission is typed,
bounded, and identity-pinned. The compiler-owned V3 staged path seals a
canonical full-plan identity before a live host may be prepared; public V2 and
direct V3 setup are quarantined rather than silently falling back. An
unavailable provider is typed unsupported or blocked evidence, never a parity
pass. See [RT/HAL typed-exit protocol](../../05_design/rt_hal_typed_exit_protocol.md).

## Environment access and evidence

Environment work is a validated `EnvAccessPlan` executed only by the app I/O
host. The closed vocabulary has 24 instruction kinds: environment/host/file/tool
reads; hardware probe; socket connect/send/receive/close; device read/write;
MMIO read/write; IRQ enable/wait/acknowledge/disable; DMA map/sync-for-device/
sync-for-cpu/submit/wait/unmap; and clock read. Physical kinds require a sealed
adapter. See [Environment Access Plans](../language/environment_access_plans.md)
for physical-adapter ownership, bounds, replay, and blocked receipt format.

Run the following suites with the pure-Simple runtime. Keep each criterion to
one acceptance execution and retain the emitted receipt/report with the revision:

```text
bin/simple test test/03_system/coverage/mcdc_modes_and_semantics_spec.spl --mode=interpreter
bin/simple test test/03_system/coverage/mcdc_enforcement_and_exclusions_spec.spl --mode=interpreter
bin/simple test test/03_system/coverage/mcdc_parallel_recording_spec.spl --mode=interpreter
bin/simple test test/03_system/runtime/rt_hal_provider_differential_spec.spl --mode=interpreter
bin/simple test test/03_system/runtime/rt_hal_external_provider_protocol_spec.spl --mode=interpreter
bin/simple test test/03_system/runtime/rt_hal_environment_receipt_spec.spl --mode=interpreter
bin/simple test test/03_system/runtime/rt_criticality_hardening_spec.spl --mode=interpreter
```

For performance and memory, use the same fixture for static-off, static-on, and
dynamic states; report timing, peak RSS, allocation/copy counters, checksums,
and optimizer receipts in
`doc/09_report/mcdc_rt_hal_perf_report_template.md`. Algorithmic reasoning is
useful review evidence but is not measured latency or memory proof.

## Traceability

The primary traceability matrix and excluded-target policy are maintained in
`doc/03_plan/sys_test/mcdc_rt_hal_hardening.md`. Executable SSpec belongs under
`test/`; its generated/manual mirror belongs under `doc/06_spec/`. A manual is
current only after SPipe/docgen reports no stubs for the affected spec. The
manuals in this lane are explicitly marked unexecuted until that self-hosted
runtime is restored.
