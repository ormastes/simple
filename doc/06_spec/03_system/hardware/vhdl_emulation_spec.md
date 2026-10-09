# VHDL emulation with owned GHDL workspaces

Executable owner: `test/03_system/hardware/vhdl_emulation_spec.spl`.
One executable suite, four scenarios. The duplicate legacy path was retired.

## Requirements

A POSIX host with real GHDL on PATH. The explicit suite fails if GHDL is
missing. This is simulation evidence, not a source-text contract. The owner
is `src/lib/nogc_sync_mut/io/vhdl_sffi.spl`; both app wrappers export it.

## Scenarios

1. Analyze and elaborate the same entity as inverter and buffer in separate
   private workspaces. Simulate both and require distinct completion markers
   after actual signal assertions.
2. Analyze malformed VHDL and require a positive nonzero exit and diagnostics.
3. Analyze and elaborate valid VHDL with a deliberately wrong signal oracle.
   Require simulation failure, its assertion diagnostic, and no success marker.
4. Use the legacy analyze/elaborate/run workflow and require a real inverter
   simulation, followed by explicit default-workspace cleanup.

Fixtures: `test/fixtures/vhdl/owned_workspace/*.vhd`.

## Legacy reconciliation

On 2026-10-08, the repaired legacy `test/system/vhdl_emulation_spec.spl`
and canonical owner were byte-identical (SHA-256
`1228d6b16bcd0b9662604e91310b295e6fe922759b9754290f1e0710af93a1ab`). Both contained the same four simulation scenarios,
imports, setup and cleanup. Retiring the legacy executable therefore removes
four duplicate executions without losing distinct behavior. Use the canonical
path above for focused runs.

Reference audit found the manual, one stale import-resolution baseline row,
and historical generated Windows summaries. The manual and baseline are updated.
The historical summaries still describe an old 12-pass run; they are preserved
as historical artifacts and do not qualify these four new scenarios.

## Lifecycle and limitations

Explicit workspace callers share one directory across all phases and remove
it after completion. Each subprocess enters that directory without changing
its parent's working directory, isolating both GHDL's library and native backend
outputs. Relative source paths resolve in the original caller directory.
The legacy API is sequential and owns one private workspace per process until
`ghdl_close_default_workspace`. Concurrent workflows use explicit contexts.
Failure may retain a private directory for diagnosis. This patch does not alter
Yosys or the higher-level plugin's waveform workflow.

## Evidence

Focused execution PASS on FreeBSD ARM64, 2026-10-08: four declared/executed
scenarios, four passed, zero failed/skipped/dropped; 790 ms runner duration.
Actual GHDL 6.0.0 (LLVM 19.1.7 backend) ran through the Simple wrapper, including
both deliberate-negative cases. Guard exit 0, quiescent 1, peak RSS 576216 KiB
under the 5859375 KiB compiler cap and 180-second outer deadline.

Tested source: `e23da7a417f3c970467db463d40af20bc764110a` plus reviewed patch
`ec7709814f76f53c2080ef1f000db80a306fbb09110eff4c8ef8d3b69e827a9d`.
Producer: separately admitted Phase1 seed from `e934d53a7e7`, SHA-256
`daadf4c854c0ef8d5a0d9cf33379c3dd28a1f7ba7c93a6b915c77973943fb721`.
GHDL SHA-256: `24feb6d8ed22fcd02b9de83210c0308f662ecd6c53642154ba0d7414b123008f`.
Seed and GHDL hashes remained unchanged after the test. The approved package
transaction installed ten new packages, with no upgrades/removals.

Retained evidence: `build/vhdl-owned/runtime-evidence.json`, `cycle1.log`,
`cycle1.rss.env`, `pkg-install.log`, `pkg-postinstall.log`, and `STATUS.md` in
the isolated `simple-phase1-vhdl-owned-20261008` worktree. The runtime receipt
binds the source/test/fixture and log hashes; source and producer are separate.

Limits: duplicate-signature and runtime-family warnings remain in the observed
mixed closure. The SFFI backlog audit has a pre-existing failure, confirmed by
baseline differential; this focused PASS does not turn that audit green.
The `@cover 80%` declaration is not measured coverage. This is not whole-suite,
pure-Simple Phase2, production, or release qualification. No passing test rerun
was needed for this evidence-only documentation update.
