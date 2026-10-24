# Phase 2 full-CLI HIR fails on missing MMIO test owner

Date: 2026-10-24
Status: source repair; whole bootstrap and hardware validation remain pending.

The full-CLI build from the frozen aarch64 Phase 2 compiler (SHA-256
`e6e0c55151bab997348a7829fc911ff62839a112476a71d5de4dd4ef3ccbf6fe`)
reported six unresolved-name diagnostics in `os.kernel.memory.vmm_core`:
`mmio_test_mode_enabled` at five call sites and `mmio_invalidate_tlb` at one.
The MMIO file had regressed to direct runtime wrappers, losing the journal and
mode-control functions still imported by VMM, boot entries and existing tests.
The x86_64 paging module also retained an unused import of the missing TLB helper.

## Repair

Restore the historical test journal from `e274cd33719^`, preserving width-specific
values, latest-write lookup, reset and explicit hardware-mode selection. Hardware
access continues through the existing `mmio_hardware` owner. Do not add raw runtime
declarations to the test-aware MMIO shim.

VMM now skips invalidation in test mode and otherwise calls an exported x86_64
HAL function. The HAL owns the tagged `rt_invlpg(u64)` boundary. Remove paging's
unused stale MMIO import; its existing invalidation implementation is unchanged.

## Validation and limits

The existing MMIO spec now also covers initial zero reads, reset and disabling
test mode. A standalone fixture at
`test/fixtures/compiler/mmio_bootstrap_probe.spl` permits native checks without
loading the general test framework. Its exit codes 1-10 identify mode, width,
reset or cleanup failures. A native binary built by the frozen Phase 2 compiler
ran with exit 0 under a 256 MiB watchdog (observed peak 2,544 KiB).
The volatile-MMIO and baremetal-MMIO authority shell checks passed.
Higher-model review found no blocking issue; VMM's guard was source-reviewed.
Neither privileged invalidation nor hardware MMIO was executed.

Ordinary spec execution is not qualified: the installed full CLI reveals a Rust
seed warning on its command path and an attempted spec failed earlier parsing
`bounded_bytes.spl`. Its fast `--version` path alone is insufficient provenance.
Default native probe packaging also failed after linking; the explicit one-binary
attempt identified missing Darwin SDK/deployment admission metadata. Supplying
the actual installed SDK settings progressed to a separate post-link refusal,
`target-identity-error: invalid-native-action-input-identity`. Six bounded probe
build attempts were retained; stop retries here. No complete build admission is
claimed. Build and runtime results must be reported separately, retaining failed
receipts. The standalone binary behavior is evidence for the MMIO repair only.

For a native regression run, use the frozen Phase 2 compiler and runtime authority,
explicit LLVM and CUDA composition source roots, `--source src/os/kernel/boot`,
`--source test/fixtures/compiler/mmio_bootstrap_probe.spl`, `--entry-closure`,
`--entry test/fixtures/compiler/mmio_bootstrap_probe.spl`, `--mode one-binary`
and `--threads 1`. Supply the actual `SDKROOT` and `MACOSX_DEPLOYMENT_TARGET`,
initialize the SCV journal explicitly for a new checkout, disable MIR sharding
for this small probe, and retain the process-tree watchdog receipt.

Preserve the active build's source snapshot and caches. Include this repair in
the next admitted source rebuild; a running compiler cannot consume live edits.
