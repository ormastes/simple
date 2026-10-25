# Phase3 MMIO test owner missing from the release branch

The frozen `89d2e18cd14` compiler CLI build fails at
`src/os/kernel/memory/vmm_core.spl:423:12` resolving
`mmio_test_mode_enabled`. Its explicit MMIO import points at a module containing
only raw read/write wrappers. That module also lacks the reset/disable hooks
already required by the MMIO and VMM map-budget specs. This is a missing owner
implementation, not evidence of a HIR name-resolution defect.

Restore the relevant production/test-owner changes from `6b818cc9b3e`:
explicit test-mode lifecycle and typed latest-write journals; normal reads and
writes delegate to `mmio_hardware`; privileged TLB invalidation delegates to
the x86_64 runtime HAL and is bypassed only while explicit test mode is active.
The VMM failure-budget semantics remain unchanged.

Regression contracts:
- `test/01_unit/os/kernel/boot/mmio_test_backend_spec.spl`: all widths,
  latest-write reads, reset clearing, and mode enable/disable.
- `test/01_unit/os/kernel/memory/vmm_map_attempt_budget_spec.spl`: bounded
  failures, clearing, and stale budgets ignored outside test mode.
- `test/fixtures/compiler/mmio_bootstrap_probe.spl`: native executable contract
  with distinct nonzero failure codes.

Static validation: `git diff --check` passed. Runtime/compiler execution is
UNRUN: the parent Phase3 matrix is near its 48 GiB cap and explicitly prohibits
launching compiler/test processes before watcher clearance. Existing donor
results do not qualify this revision. The next admitted source build must use
this change; the frozen snapshot cannot observe live worktree edits.

Boot initialization evidence: `arch/x86_64/arch_init.spl` calls
`mmio_disable_test_mode` before percpu/topology MMIO in both early-init paths;
`boot/limine_boot_aarch64.spl` explicitly disables it before device setup.
The x86_32 topology and riscv64 named-fw_cfg owners also explicitly disable it.
The hosted test backend is shared module state: MMIO specs must run serially
and reset explicitly before each simulated operation sequence. Tests disable
mode on completion; later hosted callers must reset before using fake MMIO.
