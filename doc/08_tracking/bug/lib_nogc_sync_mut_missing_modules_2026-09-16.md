# lib nogc_sync_mut: specs reference modules/exports absent from src/lib (13 specs RED)

**Status:** LIVE (triaged 2026-11-11, lane rt3 two passes — landed half verified green; still-missing half is substantive per-module feature implementation, owners named below)

## Observed (per spec, runtime/semantic error)

- `enterprise_assets_spec.spl`, `enterprise_expense_spec.spl`, `enterprise_quality_spec.spl`,
  `enterprise_warehouse_spec.spl` — `semantic: Cannot resolve module:
  std.nogc_sync_mut.enterprise_{assets.assets,expense.expense,quality.quality,warehouse.warehouse}`.
  No `enterprise_{assets,expense,quality,warehouse}` dirs exist under
  `src/lib/nogc_sync_mut/` (the sibling `enterprise_store`, `enterprise_sale`, ... do exist).
- `mission_critical/domain_arena_v2_spec.spl` — `Cannot resolve module:
  std.nogc_sync_mut.mission_critical.domain_arena_v2`; `src/lib/nogc_sync_mut/mission_critical/`
  contains only `bounded_process_policy.spl`, `domain_arena_v1.spl`, `mci_evidence_manifest_v1.spl`.
- `gpu/chromium_reference_oracle_converter_spec.spl`, `gpu/chromium_reference_oracle_sffi_spec.spl`
  — `runtime: Module "std.nogc_sync_mut.gpu" does not export 'chromium_reference_oracle_sffi'`;
  no such file under `src/lib/nogc_sync_mut/gpu/`.
- `gpu/provider_spec.spl` — `runtime: Module "std.gpu" does not export 'provider'`; no `provider.spl`
  under `src/lib/nogc_sync_mut/gpu/`.
- `concurrent/server_worker_policy_spec.spl` — `Module "std.concurrent" does not export 'server_worker_policy'`;
  `src/lib/nogc_sync_mut/concurrent/` has only actor_hooks/channel/mutex/rwlock/thread.
- `ui_test/gui_driver_spec.spl`, `ui_test/tui_driver_spec.spl` — `Module "std.ui_test" does not
  export 'gui_driver'` / `'tui_driver'`; no such files under `src/lib/nogc_sync_mut/ui_test/`.
- `io/rt_hal_buffer_dispatch_spec.spl` — `Module "std.nogc_sync_mut.io" does not export 'hal_buffer_dispatch'`.
- `spec/scenario_evidence_manifest_spec.spl` — `Cannot resolve module:
  std.common.spec.scenario_text_evidence`; `spec/scenario_evidence_manifest_io_spec.spl` —
  `Module "std.spec" does not export 'scenario_evidence_manifest_io'`.
- `ui_test/sgtti_strict_resolve_spec.spl` (0/8): `method 'resolve_strict' not found on
  type 'SgttiTestDriver'` (4 examples) and `method 'geometry' not found` (2) —
  `src/lib/nogc_sync_mut/ui_test/sgtti.spl` `SgttiTestDriver` (line 175) has no such methods.
- `sffi/package_sha256_spec.spl` — `function 'package_sha256' not found`; spec imports
  `std.nogc_sync_mut.sffi.package.{package_sha256}` but no `fn package_sha256` exists anywhere
  in `src/lib` (only gc/nogc `package/*_sffi_test.spl` reference the name).

## Impact

13 specs ERROR with executed=0; the features they contract (enterprise domain models,
domain arena v2, Chromium reference oracle, GPU provider, concurrent server worker policy,
GUI/TUI drivers, HAL buffer dispatch, scenario evidence manifests, package content hashing)
are unimplemented or were removed without their specs.

## Expectation

Either implement the modules/exports the specs contract, or delete the specs with the
owning lane's sign-off (testing rules forbid weakening assertions to pass).

## Unblock condition

Each named module/export lands in `src/lib` (or the spec is deliberately retired with a
decision record). Re-run: `SIMPLE_TIMEOUT_SECONDS=600 bin/simple test <spec>` expecting
outcome=OK.

---

## 2026-11-11 — Lane rt3 triage verdict: OPEN, partially landed (module census)

Status kept OPEN: many contracted modules now exist and their specs pass, but
a substantive subset is still absent. Census + re-verification on the current
base (seed build `46fe8f6b6def`):

**Modules landed, specs now PASS** (were "Cannot resolve module / does not
export" on 2026-09-16):
- `std.nogc_sync_mut.gpu.chromium_reference_oracle_sffi` —
  `gpu/chromium_reference_oracle_sffi_spec.spl` PASS.
- `std.gpu.provider` — `gpu/provider_spec.spl` PASS.
- `std.ui_test.gui_driver` / `std.ui_test.tui_driver` — `ui_test/gui_driver_spec.spl` 5/5 PASS
  (tui_driver module present alongside).
- `SgttiTestDriver.resolve_strict` / `.geometry` — `ui_test/sgtti_strict_resolve_spec.spl` PASS.
- `std.common.spec.scenario_text_evidence` and `std.spec.scenario_evidence_manifest_io` —
  both modules present (`scenario_text_evidence.spl`, `scenario_evidence_manifest_io.spl`).
- `std.nogc_sync_mut.sffi.package` — module present (`sffi/package.spl`);
  `sffi/package_sha256_spec.spl` PASS.
- (5 of these re-verified green in one batch: provider, chromium oracle sffi,
  sgtti_strict_resolve, package_sha256, gui_driver — 0 failed.)

**Still missing (specs still ERROR, `executed=0`):**
- `std.nogc_sync_mut.enterprise_{assets,expense,quality,warehouse}` — no such
  dirs under `src/lib/nogc_sync_mut/` (24 other `enterprise_*` dirs exist).
  `enterprise_assets_spec.spl` re-verified `outcome=ERROR, executed=0`.
- `std.nogc_sync_mut.mission_critical.domain_arena_v2` — dir still has only
  `bounded_process_policy.spl`, `domain_arena_v1.spl`, `mci_evidence_manifest_v1.spl`.
- `std.concurrent.server_worker_policy` — dir still has only
  `actor_hooks/channel/mutex/rwlock/thread`.
- `std.nogc_sync_mut.io.hal_buffer_dispatch` — no such file.

**Disposition:** the landed half needs no action. The still-missing half
(enterprise×4, `domain_arena_v2`, `server_worker_policy`, `hal_buffer_dispatch`)
is substantive feature implementation beyond a P3 triage lane; per this
record's own unblock condition each module must be implemented by an owner or
its spec deliberately retired with the owning lane's sign-off (testing rules
forbid weakening assertions to pass). Kept OPEN for that subset.

---

## 2026-11-11 second-pass corroboration — lane rt3 pass 2 (worktree simple-p3-rt3-20261111, base 7f0fa174083, seed 46fe8f6b6def)

**Verdict: LIVE (named owners) — corroborates pass 1 census; no drift in either half.**

Fresh directory census at this base:
- Still missing (confirmed): `enterprise_{assets,expense,quality,warehouse}`
  (25 other `enterprise_*` dirs exist, these four absent),
  `mission_critical/domain_arena_v2` (dir still `bounded_process_policy.spl`,
  `domain_arena_v1.spl`, `mci_evidence_manifest_v1.spl` only),
  `concurrent/server_worker_policy` (dir still `actor_hooks/channel/mutex/rwlock/thread` only),
  `io/hal_buffer_dispatch` (no such file).
- Landed half still present: `gpu/chromium_reference_oracle_sffi.spl`,
  `gpu/provider.spl`, `ui_test/gui_driver.spl`, `ui_test/tui_driver.spl`,
  `ui_test/sgtti.spl`.

Behavioral re-check: `enterprise_assets_spec.spl` still
`outcome=ERROR declared>=10 executed=0 passed=0` on the tracked seed
(interpreter, 9.4s) — module-resolution failure unchanged.

Named owners for the missing half (per this record's own unblock condition —
implement the module or retire the spec with the owning lane's sign-off):
- `enterprise_{assets,expense,quality,warehouse}` — enterprise domain lane (`src/lib/nogc_sync_mut/enterprise_*`).
- `mission_critical/domain_arena_v2` — mission_critical package owner.
- `concurrent/server_worker_policy` — concurrent package owner.
- `io/hal_buffer_dispatch` — io/HAL package owner.

No spec edited, no assertion relaxed, no production change attempted in this lane.
