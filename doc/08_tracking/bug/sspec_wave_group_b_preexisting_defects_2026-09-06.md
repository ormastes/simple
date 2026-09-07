# Pre-existing product defects surfaced during sspec modernization (group B, 2026-09-06)

While modernizing three system specs to raw=100/blockers=0
(`test/03_system/check/core_c_bootstrap_runtime_capsule_contract_spec.spl`,
`test/03_system/compiler/compiler_services_system_spec.spl`,
`test/03_system/compiler/debug_sidecar_json_order_spec.spl`), the following
genuine pre-existing product defects were confirmed and left RED (not
weakened) per testing rules. Each was RED at baseline before this
modernization pass began — none was introduced by it.

## 1. Core-C bootstrap runtime capsule producer contract drift

`scripts/check/build-core-c-bootstrap-runtime-capsule.shs` no longer mentions
two strings its own contract spec requires:
- `runtime_pool.c` — not present anywhere in the script (grep confirmed).
- `git status --porcelain --untracked-files=all` — not present anywhere in
  the script; the dirty-input gate may use a different mechanism now, but the
  documented contract string is absent.

Spec: `test/03_system/check/core_c_bootstrap_runtime_capsule_contract_spec.spl:19,150`
(scenarios "uses the canonical ordered core-C source graph" and "fails closed
on dirty input and existing output"). Baseline and after-modernization both
show `passed=4 failed=2` — unchanged, confirming this is pre-existing.

## 2. TypeCheckPort.check_fn dispatch returns nil through `any` field

`src/compiler/00.common/compiler_services.spl:158` defines
`_noop_check(module_name: text) -> [text]: []`, correctly returning an empty
list, and wires it at line 189 as `TypeCheckPort(... check_fn: _noop_check)`.
At runtime, `svc.type_checker.check_fn` (an `any`-typed field) called via
`val check = svc.type_checker.check_fn; check("my_module")` returns `nil`
instead of executing `_noop_check`, causing
`semantic: method 'len' not found on type 'nil'` wherever the result is
inspected. The structurally identical `HirLowerPort.lower_fn` and
`MirLowerPort.lower_fn` (same `any`-typed-field, same
`(text) -> [text]` shape) dispatch correctly in the same file, so this is
specific to `TypeCheckPort.check_fn`, not `any`-typed fields generally.

Spec: `test/03_system/compiler/compiler_services_system_spec.spl` lines
~182, ~194, ~403, ~449 (four scenarios: "type checker validates module by
name", "type checker returns empty error list for unknown module in noop",
"simulates a complete compilation run through all 9 stages", "pipeline can be
run for multiple modules"). Baseline and after-modernization both show
`passed=25 failed=4` — unchanged, confirming this is pre-existing.

## 3. FPGA Linux manifest/orchestrator split (SA-3) not yet done

`src/hardware/fpga_linux/fpga_linux_manifest.spl` and
`fpga_linux_orchestrator.spl` do not exist anywhere in this tree (confirmed
absent via `ls`, 2026-09-06), so every source-contract scenario in
`test/03_system/compiler/debug_sidecar_json_order_spec.spl`'s first describe
block genuinely fails (file-not-found or `-1` offset comparisons). Separately,
`build/rtl_linux/generated_rv32` and `generated_rv64` (SA-3 split build
output) do not exist either, so the generated-output scenarios also fail
closed. The SA-1 baseline document
(`doc/09_report/verify/rtl_mdsoc_baseline_2026-05-02.md`) DOES already exist
and does contain a `debug.json` section — that half of the contract is
satisfied.

As part of this modernization, three `pending(...)` placeholder scenarios in
this spec were converted to real fail-closed tripwire assertions (required by
the `.spipe` scorer's SSDOC-ORA-001 blocker rule, which treats any
`pending(...)` call as a scaffold that can never itself be the oracle). This
is a deliberate, rule-mandated change, not a regression: those three
scenarios previously reported PASS via the pending marker even though the
underlying SA-3/SA-1 gate was unmet; they now report the same unmet gate as a
real FAIL, which is the correct status until SA-3 lands the split files and
populates the generated build directories. Baseline
`passed=4 failed=10 skipped=8` (executed=22, including 8 dynamically-generated
pending sub-entries) became `passed=2 failed=12 skipped=0` (executed=14,
matching the static `it` count exactly) after modernization — every
previously-skipped or pending-masked scenario now reports its real status.

## Note on 2026-09-06 concurrent-write clobber

This spec file and this bug record were both silently reverted to their
pre-edit state by a concurrent write from another session in this shared
working copy shortly after the first modernization pass completed and was
verified. Both were reapplied identically from the verified content. If this
happens again, reapply from this record (it documents the exact intended
end-state) rather than re-deriving the fix from scratch.
