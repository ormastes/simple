# Simple Language Remaining Goal Plan

Date: 2026-05-13

## Goal

Make Simple production-level while keeping library parity work delegated to the
other active agents. This lane covers docs, directory/file hygiene, dirty
generated-file prevention, API consistency, short Ruby-like expressive API
guidelines, stable error/warning messages, and final verification readiness.

## Current Evidence

- Production audit: `doc/03_plan/simple_language_production_audit_2026-05-13.md`.
- API docs:
  - `doc/01_research/local/api_design/naming.md`
  - `doc/01_research/local/api_design/ruby_features.md`
  - `doc/01_research/local/api_design/errors.md`
- Hygiene gate:
  - `scripts/audit/repo_hygiene_audit.py`
  - `scripts/audit/repo_hygiene_policy.json`
- API consistency gate:
  - `scripts/audit/api_consistency_audit.py`
  - `scripts/audit/api_consistency_baseline.json`
- Diagnostic gates:
  - `scripts/audit/diagnostic_code_audit.py`
  - `scripts/audit/diagnostic_catalog_audit.py`
  - `test/02_integration/app/diagnostics/check_diagnostics_contract_spec.spl`
  - `test/02_integration/app/diagnostics/run_diagnostics_contract_spec.spl`
  - `test/01_unit/compiler/diagnostic_formatter_contract_spec.spl`
- Import warning debt: `doc/03_plan/import_warning_debt_2026-05-13.md`.

## Remaining Work

| Area | Remaining item | Stop condition |
| --- | --- | --- |
| Compiler imports | Resolve or retire remaining non-library compiler unresolved-import buckets: obsolete HIR/MIR seed tests, verification namespace, MDSOC weaving diagnostics, and watcher build import. | `simple check src/compiler` exits 0 with no unexpected import warnings, or each remaining warning is documented with owner and rationale. |
| Libraries | Library import and parity warnings remain delegated to other agents. | Library lane reports closure or its own tracked debt with current `simple check src/lib` evidence. |
| API predicates | Reduce the frozen legacy `is_`/`has_` predicate-prefix baseline without breaking compatibility. | `scripts/audit/api_consistency_audit.py` passes with a lower checked baseline. |
| Error depth | Broaden semantic diagnostic fixtures beyond direct literal mismatch cases. | End-to-end CLI tests cover representative non-literal semantic type errors with stable codes/help. |
| Global verify | Run the full repo verification workflow after implementation lanes converge. | Verify report covers docs, hygiene, API consistency, diagnostics, compiler/app checks, and library delegation status. |

## Latest Evidence Before Sync

- `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler module_resolver --lib`: 50 passed.
- `bin/release/x86_64-unknown-linux-gnu/simple test test/01_unit/compiler/lint/public_doc_spec.spl --mode=interpreter --clean`: 9 passed.
- `git diff --check`: passed before the sync request.

## Sync Plan

1. Commit the current workspace with a Lore-format decision message.
2. Fetch remote refs with `jj git fetch`.
3. Rebase onto `main@origin`.
4. Check tracked file count before and after rebase.
5. Set `main` to the committed revision and push with `jj git push --bookmark main`.
