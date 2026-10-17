# Leak-check result schema and failed status loss

Date: 2026-10-16. Base: `6a0600fed4015690b72efff8b21e531f10112ba9`.
Status: repair implemented; execution/native admission pending. Bug DB reconciliation pending: no callable bug-add/database tool was available and an admitted full CLI is not available in this lane.

`LeakCheckResult` lacked `target`, `verdict`, and `static_violations`, although static/growth runners and lightweight finalization used those fields. The canonical owner is `compiler.tools.leak_check.types`; its app facade reexports that owner. Both source constructors now explicitly initialize the appended fields, preserving the existing field order.

Concrete failure: `run_static_check` on a nonexistent file returns `exit_code=1`, `verdict="fail"`, and no violation records. `finalize_light_result` previously treated empty violation/growth arrays as success and replaced that result with `exit_code=0`, `verdict="pass"`. Failed growth startup can follow the same path. Finalization now preserves every nonzero exit code and records a failing verdict before interpreting successful observation rows.

Regression: `test/01_unit/app/leak_check/result_status_spec.spl` exercises the actual missing-file runner and finalizer, independent factory arrays and typed violation fields, preservation of exit125, and positive static classification. No source-text assertion substitutes for these behavioral checks. Execution and branch coverage remain unverified; no interpreter/native PASS claimed.

The earlier upstream `StaticViolation` declaration fix (#3536) is necessary but does not repair this result schema or lost failure status. Existing linked MCP/LSP startup cohorts contain no leak-check native owner entries and do not qualify this change. No full compiler/tool build was started while the main build and tool workers reserved memory.
