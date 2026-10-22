# Critical match coverage severity

Status: **AUTHORED / UNRUN** for this change. Manual authored from the executable spec; no docgen run.

Executable: `test/01_unit/compiler/semantics/match_coverage_critical_spec.spl`.

The twelve API scenarios exercise the real coverage and severity owners. Ten existing cases are carried unchanged. The old critical-wildcard-false assertion now follows the selected later static policy: a wildcard does not cover unnamed static variants under critical or mission-critical. One added case verifies noncritical defaults remain accepted and explicit complete coverage plus a wildcard remains accepted under critical.

The legacy `is_exhaustive()` and `missing_variant_ids()` wildcard behavior is intentionally still tested and unchanged. Variant identity, missing-name reporting, profile/alias severity, complete coverage and foreign-ID controls remain. Real compiler dispatch is covered separately in `critical_enum_extension_wiring_spec.spl`; these API cases alone do not establish compiler wiring.

No runtime, compiler, formal or performance PASS is claimed. See the REQ-002 plan appendix for source ownership, actual pipeline controls and remaining qualification.
