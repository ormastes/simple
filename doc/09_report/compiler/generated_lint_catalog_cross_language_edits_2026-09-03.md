# Generated Lint Catalog and Cross-Language Edit Metadata

**Date:** 2026-09-03

**Scope:** generated lint catalog projection and normalized edit metadata

**Verdict:** PASS for the focused slice

## Changes

- Removed the independent `lint_name_is_known` match table. Membership now comes from the same canonical default catalog as enumeration and configuration.
- Added canonical per-profile rule descriptors for Moderate, Strict, Robust, and Critical projections without changing existing levels.
- Fixed the observable catalog drift where `nonexistent_type` had a default but was absent from the manual membership table.
- Replaced numeric edit applicability with `LintFixApplicabilityV1`.
- Added provider ID, language ID, expected snapshot digest, and conflict group metadata to normalized edits.
- Projected edit provenance through JSON, SARIF, and LSP code actions.

No KPF schema or extended-enum source was changed.

## Non-Vacuous Evidence

- `generated_rule_catalog_spec.spl`: 2/2 PASS; requires more than 50 rules, equal descriptor counts, formerly omitted membership, and profile-specific severity values.
- `output_adapters_spec.spl`: 3/3 PASS; verifies typed applicability and conflict metadata in normalized output.
- `tooling_edge_protocol_adapters_spec.spl`: 4/4 PASS.
- `toolingd_adapter_spec.spl`: 5/5 PASS.
- `git diff --check`: PASS.

## Compatibility

Existing lint rule defaults and profile escalation behavior are preserved. The normalized edit record is intentionally extended at its current internal V1 source boundary; all repository constructors were migrated in this commit.
