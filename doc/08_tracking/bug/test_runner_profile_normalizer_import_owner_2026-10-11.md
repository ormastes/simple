# Test-runner profile normalizer imported through the wrong owner

Status: local import-only repair, native verification pending. No release or
performance admission. Canonical implementation and profile semantics unchanged.

The failed-entry diagnostic for `test_runner_config.spl` exposed its import of
`normalize_profile_name` from `test_runner_args`. That module no longer defines
the function: its WP-3 comment and import identify
`compiler.common.assurance.policy_names` as the canonical owner. Importing a
name privately does not establish a public definition for dependent modules.

The configuration reader now imports the canonical leaf directly. The existing
`test/01_unit/lib/test_runner/profile_aware_execution_spec.spl` uses the same
owner for normalization while retaining argument parsing imports from
`test_runner_args`. No assertions, accepted aliases, defaults or validation
rules changed. The existing suite covers profile aliases, invalid values,
manifest reading and precedence; execution on the repaired pure runner remains
UNRUN. Direct failure evidence is retained under
`build/native_probe/build-runner-review-20261011/test-failed-direct-09-test_runner_config/`.

The canonical leaf has no imports or module-level state. This removes an
unnecessary dependency through CLI argument parsing for this name, but source
inspection is not a latency or memory measurement. Verify compilation,
real profile behavior and equivalent-work startup/peak memory before admission.
The frozen running diagnostic source was not modified. Canonical bug-DB
reconciliation is pending; this document records the local defect and repair.
