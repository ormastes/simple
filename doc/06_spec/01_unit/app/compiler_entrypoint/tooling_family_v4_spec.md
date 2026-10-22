# Finite tooling inventory v4 regression manual

Execution status: UNRUN. Source-only review does not establish native correctness.

Executable: test/01_unit/app/compiler_entrypoint/tooling_family_v4_spec.spl.

1. Normalize actual canonical selectors; inspect scalar family count/order and reject sibling, traversal, foreign and control-bearing selectors.
2. Encode/decode real membership records and check each scalar path; replace a selected family while preserving the others.
3. Decode exact v3/v4 contracts and reject wrong versions, missing named digests and malformed records.
4. Create a real isolated Git fixture with all eight canonical selectors. Acquire cold authority, advance other-family commits, add/delete an untracked tooling source, and verify snapshot content and generation rejection.
5. Publish an actual legacy v3 cursor through the production publisher; require warm tooling refusal and a real cold-owner migration.
6. Exercise the production bounded pointer reader with a maximal legal v4 record and an oversized negative record. These reader-only adversarial bytes are never offered to source admission.

Expected: scalar assertions pass and I/O helpers return an empty failure string. Evidence must include actual test exit/output and compiler identity before any PASS is recorded. No test has been executed for this source-only change.
