# Windows target-preset regression omitted its production import

Observed 2026-10-07 in the restored Phase1 source lineage
`e59027c353e9ed6ea8ddf572424da70e188fe511`, original seed runtime SHA
`0f9bfc1f7a9f6aca254755a543687d6b3d60f18b254da9441cb60e1cd3d4a2c7`.
This is fixture repair evidence, not complete compiler qualification.

`test/01_unit/compiler/target/target_presets_spec.spl` said it had no imports
and replicated preset logic in local helpers. Its Windows criterion instead
called `preset_by_name("windows-x86_64")` without importing that function.
Actual restored row4865 executed16 cases,15 passed and Windows failed with
`semantic: function preset_by_name not found`. Original evidence remains at
`/tmp/simple-phase1-restored19-per-row-attempt-20261007/04865`; its actual
artifact stdout records this error. No failing expectation was weakened.

The production owner `src/compiler/70.backend/target_presets.spl` already
defines Windows x86-64 and dispatches that exact name to the correct preset.
The test now imports only `compiler.backend.target_presets.preset_by_name`
and checks name, architecture, OS, MSVC ABI, pointer width64, enabled standard
library and enabled GC as seven separate exact assertions. Existing15 helper
cases and all helper definitions are unchanged. Their replicated logic is
not presented as production-owner coverage. No compiler/target behavior
changed and no mock Windows preset was added.

The isolated release9a4ba9491915c5eecd2b9d954d99c8425b407ef0 changed spec
SHA `a9370f2e9b1e892f8fa639b2936c65fa3957d26394d141acffae027d58b929ec`
actually passed16/16, zero failures/skips,122ms using the original Phase1
diagnostic runtime. Result:
`/tmp/simple-target-presets-real-owner-result-20261007/result.json`.
Canonical1GiB kernel receipt:
`/tmp/simple-target-presets-real-owner-kernel-20261007/kernel-containment-terminal.env`
records closed0/quiescent1. There was one changed-test run and no green
replay. Generated manual and scoped structural review accompany the repair.

Whole Phase1, native compiler/core/library and later bootstrap phases remain
separately qualified work. This fixture PASS does not admit them.

Documentation verification added authored module documentation for purpose,
audience, scope, preconditions, workflow, evidence, limitations and recovery.
Final source SHA is
`a6fb271cff222df8408a725578d1937c361bb9ee0c5aded2092a60371c070c18`;
removing only that leading module documentation recovers the entire tested
source byte-identically at SHAa9370f2e above. No passing test was replayed.
Canonical changed-source docgen generated1complete/0stubs. Its mirrored
manual is `doc/06_spec/01_unit/compiler/target/target_presets_spec.md`;
unrelated flattened23-case legacy manuals remain unchanged.

The changed-source documentation scan reports16scenarios,23real assertions,
aggregate78,release_ready=true,0blockers. Its six nonblocking warnings were
four existing model cases without step flows, no implemented requirement
identifier, and a source-hash freshness warning because canonical docgen
omits the hash. No fictitious REQ identifier or behavioral step was added.
Mechanical final provenance records the actual source hash while preserving
the generated body; this directly satisfies the scanner's documented
hash-presence freshness predicate. Documentation facts were authored in SPL
and regenerated, not patched into the manual to hide missing source facts.
