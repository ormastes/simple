# Incremental-build optimization handoff

This is a proposed implementation handoff, not documentation of enabled compiler behavior.

Start with the [detailed design](../../05_design/incremental_build_metadata_20261008.md) and [parallel work packages](../../03_plan/agent_tasks/incremental_build_metadata_20261008.md). The [acceptance plan](../../03_plan/sys_test/incremental_build_metadata_20261008.md) defines the warm 100 ms target, correctness matrix and measurements still required.

Prioritize actual pure-Simple compilation costs: redundant toolchain reads, heavy TLDR consumer imports, and per-worker source inventory refresh. Existing TLDR and SMF files alone do not prove that these costs are avoided. Preserve complete cache identity, source-generation pins and publication validation.

Header readiness and object readiness are separately committed results. Object failure preserves a valid header but fails any required object/link join. Interface-only compilation does not claim diagnostics for unread dependency bodies; full diagnostic qualification needs exact matching body-validation coverage.

Continue bootstrap with immutable source/recipe bindings while optimization candidates are tested separately. Reuse valid successes and collect independent failures to the end. Report module progress, generated objects, linked executables and passed test cases separately.

Before enabling new runtime behavior, implementation owners must add real executable SPipe scenarios and generated manuals, run the relevant correctness/memory/performance checks, and update affected build/bootstrap/test skills and agent instructions. This proposal does not silently change those workflows or certify a release.
