# Requested native entry dropped by the dependency filter

Status: source fix prepared; executable regressions and replacement compiler
qualification are pending. REQ-NATIVE-REQUESTED-ENTRY-001 preserves requested
entries with and without collection feedback. REQ-NATIVE-REQUESTED-ENTRY-002
keeps unrelated test dependencies excluded.

The retained Windows Stage 2 compiler from source `7734f947be8ba9465d0ba312170681074e990587`
reported zero source files for an existing frozen snapshot entry beneath
`test/04_smoke`. Earlier analysis incorrectly assumed this invocation reached
the explicit collector and localized the problem to nullable file reads.
That inference was wrong: the ordinary native CLI takes the dependency
collector when the compiler-owned entry configuration is missing.

## Exact source chain in 7734

1. `src/app/io/_CliCompile/compile_targets.spl:1223` exports the parsed,
   admitted `entry_point` as `SIMPLE_NATIVE_BUILD_ENTRY`; line 1247 clears
   `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE` to `0` before loading.
2. Both native CLI compilation branches call
   `native_build_compile_with_collection_profile(driver, entry_point, ...)`
   at lines 1325 and 1375. The same local value supplies the environment and
   this argument; the fix does not recover an earlier host path or replace
   the admitted snapshot path.
3. `native_collection_profile.spl:39` previously called
   `compiler_driver_run_compile(driver)` without publishing an entry in
   `driver.ctx.config`. That compiler helper simply calls `driver.compile()`.
4. `driver_phase_gates.spl:29` obtains the explicit entry exclusively from
   `ctx.config["compiler_source_entry"]`. The only existing write was in
   `driver_source_llvm_ir.spl:131`, a different compiler API.
5. `driver_source_pipeline_loading.spl:248` therefore computes
   `explicit_entry_closure=false` while the environment still enables
   `entry_closure_walk`. Lines 727–732 select
   `_driver_collect_entry_import_source` for this requested native entry.
6. `driver_source_loading.spl:1407` rejects an absolute path containing
   `/test/` before reading its contents. The snapshot entry satisfies that
   predicate, so phase 1 receives an empty collection.

The shared native collection-profile handoff now publishes precisely
`compiler_source_entry=entry_path` before either profiled or unprofiled
compilation. It follows the existing compiler owner pattern for mutating
driver context; no context copy, global filter relaxation, or new semantic
policy flag is introduced. Dependency collection remains unchanged.

## Acceptance and evidence

`native_requested_entry_context_spec.spl` drives the real shared handoff in
Check mode, with an absolute existing test entry and with/without a valid,
source-bound collection profile. A negative control checks that a neighboring
existing test source is still rejected by dependency collection. These are
behavioral assertions, not source-text matching. Tests are not yet executed.
The source diff passed whitespace validation and the working-tree direct
environment/runtime guard. These checks do not establish runtime correctness.

A separate retained-compiler diagnostic subsequently compiled the tracked
`src/compiler/bootstrap_admission/hello_world.spl` and ran its output with
exit 0 and exact `hello` output. Its evidence is preserved under
`D:/dev/windows-release-7734-build-20261002/rejected-hello-cycle5` and records
`canonical_admission=0`. That source-tree entry avoids the test dependency
filter; it neither verifies this patch nor qualifies a full test runner.
This routing fix makes no claim about memory-cap defects or their fixes.

Prior diagnostic evidence is preserved at
`D:/dev/windows-nullable-source-evidence-20261002`. Its isolated extracted-shape
ABI probe compiled successfully and passed 13 source-boundary observations;
it exited 2 because the old Rust producer evaluates a successful `??` operand
twice. That separate defect is independently owned. The ABI probe did not
exercise the actual native-entry configuration handoff and did not qualify
the retained compiler.

The frozen checkout, rejected candidate and all caches are unchanged. No
additional retained-candidate invocation or previously passing check was run
to establish this source-level routing defect.
