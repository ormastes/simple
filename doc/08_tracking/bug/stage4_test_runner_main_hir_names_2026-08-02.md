# Stage4 test-runner main HIR names

## Reproduction

Stage4 reached `src/app/test_runner_new/test_runner_main.spl` and reported
unresolved `time_now_unix_micros`, `duration_ms`, `to_int`, and
`file_atomic_write` names.

## Fix

Time and atomic-file helpers now come from their concrete `time_ops` and
`file_ops` owners. Text conversion uses the supported optional method form.
The daemon elapsed duration is computed before the success/failure branch, so
both branches see the same value. The adjacent library runner mirror receives
the same time, conversion, and duration-scope fixes.

## Regression evidence

`test_runner_main_hir_contract_spec.spl` checks concrete owners, conversion,
scope order, and mirror parity.

## Grouped library test-runner follow-up

The same broad-facade failure shape remained across the library test-runner
subtree. The grouped repair routes directory walking through
`std.io_runtime`, time reads through the concrete `time_ops` owner, atomic
file writes through the concrete `file_ops` owner, and the system monitor's
previously undeclared raw file read through `std.io_runtime.file_read`.

Behavioral regression coverage is executable rather than a source-text
assertion:

- `test/01_unit/lib/test_runner/bootstrap_facade_owner_behavior_spec.spl`
  recursively discovers a real nested Markdown fixture and reads live system
  metrics through the repaired modules.
- `test/01_unit/lib/test_runner/source_doctest_runner_spec.spl` exercises real
  doctest extraction through `doctest_runner`, whose time, directory, and
  atomic-file dependencies now use bootstrap-visible owners.

The focused no-stub native build compiled 45 modules with 0 failures, and its
fresh executable ran 2 examples with 0 failures. The retained build log is
`build/focused-stage4-facade/logs/native-build.log`.

Bare `to_int(text)` repairs were handled by a separate non-overlapping lane;
that lane also routed `checkpoint.spl` through the concrete time owner after
the batches were integrated. `dir_walk_native` in `test_manifest_scanner.spl` remains a
similar but unproven broad-facade risk because `std.io_runtime` does not expose
that distinct native-walk surface.

## Core execution owner follow-up

The next complete Stage 4 error-collection pass proved the same broad-facade
failure for `ProcessResult`, bounded process execution, raw file size, and file
modified time in `test_runner_execute.spl`. The grouped repair routes the exact
family through `std.nogc_sync_mut.io.process_ops` and
`std.nogc_sync_mut.io.file_ops` in all seven affected modules, and removes the
unused `ProcessResult` import from `test_runner_container.spl`.

Existing behavior coverage remains the oracle for the unchanged operations:
`source_doctest_runner_spec.spl`, `process_tracker_spec.spl`,
`test_runner_tracked_wait_spec.spl`, and
`test_runner_spipe_expect_helper_spec.spl`. Final admission is the no-stub
Stage 4 full-CLI build; the isolated native owner probe was interrupted before
producing a verdict and is not recorded as PASS evidence.

## Directory creation owner follow-up

The next Stage 4 pass proved `dir_create_all` unresolved through the broad
`std.io` facade in `test_runner_coverage.spl`. The same exact family remained
in `doc_generator.spl`; both now import `std.io_runtime.dir_create_all`, and an
unused matching import was removed from `test_runner_main.spl`.

The existing coverage aggregation and system coverage specs remain the
behavioral oracle. The isolated no-stub probe was interrupted without a
verdict, so only the subsequent full Stage 4 build may admit this repair.

## Compiler warning owner follow-up

After the directory repair passed, Stage 4 reached
`test_runner_helpers.spl` and proved its active call-graph and closure warning
accessors were missing imports. The helper now imports the two concrete
compiler owners directly. A focused no-stub interpreter regression clears the
shared owner state, invokes both display helpers, and verifies both owner
accessors remain empty; it passed 1/1 before the next full Stage 4 cycle.

## Doctest cleanup owner follow-up

The next Stage 4 cycle passed the warning helpers and then proved
`file_remove` unresolved through the broad `std.io` facade in both doctest
runners. All four active cleanup calls now import the concrete
`std.nogc_sync_mut.io.file_ops.file_remove` owner alongside their existing
atomic-write dependency.

`source_doctest_runner_spec.spl` now executes a real source doctest and verifies
that its generated fixture is absent after the runner returns. The focused
no-stub diagnostic passed 2/2. Final admission remains the subsequent full
Stage 4 full-CLI build.

## Test-cache stat owner follow-up

The following Stage 4 cycle passed the doctest cleanup repair, reached 395 HIR
modules, and then proved `rt_file_stat` unresolved in
`app.test_cache_shared`. That module was importing three raw runtime symbols
through `app.io.mod`; it now uses the concrete public
`std.nogc_sync_mut.io.file_ops` wrappers for stat, text read, and write. The
adjacent read/write migration prevents the same invalid facade family from
failing on the next resolver step.

`test_result_cache_spec.spl` now records a real dependency, removes it, and
verifies the cached result becomes stale. The single focused command exited
before parsing because the Stage 3 CLI does not expose `test`; it is retained
as non-evidence. Final admission remains the next no-stub full Stage 4 build.

## Shell and process helper owner sweep

The next no-stub Stage 4 cycle passed `app.test_cache_shared`, reached 398 HIR
modules, and then proved `shell_int` unresolved through the broad `std.io`
facade in `test_runner/system_monitor.spl`. A bounded production sweep found
the same ownership defect for shell and process helpers in 65 modules across
test-runner, debug/T32/DAP, QEMU, replay, MCP, package, and process-monitor
surfaces. Those modules now import only the affected names from the concrete
`std.nogc_sync_mut.io.process_ops` owner; unrelated file and environment names
remain on their existing imports, and re-export-only facades were not changed.

`bootstrap_facade_owner_behavior_spec.spl` now executes canonical `shell_bool`
and `shell_int` behavior alongside its live system-resource assertions. The
single focused command stopped at the deployed runtime ABI probe before test
parsing and is non-evidence. Final admission remains the next no-stub full
Stage 4 build.

## Random-access file owner follow-up

The subsequent Stage 4 cycle passed the system-monitor blocker, reached 400
HIR modules, and then proved `file_size` and `file_read_text_at` unresolved in
`test_runner_async.spl`. All five adjacent file helpers in that module now
come directly from `std.nogc_sync_mut.io.file_ops`; the mutability siblings are
re-export-only facades and require no duplicate edit. The related
`test_runner_execute.spl` size/mtime pair was already on the concrete owner.

`random_access_file_owner_behavior_spec.spl` writes a real file larger than the
capture cap, verifies its exact size, and proves the async reader retains the
HEAD and TAIL while reporting the eight omitted bytes. Its single bounded
diagnostic passed 1/1, but the executable identified itself as the Rust seed;
this is supporting behavior evidence, not pure-Simple Stage 4 admission. The
next no-stub full build is the final cycle in this continuation.

## MIR target-family type blocker

The final permitted cycle passed both preceding file/process owner blockers and
advanced to 424 HIR modules. It then stopped in
`compiler.mir_opt.mir_opt.target_family` because `GpuBarrierScope`,
`GpuAtomicOpKind`, and `VhdlProcessKind` were unresolved. No candidate binary
was produced. In accordance with the three-cycle guard, this grouped type-owner
family is recorded for the next fresh continuation; no fourth repair/build
cycle was attempted.

## MIR target-family preload repair

The diagnostic location was package-surface attribution rather than a physical
use in `target_family.spl`: all three names occurred only in an unused preload
inside `compiler/60.mir_opt/__init__.spl`. The preload is removed instead of
adding false MIR hardware dependencies to the target-triple identity layer.
Canonical ownership remains in `compiler.mir.mir_instruction_support`, with
existing GPU/VHDL backend behavior coverage unchanged.

`target_family_package_surface_spec.spl` imports the public `compiler.mir_opt`
package and behaviorally verifies hosted/embedded classification plus feature
metadata. Its bounded diagnostic passed 2/2 on the Rust seed, so it is focused
supporting evidence only; the fresh no-stub Stage 4 build remains admission.

## MIR optimizer facade payload closure

The next Stage 4 cycle showed the preload removal alone was incomplete: the
same three names were then correctly attributed to `compiler.mir_opt.__init__`
at 195 HIR modules. That facade publicly re-exports `MirInstKind`, whose GPU
barrier, GPU atomic, and VHDL process variants carry the missing types. The
existing `compiler.mir.mir_instructions` export edge now mirrors the proven MIR
facade grouping for `GpuBarrierScope`, `GpuMemoryScope`, `GpuAtomicOpKind`,
`VhdlProcessKind`, `VhdlClockDomain`, and `VhdlClockEdge`. No new module edge or
backend-local duplicate type is introduced.

The package-surface regression now constructs and pattern-matches the three
observed `MirInstKind` variants solely through `compiler.mir_opt`. Its seed test
selection broadened into an unrelated failing MIR-opt suite, so that attempt is
non-evidence; the next no-stub Stage 4 build is authoritative.

## Canonical MIR optimizer boundary

Cycle 2 passed the optimizer initializer but reproduced the same aliases at
`target_family.spl`, proving that expanding the convenience export only moved
the failure. The pure-Simple package resolver rematerializes imported enum
surfaces in sibling children; the cross-layer `MirInstKind` re-export therefore
pulled its GPU/VHDL payload closure into every optimizer module and attributed
failures to the current child.

No pre-existing production or test consumer imports MIR base types through
`compiler.mir_opt`. The unused convenience re-export is removed completely:
optimizer APIs remain owned by `compiler.mir_opt`, and MIR types are imported
from canonical `compiler.mir`. The regression keeps its target-family behavior
through the optimizer facade while constructing the three variants through the
MIR facade; its bounded seed diagnostic passed 3/3. A refreshed Stage 3 and the
final no-stub Stage 4 cycle remain authoritative.

## Package-sibling import leak confirmed

Stage 3 was rebuilt from the admitted Stage 2 compiler after the canonical
boundary repair. The 724-module build had zero failures or stub markers; its
bootstrap identity, unsupported-command behavior, candidate frontend admission,
and before/after hash all passed. Nevertheless, the final Stage 4 cycle again
reported the same three aliases at `target_family.spl` after 423 HIR module
declarations.

The remaining owner is the HIR directory-package resolver. Its sibling path
calls `register_glob_imported_symbols`, whose named-import expansion registers
not only a sibling's own declarations/explicit exports but also every name that
sibling imported for private use. `lower_module_enum_definitions` then
rematerializes those leaked enums in each unrelated child and reports missing
payload types against the current child's filename. The compiler fix and
behavioral regression are tracked in
`hir_package_sibling_imported_enum_surface_leak_2026-08-02.md`. No fourth build
was attempted.

## FIXED BY CONTENT — verified 2026-08-17
`src/app/test_runner_new/test_runner_main.spl` no longer resolves these through
the broad `std.io` facade: line 12 is
`use std.nogc_sync_mut.io.time_ops.{time_now_unix_micros}` and line 13
`use std.io.{dir_create_all}` (explicit single-item import, not the glob facade).
`duration_ms` / `to_int` are used as ordinary members. Executable evidence: every
`bin/simple test <spec> --no-session-daemon` run performed today (5 specs,
including 20/20 and 21/21 green files) is driven by this exact module, so the
names resolve at runtime. Status: FIXED.
