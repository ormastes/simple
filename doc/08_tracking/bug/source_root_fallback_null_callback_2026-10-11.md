# Native loader fallback dispatches through null function pointer

Status: source repair candidate; rebuilt native qualification pending.

Producer SHA256
`fcdb2397a1a681c2b6fe32ada16585b4e24afc37f6397a34db55a183dffb73c2`
crashes before HIR when a selected source-root lookup returns `Missing`.
`source_root_resolution_with_fallback_v1` calls the supplied
`_driver_resolve_entry_import` function value, but native dispatch reaches PC 0.
This is distinct from the earlier enum text formatting failure.

Independent backtrace:
`/home/yoon/dev/simple-foreign-field-owner-20261011/build/native_probe/foreign-field/integrated/source-closure-backtrace.log`.
Frame 1 is the fallback helper at `0x4cc048`; frame 2 is
`driver_source_pipeline_loading.CompilerDriver_load_sources_impl`.
Two unchanged foreign-owner fixtures exited 139. The CUDA owner fixture also
failed source closure with worker exit -139, zero claimed/sealed modules and
outer exit 1; its log is `build/cuda-policy/source-root-fcdb-build.log`.

The loader does not need a callback abstraction. Its caller now matches
`Found`, `Missing`, and `Ambiguous` directly; only `Missing` calls the canonical
resolver. The removed function-value API's four tests were removed, rather
than claiming they pass. The eight numbered/enum native probe assertions and
filesystem ambiguity/default regressions remain. No compiler function-value
codegen fix is claimed; the general dispatch defect remains open.

The removed cross-module callback shape is preserved as a dedicated source
fixture in `test/fixtures/compiler/source_root_named_callback_probe/main.spl`,
with separate callback owner and named target modules. It expects
`NAMED_CALLBACK_PASS` and exit 0. This fixture has not run: the current producer
crashes in its own loader before it can compile such a fixture. The observed
reproducer is the producer's loader and retained backtrace, not a claimed
failure of this newly extracted standalone fixture.

Required qualification: rebuild the producer, run the owner probe and normal
missing-root closure, execute both ambiguous-overlay/default regressions, and
prove disabled CUDA source closure and linked-symbol exclusion. No private
compiler build or second attempt with the crashing producer was performed.

## Changed producer qualification

Producer `e9e8762c79e47d1c0db418d2a8ff5d5eda7b1ef8744ccff32227ae7463926491`
includes the direct fallback correction. The native fixture
`test/fixtures/compiler/source_root_missing_loader_probe.spl`, compiled with
only `test/fixtures/compiler` as an explicit source root, imports an admitted
relative sibling. This returns `Missing` from selected-root lookup and uses
the direct importer-relative fallback. Build and execution passed, exit 0,
printing `SOURCE_ROOT_MISSING_FALLBACK_PASS`. Logs:
`build/cuda-policy/source-relative-e9e8-{build,run}.log`.

A prior missing-module probe referenced a compiler module outside its admitted
snapshot and returned the expected controlled unresolved-import error instead
of SIGSEGV. Its log is `build/cuda-policy/source-missing-e9e8-build.log`.
The general named-callback fixture remains unrun; only removal of callback
dispatch from the loader is qualified. End-to-end source authority still fails
as recorded in `source_root_worker_authority_gap_2026-10-11.md`.

## Preserved aggregate provenance

The record above is retained from externally merged PR #2870 at release
`467b5ad34ea1cc6a92302a4650ee4dc8eb193e9e`. The record below is retained from
frozen aggregate `5227c794ad82aad2328bd665638ac7c903e443c3`; its failed cycle2
producer predates the direct-fallback correction in that aggregate. These are
distinct historical source/producer contexts, not qualification of this
reconciled source head. No new compiler build or runtime test was performed
for this documentation reconciliation.

## Release aggregate reproduction, 2026-10-11

The release aggregate independently reproduced the same fault with source
`c2a88e77ec2847e63cdc540e726ed38f11e6a88b` and pure-Simple producer SHA256
`e05e69a2539bb417eda6519d98666ed244f93fdb7db38e92224f58e80f8af178`.
Its constructor completed 1229 modules with zero failures and the native Hello
probe passed. Compiling `test/fixtures/compiler/nested_enum_field_owner/main.spl`
with LLVM 18 and two HIR workers failed before claimed/sealed modules.

A single bounded debugger probe followed shell children and worker inferiors
until the actual fault, rather than treating the first shell exit as completion.
Worker PID 110891, inferior 17, stopped at PC zero with this stack:

```text
#0 0x0000000000000000
#1 0x00000000004d0e40 source_root_resolution_with_fallback_v1
#2 0x00000000012b3b40 CompilerDriver_dot_load_sources_impl
```

In the Missing arm, the frozen producer calls `rt_closure_func_ptr` with the
callback handle, copies the returned zero to x7, then executes `blr x7` at
`0x4d0e3c`. The return address is `0x4d0e40`. This establishes the failing
function-value dispatch; it does not establish a general callback-codegen fix.
All six constructor source roots contained every tracked entry, and all three
app symlinks resolved. Missing checkout contents are not the cause of this fault.

Evidence is retained under
`/home/yoon/dev/simple-owned-fixes-qualification-20261011/build/native_probe/release-owned-cycle2-20261011/astra-source-closure-debug/`:
`run-debug.py`, `continue-until-fault.gdb`, `debug.log`, and `receipt.json`.
The log SHA256 is
`1fa69c7493bae103a5e8ad7ebf2d4461cd2bc96e845076c77884e2536ef9fd6b`.
The run used CPUs 14–15, a 300-second/6-GiB watchdog and disabled core dumps.
Elapsed time was 111.503 seconds; maximum summed descendant RSS was 3,873,156
KiB. Source and producer identities were unchanged and no owned process remained.
The debugger's exit zero records successful fault capture, not compiler success.

This candidate selectively adapts `353089783b3712b988449600d54bf37c54853bf6`
to the aggregate: two production files, current tests/probes, and this record.
Found keeps its selected path; Ambiguous still reports an error before fallback;
only Missing directly calls `_driver_resolve_entry_import`, including its empty
result. No unrelated policy documentation is included.

Required qualification remains pending: rebuild the coordinated producer, run
the owner probe and normal missing-root closure, and execute the existing
ambiguity/default regressions. The dedicated callback fixture tracks the general
open defect and is not claimed to pass after this loader-only repair. The separate
indexed-layout MIR crash is outside this repair. No new native build or test was
run for this source adaptation; full verification and release admission remain
pending.
