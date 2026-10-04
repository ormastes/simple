# Native test generated-source authority

2026-10-04; inspected release `9af9a8c0c70c4a04f6fc3a5bac7db475362854f5`.
Owner `/root/linker_research`, isolated branch
`work/item4-generated-source-design-20261004`; sidecars N/A.
**Status: frozen repair source-reviewed at `44d01e5fbcb`; all behavioral
execution UNRUN.** Initial intent `b83b2acb980` preceded production edits.
The original source mismatch below records the inspected base, not a claim that
the repaired candidate still has identical behavior. Root owns integration;
source review and authored tests do not qualify the runtime or close item4.

## Original confirmed source mismatch

`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl` writes the native
SPipe wrapper under the OS temporary directory in `preprocess_spipe_file`.
Both explicit-AOT and coverage native compile argument paths explicitly select
only `--source src/lib`. The coordinator's
`native_build_authority_source_roots_v1` in `src/app/cli/native_build_main.spl`
requires the entry to belong to the admitted checkout. The source-authority
owner further restricts inventory families to `src` and `test`. An OS-temporary
wrapper cannot satisfy this contract.

Removing only the outside-checkout rejection would weaken authority and is not
the remedy. Moving only the wrapper is also insufficient: the coordinator skips
fresh acquisition when `SIMPLE_SCV_SNAPSHOT_ROOT` is already inherited.
`src/app/io/_CliCompile/native_build_closure.spl` then opens and validates that
immutable generation; a wrapper created afterward is absent from it. That
failure is correct for inherited snapshots and must remain so.

The canonical default in `native_build_snapshot_source_roots_v1` already covers
`src/app`, `src/lib`, `src/compiler`, `src/os`, `src/plugins`, plus an uncovered
entry parent. Remove the runner's hardcoded `--source src/lib` rather than
duplicating this list in another owner. Explicit finite source choices in other
callers remain unchanged.

## Existing mechanisms to reuse

- `std.nogc_sync_mut.io.file_ops.secure_temp_dir` can allocate a unique owned
  directory beneath an explicit parent. Stage source under a nonignored `test`
  descendant, for example `test/native-generated-<unique>/entry.spl`. The name
  must not match ordinary spec discovery. Keep executable/cache output elsewhere.
- `compiler_source_authority_acquire_v1` in
  `src/app/compiler_entrypoint/source_authority.spl` validates selected families,
  refreshes inventory, acquires a snapshot and checks its binding.
- `compiler_inventory_refresh_v1` and its locked implementation in
  `inventory_events.spl` discover untracked source via canonical Git membership:
  cold `ls-files --others --exclude-standard`, warm porcelain status with all
  untracked files. Existing membership comparison handles subsequent deletion.
  No manually synthesized event, digest, CURRENT file or admission receipt is needed.
- `compiler_source_authority_clear_v1` and `publish_v1` already own the complete
  environment binding. Internal compilation workers inherit that frozen binding;
  they must not independently refresh it.

Read-only ignore inspection found `test/runtime_generated/.../entry.spl`
nonignored, whereas `test/.tmp_native_example/entry.spl` matches `.tmp*/`.
This is a current-checkout observation, not permission to bypass future ignore
or source-membership rules. A staging failure must remain a named error.

## Frozen repair flow

1. Transform the actual input using the existing SPipe/coverage logic. Stage the
   exact resulting bytes in one unique, owned `test` directory before compilation.
   Preserve original-source markers and diagnostics; validate write success.
2. Request a new source admission explicitly for this generated-entry compile.
   The coordinator-only option is `--refresh-source-authority`. It consumes the
   option, rejects duplicates and internal-worker use, clears the
   inherited source binding, then invokes the canonical acquire/publish path.
   Do this inside the compiler child, before any shards spawn.
3. The canonical refresh discovers the newly staged entry and creates a new
   immutable generation. Existing scope, snapshot integrity and index checks
   remain mandatory. A failed refresh does not fall back to live source or an
   older generation. Normal inherited compilation does not silently refresh.
4. Workers receive the newly published generation and compile its frozen entry.
   The explicit refresh option must not leak as an unknown worker argument.
5. After terminal compilation, remove only the owned generated file/directory
   unless keep-artifacts is requested. Report cleanup failures honestly; never
   remove another job's directory or an active source generation. Later normal
   inventory refresh observes source deletion; old immutable snapshots remain.

Do not temporarily mutate and restore the runner parent's environment: parallel
jobs could inherit the wrong authority. The present `_run_scoped_child` interface
does not expose an isolated environment overlay. A wholesale migration to the
V4 process API would be a larger change than this coordinator-owned request.
Do not clear source authority for all public native builds or weaken the inherited
snapshot owner's failure behavior. Inventory priming is a distinct prerequisite,
not an excuse to set cold initialization on every child.

## Authored owners and evidence limits

`native_test_source_stage.spl` exports `NativeTestSourceStageV1{directory,path}`,
`native_test_stage_source_v1(checkout_root,source_path)` and
`native_test_cleanup_source_v1(stage,keep_artifacts)`. Reads use the existing
checked regular-file provider; cleanup validates the exact stage path and never
recursively removes the directory. A foreign file causes cleanup failure and
permits retry. The ordinary SMF path remains unchanged.

`native_build_authority_request_v1(args,internal_worker)` returns
`NativeBuildAuthorityRequestV1{args,refresh}`; ordinary option values retain their
bytes even if equal to the refresh token. Only the compiler coordinator changes
its own binding. Coverage and explicit AOT stage the preprocessed source and use
canonical default roots. Staging cleanup occurs before executing the compiled
image; keep-artifacts preserves it and cleanup failure preserves the primary
compilation error.

The compile call requests the existing owned-test process route. On Windows,
when a completion receipt reports `tree_reaped=false`, the runner fails and
retains source, image and cache. A missing receipt on other providers uses the
existing synchronous completion contract. This is not universal proof that all
descendants were reaped, nor resource-scope qualification.

Five unit scenarios are authored in
`test/01_unit/lib/test_runner_native_source_authority_spec.spl`; one real Git
snapshot scenario is authored in
`test/02_integration/app/native_test_generated_snapshot_spec.spl`
(`a86230d1301`, manual `9ce30feac71`). The latter calls real cold/warm acquire,
checks exact staged bytes, deletion and sealed prior generations, and compares
the caller's snapshot-root binding. It does not invoke the CLI refresh option
or prove child environment isolation. All six scenarios remain UNRUN.

## Test-first acceptance before implementation

Use real owner calls and filesystem artifacts, without source-string assertions
as substitutes for behavior. At minimum:

- Exact staged bytes, unique nonignored `test` paths, write failure, cleanup and
  keep-artifacts behavior. No stage appears in arbitrary OS temp or ignored scope.
- Two independent stages cannot collide or remove one another; the caller's
  environment binding remains unchanged.
- A prior snapshot lacks a newly staged wrapper; explicit refresh admits a new
  generation containing it, while the previous generation remains immutable.
- Ordinary inherited requests retain their old binding/failure behavior. Outside
  `src`/`test`, malformed provenance and ignored/missing source still fail closed.
- Real compiler imports beyond `std` use canonical default roots after removal
  of the hardcoded source list. Both coverage and explicit backend call paths
  use the same admission contract.
- Warm inventory observes generated-source creation and deletion without forged
  journal writes. Existing compatible caches remain intact.
- Native backend integration's positive and assertion-failure SPipe fixtures
  must end in `_spec.spl`, because preprocessing deliberately returns ordinary
  `.spl` files unchanged. A deliberate zero-example `fn main` fixture stays
  plain `.spl`; this fixture intentionally exercises zero-example rejection
  after execution, not a compile-negative claim.

A real native executable, non-vacuous test summary and expected failure outcome
are required for eventual behavioral evidence. Authored tests alone remain UNRUN.

## Runtime evidence remains separate

The prior three item4 diagnostic attempts and timeout are recorded in
`doc/08_tracking/bug/item4_source_inventory_cold_init_timeout_2026-10-03.md`.
This source mismatch does not prove the cause of that cold-inventory timeout.
No fourth blind attempt, lock deletion, rebuild or live-process change follows
from this design.

`doc/07_guide/tooling/bootstrap_failure_collection.md` permits provisional work
with an immutable pure-Simple producer after its real compile-and-run Hello gate,
before formal admission. A compiler-only artifact still does not provide the
full CLI/test runner. Current independently owned runtime progress must be
recorded with exact hashes and receipts; it does not turn this design or item4's
full SDK, five-host, coverage and resource gates into PASS.
