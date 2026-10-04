# Native test generated-source authority: pending follow-up

2026-10-04; inspected release `9af9a8c0c70c4a04f6fc3a5bac7db475362854f5`.
Owner `/root/linker_research`, isolated branch
`work/item4-generated-source-design-20261004`; sidecars N/A.
**Status: design proposal only. No implementation, executed regression or
runtime qualification is supplied by this document.** Root owns subsequent
scope freeze/integration; source changes require concrete test intent first.

## Confirmed source mismatch

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

## Proposed minimal flow

1. Transform the actual input using the existing SPipe/coverage logic. Stage the
   exact resulting bytes in one unique, owned `test` directory before compilation.
   Preserve original-source markers and diagnostics; validate write success.
2. Request a new source admission explicitly for this generated-entry compile.
   A proposed coordinator-only option is `--refresh-source-authority`; its name
   and interface are not frozen yet. The coordinator consumes it, clears the
   inherited source binding, then invokes the canonical acquire/publish path.
   Do this inside the compiler child, before any shards spawn.
3. The canonical refresh discovers the newly staged entry and creates a new
   immutable generation. Existing scope, snapshot integrity and index checks
   remain mandatory. A failed refresh does not fall back to live source or an
   older generation. Normal inherited compilation does not silently refresh.
4. Workers receive the newly published generation and compile its frozen entry.
   The explicit refresh option must not leak as an unknown worker argument.
5. After owned process completion, remove only the owned generated file/directory
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
  `.spl` files unchanged. A deliberate `fn main` compile-negative fixture stays
  plain `.spl`; its error must not be confused with skipped preprocessing.

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
