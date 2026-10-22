# Stage 2 test-runner build: imported enum owner text is overwritten

- Status: OPEN
- Bug DB: reconciliation pending. `bug-add` (src/app/bug_add/main.spl) run
  on the Rust seed built from this tree dies in save with `stack overflow:
  recursion depth 1000 exceeded limit 1000 in function 'rename_path'`
  (io_runtime.spl:493 -> rt_file_rename), and no self-hosted full CLI
  exists yet, so `bug_db.sdn` was not updated.
- Date: 2026-10-19
- Platform: aarch64-unknown-linux-gnu
- Blocks: `stage2-compiler-tests` task `test_runner_build` (Stage 2
  qualification of `--full-bootstrap --stop-after-stage2`), hence the
  bootstrap verdict `ABORTED: stage=stage2-compiler-tests`.

## Observation

The admitted Stage 2 compiler builds `src/app/test_runner_new/main.spl`
through HIR, then fails in MIR with two error families (138 errors, run r4,
base `630f773bdc7` + `cb651fe214e` + `ab61aacfa0e`):

```text
enum construction: unregistered declaration 'schema=.TestExecutionMode'
enum construction: unregistered declaration 'schema=.TestOmissionStatus'
unresolved method call: operator overload for struct
  lib.common.perf.execution_metrics.TerminationCause (no matching __eq__ ...)
```

The second family is `==`/`!=` between an enum-typed field read and an enum
literal (`src/lib/nogc_sync_mut/test_runner/native_owned_process.spl:36`,
`src/lib/nogc_sync_mut/mcdc/dynamic_aspect.spl:78`,
`src/lib/nogc_sync_mut/io/process_ops.spl:1103`): `local_enum_type_id` does
not match the two sides, so `expr_dispatch.spl:4076` treats the enum operand
as a struct.

The first family shows the cause: `enum_qualified_key`
(`switch_operators_calls.spl:240`) builds `"{owner}.{Name}"` from
`symbol_defining_module_scalar_raw`, and the owner text it reads is
`schema=...` -- bytes of the build-progress snapshot writer
(`src/lib/common/build_progress/model.spl:3`, `schema=simple-build-progress-v1`),
not a module path. In run r1 (before `cb651fe214e`) the same corruption read
`schema=simple-build-progress-v1.MemoryOrdering` (157 errors). The defining
module text of imported enum symbols is reclaimed and its storage reused
while the symbol row still points at it: a dangling text root, the
transient-scope lifetime class.

`test_runner_build` lowers HIR in the main process for every module whose
shard cache store is refused (`[hir-cache] ... refused=... reason=codec`),
so the main-process HIR path is the suspect owner.

## Reproduce

```sh
SIMPLE_CACHE_SCOPE=<lane> LLVM_SYS_231_PREFIX=<llvm-23.1.2> \
  sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap \
  --stop-after-stage2 --mode=dynload --jobs=8 --output=<fresh> \
  --produce-stage3-receipt=verify-landed-compiler-fix
# -> <fresh>/stage2-compiler-tests/<triple>/verification/logs/test_runner_build.log
```

Stage 2 compiler sha256 for r4: `79307b44e2233463ef44f164dae0eb480c536c316d5c2f85021273480824f7d9`.

## Not yet established

Which owner stores the text without promoting it. No source workaround is
small enough: the corrupted rows differ run to run.
