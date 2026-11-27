# Stage 2 test-runner build: imported enum owner text is overwritten

- Status: fix-implemented-verification-pending (2026-11-08): the source fix
  landed on 2026-10-19 as `eddc499e14e` (see "Fix" below). The 2026-11-03
  line that said "no source change proven; root cause cannot be established"
  was stale: it missed that commit. Verify by re-running the Reproduce
  command with a stage2 built from current release/1.0.0 and checking
  test_runner_build.log for `schema=` owner text.
- Bug DB: reconciled 2026-11-08 (`bugs_active` row ->
  `fix-implemented-verification-pending`, lane `lane-f-enumowner`). Filing
  history: `bug-add` (src/app/bug_add/main.spl) run on the Rust seed built
  from this tree died in save with `stack overflow: recursion depth 1000
  exceeded limit 1000 in function 'rename_path'` (io_runtime.spl:493 ->
  rt_file_rename), and no self-hosted full CLI existed yet, so `bug_db.sdn`
  was not updated at filing time.
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

**Revalidated 2026-11-02: still plausible because the report title (Stage 2 test-runner build reads overwritten imported-enum owner text (schema=..) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

## Fix (2026-11-08 reconciliation, lane `lane-f-enumowner`)

The "Not yet established" owner WAS established, the same day this record
was filed, by commit `eddc499e14e` (2026-10-19, "fix(compiler): logical-name
memo must not retain entries from a transient scope"), which is on
release/1.0.0. The record was never updated to cite it; the 2026-11-02 and
2026-11-03 notes above re-derived "no fix cited" from this record alone.

Root cause (gdb on the r4 Stage 2, per that commit): the freed text was NOT
the symbol row's `defining_module` -- it was the memo VALUE returned by
`module_logical_name_from_path` (`src/compiler/00.common/module_path_naming.spl`),
which `enum_qualified_key` reaches through
`bootstrap_mir_logical_module_name` (`50.mir/_MirLowering/bootstrap_globals.spl:82`).
The memo (cycle-166, `68e5680a0a8`) inserted into a module-level dict on
every miss; misses occur inside the per-file HIR and per-module MIR
transient scopes, no promote root reaches a module-level dict, so scope end
freed the retained value and later hits returned reused storage (the
build-progress writer's `schema=...` bytes). The dangling inserts were
placed under `HirLowering.register_imported_type_methods_inner` -- the
imported-enum registration path, which is why only imported enums showed
the corruption and why the rows differed run to run.

Fix shape: a plain lookup never inserts; retention is opt-in through
`module_logical_name_cache_warm`, called at state 0 (no scope running) by
`driver_warm_mir_logical_names_v1` (`80.driver/driver_pipeline_lowering.spl`)
for every module name and every symbol's defining module, so MIR keeps its
hit rate. The source now cites this bug id at `module_path_naming.spl:196`.

Why the workaround proposed for this lane ("make `defining_module` owned at
the store point") was NOT applied: the corruption is fully explained by the
memo, the symbol row's own text is a persistent HIR string (it is what the
driver warms FROM), and adding a second speculative copy would be dead
weight. Premise checked against current code before acting (lane rule).

Evidence this tree carries the fix:

- `git show eddc499e14e~1:src/compiler/00.common/module_path_naming.spl |
  grep -c _module_logical_name_cache_retaining` = 0; at HEAD = 4.
- `sh scripts/check/check-transient-scope-text-field-promotion.shs` on this
  worktree: `PASS — 4 freeze-scope text field(s) checked ..., logical-name
  memo store guarded` (exit 0). Tier 1 of that gate is the push-tier
  regression pin for an unguarded memo store (7 selftest fixtures).

Specs (both cited per testing rule; interpreter lane, Windows,
`bin/simple.exe test`):

- Reproducing/guard spec:
  `test/01_unit/compiler/bootstrap_regressions/imported_enum_owner_logical_name_memo_guard_spec.spl`
  -- 8 examples. Against the pre-fix `module_path_naming.spl`
  (`eddc499e14e~1` swapped in, then restored): `3 passed, 5 failed`
  (outcome=ERROR). Against HEAD: `8 passed, 0 failed`.
- Native free/reuse itself (not reachable on the interpreter, whose
  `rt_transient_*` externs are inert): tier 2 of the gate above builds and
  runs `test/fixture/transient_scope/global_text_memo.spl` (case A retains
  a dead-scope entry, case B does not) and
  `test/fixture/transient_scope/text_field_promotion.spl`.

Sibling-pattern scan (prevention): the other module-level `{text: text}`
memos in `src/compiler` are all under `10.frontend/core/interpreter/`
(`compiled_module_adapter.spl`, `load_session_cache.spl`,
`module_loader_lazy.spl`) -- the interpreter module-loader lane, not the
Stage-2 native compile path that `bootstrap_main.spl` links. Not changed
here; left as an observation.

Still unverified (native): the Reproduce command above on a stage2 built
from current release/1.0.0, confirming `test_runner_build.log` carries no
`schema=` owner text. That is the only thing standing between
`fix-implemented-verification-pending` and `fixed`.
