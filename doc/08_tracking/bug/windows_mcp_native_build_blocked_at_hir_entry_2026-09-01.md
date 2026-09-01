# Windows: MCP native build reaches HIR entry, then aborts — MIR error count still unobtainable

- **Filed:** 2026-09-01
- **Status:** OPEN (blocked on another agent's HIR-entry defect — NOT owned here)
- **HEAD:** `da0122d819b` (detached), 18866 dirty paths in a shared worktree
- **Seed:** `src/compiler_rust/target/release/simple.exe`,
  md5 `286f66b8615dce0e0da788f0550c4008` (carries the COFF `.refptr` ->
  GotPcRel fix, `04603e026ca`)

## Reproduction

```sh
S=src/compiler_rust/target/release/simple.exe
SIMPLE_NATIVE_BUILD_WORKER=1 SIMPLE_EXECUTION_MODE=interpret SIMPLE_BINARY=$PWD/$S \
  $S run src/app/cli/native_build_worker.spl \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/mcp/main.spl \
  --threads 1 --cache-dir build/mcp_probe_cache \
  --output build/mcp_probe_server.exe
```

`rc=1` after ~28 minutes of wall. Final lines:

```
[frontend-cache] hits=0 misses=100 parses=100
[bootstrap-error-count] source_idx=0 point=entry count=0
error: semantic: undefined field 'symbols': cannot access field on value of type 'bool'
```

## What this establishes

**1. `method len not found on type enum` does NOT reproduce.** Zero occurrences
across the full 1,118-line build log; `method ... not found` matches **0** lines
of any kind. The blocker as reported is not observable at this HEAD with this
seed. It is most plausibly cleared by the `any?` receiver-erasure and
`env_get` nil-guard fixes that landed 2026-08-30/09-01 (`628ac26d38d`,
`040c306da80`), but this run does not prove causation — it proves only absence.
**Scope limit — read before citing this.** The build aborts at HIR entry,
so this absence is proven only for the phases that actually RAN (parse,
surface build, HIR entry). Everything downstream of the abort — MIR lowering
included — never executed, and if the enum-len failure fires there, this run
could not have seen it. Absence up to the abort point is not absence entirely.
**Do not re-file it without first reproducing it, and do not treat it as
cleared until a build gets past HIR entry.**

**2. The MCP MIR error count is still unobtainable, and the last figure of 133
remains unsuperseded.** The build aborts at HIR entry, before MIR lowering
runs, so no MIR error population is ever produced. The only count this run
emitted is `[bootstrap-error-count] source_idx=0 point=entry count=0` — that is
an ENTRY-point count, not the MIR error count, and it must not be reported as
133's successor. Anyone citing "0" from this log is citing the wrong number.

**3. The abort is the HIR-entry blocker another agent owns.**
`error: semantic: undefined field 'symbols': cannot access field on value of
type 'bool'` is the exact defect named as separately owned. Recorded here only
as the thing encountered; **not diagnosed or attributed in this lane.**

**4. Everything before HIR entry is now green on Windows.** All 100 surface
build units completed with **0** errors, 100 parses, no crashed/terminated
units. Reaching this point at all is new: before the COFF `.refptr` fix
(`04603e026ca`) the seed could not emit a single object on Windows.

Remaining non-fatal noise, for whoever picks up the HIR-entry defect: 5
`[hir-callable-dep-origin-unresolved]` lines (`Dict` and `Option` in
`app.mcp.main_lazy_ctx_tools`, `Option` in `app.mcp.main_lazy_telemetry`),
5 `unresolved type:` lines, and two `[use-warning]`s naming `rt_env_cwd`
(`std.io_runtime`) and `BackendCompileOptions`
(`compiler.common.driver_core_types`).

## Secondary Windows defect: the worker wrapper cannot spawn its own worker

The reproduction above bypasses the wrapper deliberately. Driving `native-build`
normally fails before any compilation, even on a three-line hello world:

```sh
src/compiler_rust/target/release/simple.exe native-build hello.spl -o hello_nb.exe
# rc=127
# error: native-build worker wrapper exited abnormally (signal or wait failure,
#        code -1) before producing a binary; its process group has been terminated.
```

Emitted at `src/app/cli/native_build_main.spl:675`. The parent re-execs the
interpreter as `<simple_bin> run src/app/cli/native_build_worker.spl <args>` via
`process_run_timeout_live` (`:641`). Running that exact child command **by hand
works** — it compiles and reports a normal build outcome — so the failure is in
the parent's spawn/wait, not in the worker. `code == -1` with no `[TIMEOUT:]`
marker means the wrapper died by signal or the wait itself failed.

This is the same message as
`doc/08_tracking/bug/coverage_native_build_worker_abnormal_exit_2026-08-31.md`
(OPEN); this record adds the Windows hello-world data point and the finding
that the child command succeeds standalone.

## Unblock condition

1. Fix `semantic: undefined field 'symbols' ... on value of type 'bool'` at HIR
   entry (owned elsewhere). Then re-run the command above; MIR lowering will
   run and the error count becomes measurable for the first time.
2. Independently, fix the Windows worker-wrapper spawn so `native-build` is
   usable without hand-assembling the worker invocation.
