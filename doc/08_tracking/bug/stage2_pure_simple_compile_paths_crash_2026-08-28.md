# Stage2 pure-Simple compiler: `compile` and single-file `native-build` crash or fail on ordinary modules

- **Date:** 2026-08-28
- **Binary:** `build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple` from the goal-bootstrap lane (tree 887507a3921, seed-compiled)
- **Component:** 10.frontend `_FlatAstBridge` / parse, 80.driver single-file lowering (loader + driver owners; recorded here by the middle/back-end perf lane because they block every fixed-input workload)
- **Status:** OPEN

All runs: `SIMPLE_BOOTSTRAP=1`, stage-3 lane env (`SIMPLE_FRONTEND_CACHE=0`,
`SIMPLE_STAGE3_STREAMING_SURFACES=1`, `MALLOC_ARENA_MAX=2`, ...), cwd = release
tree bb87306b64c, `--threads 1`.

| workload | result |
|---|---|
| `compile src/compiler/00.common/config.spl --format=smf` | SIGSEGV (rc 139) after `hir 4/4`; with `SIMPLE_COMPILER_TRACE=1` the last lines are `[flat-bridge] decl:start 5 tag 9` (`10.frontend/_FlatAstBridge/module_assembly.spl:268`) |
| same, without `SIMPLE_FRONTEND_CACHE=0` | SIGSEGV earlier, at `parse 0/4 ... file:start` |
| `native-build _perf_bis_struct.spl` (one `struct P: a: i64` + main) | SIGSEGV after `hir 1/1` |
| `native-build _perf_bis_usestd.spl` (`use std.nogc_sync_mut.io_runtime.{time_now_monotonic_ms}`) | SIGSEGV after hir |
| `native-build _perf_bis_gvar.spl` (module-level `var g: i64 = 0`; `g = g + 1` in main) | rc 1: `bootstrap MIR lowering: assignment target has no local binding` |
| `native-build _perf_bis_garr.spl` (`var g: [i64] = []`; `g = g.push(1)`) | same error |
| `native-build _perf_bis_extern.spl` / `_perf_bis_twofn.spl` / hello world | OK |
| `native-build src/app/cli/bootstrap_main.spl` (the exact stage-3 argv, threads 1 and 32) | SIGSEGV at `parse 1/717` on `src/compiler/driver/driver.spl`, 54 s in, deterministic (2/2) |
| same argv, cwd = `git archive` of 887507a3921 (the tree stage2 was built from) | parses all 717 files (587 s single-thread), then HIR poisons every module with `ambiguous explicit callable dependency` / `unresolved name` errors (3994 errors by module 57) — likely a project-root/prelude resolution difference of the archive cwd, not a compiler defect; recorded so nobody re-derives it |

Consequences for measurement: the only fixed-input workload that runs end to
end on this stage2 is a hello world; `--entry-closure --entry X` is NOT a
pure-Simple workload — `bootstrap_main.spl:305` routes any explicit `--entry`
to `rt_native_build`, the Rust native-all backfill (objects then appear as
`native-objects-*/mod_N.o`, a Rust `native_project` naming). A tree-consistent
stage2 rebuilt by the seed from bb87306b64c (`scratchpad/s2_r1`, threads 1)
reproduces the single-file rows exactly (`struct` rc 139, `usestd` rc 139,
`gvar`/`garr` "no local binding", `extern`/`twofn`/hello OK), so these are
compiler defects in the pure-Simple single-file lowering path, not a
snapshot/tree mismatch. Only the `driver.spl` parse SIGSEGV is snapshot-vs-tree
specific (not reproduced with `s2_r1`).
