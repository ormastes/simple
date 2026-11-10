# HIR callable-dep diagnostic fabricates name/position for bare `fn()` types
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Filed:** 2026-08-29 (debug_service_v1 Opus verification)
**Status:** OPEN

Native build reports `unresolved name: signal|mcp_run_argv|mcp_server_init`
at (file,line,col) triples that do not match file content. Root: the bare
`fn()` callable type in `std.nogc_sync_mut.io.signal_stubs.signal_handler_install`
— log line `[hir-callable-dep-origin-unresolved] owner=...signal_stubs dependency=fn`
— is reported with a fabricated name/location against unrelated modules
(src/app/mcp/main.spl:24:8 etc.). One defect, not three; no import binding can
fix it; needs the HIR callable-dependency diagnostic (and possibly resolution
of bare `fn` types) fixed in the compiler. Last blocker for a clean native MCP
build (10 error lines). Evidence: $SCRATCHPAD/VERIFY_debug_service.md §3.


---

## Addendum 2026-11-11 — lane compiler2 — verdict BLOCKED (native-build proof required)

Triage-first pass, batch 2. This row's only honest end-to-end proof is the
heavy entry-closure **native MCP build** — exactly the class of build this
lane's mandate says NOT to run. It was not run.

**Why no lighter proof exists here.** The defect is the HIR callable-dependency
diagnostic fabricating a (file,line,col) for a bare `fn()` dependency during
the native build of `src/app/mcp/main.spl`. The natural lighter proxy,
`bin/simple check src/app/mcp`, was attempted time-boxed (260s) on the
refreshed seed and **did not complete** (exit 124) — so it yields no verdict
either. The dedicated HIR callable-dep unit specs in
`test/01_unit/compiler/hir/` (`callable_signature_owner_imports_dependency_spec`,
`callable_generic_binder_not_owner_dependency_spec`, `hir_module_callable_index_spec`,
…) cover *related but distinct* mechanisms (owner-side type-name gaps, generic
binder `T`, module-callable index perf) — none pins the bare-`fn()`
fabricated-position scenario of this row, so they are not a substitute repro.

**Evidence lean (unconfirmed):** substantial HIR-callable-dependency work landed
after the 2026-08-29 filing and is present in HEAD, e.g. `7623d26baeb4`
(bind facade-imported callables to the declaring owner), `f657be3985da` /
`4a710c9ce465` (generics-cov2 HIR callable + module_callable_types MC/DC),
`22a841b1a579` (skip generic binders as owner deps), and `1aa81cac8c6` (the
owner-naming advisory itself). The row is *plausibly* superseded, but with no
seed-smoke-able repro and no isolated fixing commit, that is a hypothesis, not
a verdict.

**Exact command needing grant (run, then grep the build log for
`unresolved name: signal|mcp_run_argv|mcp_server_init` and for
(file,line,col) triples that do not match file content):**
```
SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe bin/simple.exe native-build \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/mcp/main.spl --strip \
  --output build/bootstrap/mcp-package/simple_mcp_server
```
A clean build (no fabricated-position `unresolved name` lines) => SUPERSEDED;
reproduction => LIVE (fix in `src/compiler` HIR callable-dep position
attribution). Evidence attempt log: `build/review/p3c2-mcp-check.log` (timed
out, inconclusive).

**Cycles:** 0 (no fix attempted — verification blocked, not a fix cycle).
