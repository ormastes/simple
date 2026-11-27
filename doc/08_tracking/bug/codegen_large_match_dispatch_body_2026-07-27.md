# Codegen fails on very large function body: _dispatch_function (236-arm match, 2497 lines)

- **Date:** 2026-07-27
- **Lane:** stage4 native-build (cranelift), full-CLI closure
- **Status:** RESOLVED for the stage4 blocker (workaround 2 landed; see 2026-11-25 note below) — the compiler-side scalability item (fix 1, large string-match lowering) remains a separate open program

## Symptom
`native-build` of `src/app/office/sheets/formula.spl` fails:
```
codegen: Module error: 1 function body/bodies failed to compile: [_dispatch_function];
set SIMPLE_ALLOW_STUB_FALLBACK to emit empty stubs instead (unsafe)
```
`_dispatch_function` (formula.spl:4270-6767) is a single 2497-line function whose
body is one `match canonical_name:` with **236 quoted string arms** (Excel
function dispatch). It also first hit a 300s per-file compile TIMEOUT before the
codegen error surfaced (raised to 900s to get past the timeout).

## Assessment
Per project rule "Compiler auto-optimizes patterns — don't make users rewrite for
perf; fix it in the compiler": a 236-arm match SHOULD compile. This is a codegen
scalability limit on large function bodies / large string-match lowering, not a
user error. Regression window: grew with `15b03323ee feat(office): add full-size
Calc TUI UI access`.

## Two fixes
1. **Proper (compiler):** make codegen handle large match/function bodies (chunked
   lowering, or lower a big string-match to a table/hash dispatch instead of a
   linear IR chain). Codex/compiler territory.
2. **Workaround (source, to unblock deploy):** split `_dispatch_function` into
   category sub-dispatchers (math / stats / text / lookup / logical …), each a
   separate `fn` with a manageable arm count, called in sequence. Preserves exact
   behavior; gets each body under the codegen limit. Being applied to unblock the
   stage4 deploy while the compiler fix is pending.

## Fleet verification note (2026-11-25, worktree wt-p2w1-ae, branch work/p2w1-ae-20261125)

Verified at `origin/release/1.0.0` HEAD (`38265c7f249`) by code inspection:

- Workaround 2 (split into category sub-dispatchers) is LANDED:
  `src/app/office/sheets/formula.spl:4287-4303` — `_dispatch_function` is now a
  17-line router over six partitions `_dispatch_function_0` …
  `_dispatch_function_5` (bodies at lines 4305, 4580, 4913, 5346, 5923, 6427;
  largest partition ≈ 580 lines, well under the 2497-line failing body). The
  split landed as "perf: partition formula dispatch without changing function
  arms" (e.g. `d738b7846e6`, transplanted by `88aac2ffe28`).
- Therefore the "blocks stage4 full-CLI build (last remaining compile
  blocker)" claim in the header is stale: the file no longer contains the
  236-arm single-body match that tripped the codegen limit.
- Compilation verification is environment-blocked on this host (no admitted
  pure-Simple binary; the pinned Rust seed rejects `@representation_boundary`
  decorators repo-wide at HEAD, and `native-build` of the full closure needs a
  bootstrap-scale build). Closure is on source-shape evidence: the failing
  construct no longer exists.
- Fix 1 (compiler-side: lower large string-match to table/hash dispatch)
  remains an open compiler scalability program, tracked independently of this
  ledger row; it is not a P2 bug fix for this lane.

Status updated: stage4 blocker RESOLVED via the documented workaround.
