# Full compiler check shows no progress for more than five minutes
## Open 2026-11-11 — LIVE (progress instrumentation landed; full-tree verdict still not bounded), keep OPEN (lane ne10; see addendum)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-21  
**Status:** Open — re-measured LIVE 2026-11-11 by lane ne10 (see addendum)  
**Command:** `bin/simple check src/compiler`

During SFFI function-pointer hardening, the required full compiler check emitted
no result or progress for 5 minutes 55 seconds and was terminated to honor the
repository runaway guard. The focused checks for every changed Simple file had
already passed. The command was run through the repository `bin/simple`, which
warned that the deployed executable is currently a Rust bootstrap seed rather
than the required pure-Simple production tool.

This is not evidence of a correctness failure in the SFFI change, but it is
also not a PASS. A follow-up should identify whether the time is spent loading
the full compiler tree, resolving duplicate modules, or checking files that are
outside the entry closure. The check should expose bounded progress and a
measured warm-run target so release verification cannot hang silently.

No retry was performed in this session.


---

## 2026-11-11 addendum — lane ne10 (P3 traverse, batch ne10)

**Verdict: LIVE — keep OPEN.** Half of this record's ask is now landed; the other
half is re-measured and still red.

- **Landed (the "bounded progress" ask):** `src/app/check/main.spl` now accepts
  `--progress <summary|count|dot|none>` and emits designed progress events —
  `event=check_phase phase=… elapsed_ms=… done=… total=… current=… terminal=…`
  per file and per phase (main.spl:63-101). This came in with
  `bc5245e0f918` via PR #7597 (`9e7e7a526edb`, 2026-11-07). So the check can no
  longer hang *silently by design* on configurations that reach the per-file
  loop.
- **Still LIVE (re-measurement, seed-smoke):** `SIMPLE_LIB=src
  SIMPLE_BINARY=$PWD/bin/simple.exe ./bin/simple.exe check src/compiler
  --progress count` on tracked seed `bin/simple.exe` build-commit `46fe8f6b6def`
  was killed by the lane at **16m23s** with **no verdict**. Across 3,698 lines of
  output: **0** `check_phase` events fired (the run never left the dominant
  parse/lint stage that precedes the per-file loop), and only **17 of 2,641**
  `src/compiler/**.spl` files ever appeared in the output. The 2026-08-21
  symptom "no result for 5m55s" therefore still reproduces in kind: release
  verification cannot get a bounded full-tree verdict from this configuration.
- **Where the time goes (this doc's follow-up question):** identical lint
  warnings from shared stdlib files repeat ~11× across the log
  (`src/lib/nogc_sync_mut/io_runtime.spl`, `src/lib/common/string_core.spl`,
  `src/lib/nogc_sync_mut/io/process_ops.spl`, …) — i.e. the same shared modules
  are re-loaded and re-warned per consumer module. That is the
  "resolving duplicate modules" hypothesis from the body, now the visibly
  dominant cost, compounded on this host by JIT demotion of the check driver to
  the interpreter (`[engine-demotion] reason=jit-compile-error … whole module
  dropped to the interpreter (expect ~100-1000x slowdown)`).
- **Measured warm-run target:** still defined only for focused files (NFR-005:
  warm focused-file `check`/`lint`/`fmt --check` p95 < 2s,
  `doc/02_requirements/nfr/pure_simple_tool_infra_hardening.md`). No full-tree
  `check src/compiler` target exists, so "more than five minutes" remains
  contractually unbounded.
- **Not retried:** per the runaway-guard rule this red measure was taken once;
  the lane did not loop it.
