# rv64gc reland removed `core64_step` but left its export and 4 spec call sites dangling

- **Date:** 2026-07-21
- **Status:** open
- **Severity:** high (rv64gc_rtl package cannot compile once a working test
  runner executes it; currently masked by the stale-seed runner outage)
- **Area:** `src/lib/hardware/rv64gc_rtl/__init__.spl:48` + 4 spec files
- **Introduced by:** `81d904de4b5` ("surgical reland of session-unique work
  onto main tip")

## Facts (verified at tip `81d904de4b580aecbc002c218563e1eb29077ea4`)

- `core.spl` no longer defines `core64_step` (0 hits) — the reland replaced it
  with the full bus-protocol `core64_cycle(state, request_ready,
  response_valid, ...)` (line ~713). That replacement itself is the *right*
  direction: it closes the audited one-seam disconnect
  (`doc/03_plan/hardware/riscv/riscv_unification_parallel_agent_plan_2026-07-21.md`,
  Wave 1 results) with the complete July-18-lineage implementation.
- But `__init__.spl:48` still does `export core64_init, soc_bus64_init,
  core64_step` — a dangling re-export.
- Callers still referencing `core64_step`:
  - `test/01_unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl`
  - `test/unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl`
  - `test/01_unit/lib/hardware/soc_rtl/soc_top_64_spec.spl`
  - `test/unit/lib/hardware/soc_rtl/soc_top_64_spec.spl`
- Also still open at tip: `src/lib/hardware/soc_rtl/soc_top_64.spl:91` does
  `out.core.pc = out.core.pc + 4` — the SoC tick bypasses the core entirely
  (tracked as lane W2-D in the parallel-agent plan).

## Why it is masked today

The deployed self-hosted binary is a stale seed whose test runner hangs /
executes no examples
(`doc/08_tracking/bug/deployed_seed_test_runner_init_hang_2026-07-17.md`), so
nothing currently compiles these specs. The moment the runner is redeployed,
every rv64gc spec goes red on an unresolved symbol instead of on real
behavior.

## Fix options (owner: the session driving the `core64_cycle` reland)

1. Migrate: update `__init__.spl` and the 4 specs to drive `core64_cycle`
   (preferred — the specs then exercise the real bus protocol), or
2. Shim: reintroduce a thin `core64_step(state, bus)` wrapper over
   `core64_cycle` for legacy callers. A reviewed, behavior-probed single-cycle
   wiring diff (superseded lane W2-C) exists as reference in the session
   scratchpad (`w2c/` safety copies), but note its `SocBus64` field additions
   were NOT landed, so it does not apply cleanly to tip.

Deliberately NOT fixed inline here: the owning session is actively pushing
this lane; a blind fix risks the next reland clobbering or double-defining
the symbol.
