# rv64gc reland removed `core64_step` but left its export and 4 spec call sites dangling

- **Date:** 2026-07-21

> ## 2026-08-17 — REPRODUCED, still LIVE (not fixed by this lane)
>
> Confirmed live by content **and** by execution. `grep -rn "fn core64_step"
> src/lib/` returns **zero** hits; `Core64StepResult` is likewise undefined.
> `git log -S"fn core64_step"` on `core.spl` is empty, so this symbol was never
> defined — it is a spec written against an API that does not exist, not a
> regression that removed one.
>
> Surviving call sites: `test/01_unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl`
> imports both symbols at line 42 and calls `core64_step` at lines 323 and 330.
> (The `.spipe_wrapped_entry_*` path named in the original triage row no longer
> exists; the live file is the unwrapped one above.)
>
> **RED evidence** — `bin/simple test test/01_unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl`:
>
> ```
> semantic: function `core64_step` not found
> [use-warning] 'Core64StepResult' is named in `use std.hardware.rv64gc_rtl.core.{...}` but module '.../src/std/hardware/rv64gc_rtl/core.spl' does not provide it
> [use-warning] 'core64_step' is named in `use std.hardware.rv64gc_rtl.core.{...}` but module '.../src/std/hardware/rv64gc_rtl/core.spl' does not provide it
> Results: 35 total, 32 passed, 3 failed
> ```
>
> Note the failure mode: the unresolved import is only a **warning**, and the
> module still ran 32 green examples. Exactly the silent-degradation shape this
> sweep targets. (`src/std` is a symlink to `lib`, so the resolved path is the
> same file — not a second copy.)
>
> **Deliberately NOT fixed here.** The obvious repair is a thin one-cycle
> wrapper composing the existing verified primitives —
> `core64_combinational(state, imem, dmem_rdata, state.rf)` then
> `core64_update(state, imem, comb, rf.reg_10, rf.reg_11)` — returning a
> `Core64StepResult`. But `SocBus64` (`pkg.spl:167`) is a stub carrying a single
> `data: i64` with no fetch path, so the instruction-fetch semantics the spec
> intends cannot be inferred from source. Guessing them would put unverifiable
> CPU-step semantics into a shared RTL library. Needs an owner who can validate
> against the RV64GC reference. The 3 failing examples are all `core64_step`.
- **Status:** partially fixed (Lane FF, 2026-07-22) — see "Update" below;
  dangling `__init__.spl` export removed, 2 of 4 spec call sites already
  self-resolved, 2 remain open.
- **Severity:** high (rv64gc_rtl package cannot compile once a working test
  runner executes it; currently masked by the stale-seed runner outage)
- **Area:** `src/lib/hardware/rv64gc_rtl/__init__.spl:48` + 4 spec files
- **Introduced by:** `81d904de4b5` ("surgical reland of session-unique work
  onto main tip")

## Update (Lane FF, 2026-07-22, verified in worktree at tip `f4a2165f389`)

- `__init__.spl` no longer exports `core64_step` (nor the other dangling
  `core.spl` symbols confirmed to have zero definitions/consumers tree-wide:
  `CorePorts64`, `core64_ports`, `Core64StepResult`) — grep for all four across
  `src/` and `doc/` returns 0 hits outside this doc.
- Of the 4 call sites originally listed, 2 have already migrated off
  `core64_step` independently of this lane:
  - `test/01_unit/lib/hardware/soc_rtl/soc_top_64_spec.spl` — now drives
    `core64_combinational` + `core64_update` (bus-protocol path), no
    `core64_step` reference remains.
  - `test/unit/lib/hardware/soc_rtl/soc_top_64_spec.spl` — same.
- 2 call sites still reference `core64_step` directly from
  `std.hardware.rv64gc_rtl.core` (bypassing `__init__.spl`, so this lane's
  export removal does not touch them) and will fail to resolve once the
  SSpec runner is unblocked:
  - `test/01_unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl:41,319,322,325,329`
  - `test/unit/lib/hardware/rv64gc_rtl/core64_integration_spec.spl:41,234,237,240,244`
- These 2 remaining files are out of this lane's file set (test/ specs, not
  the rtl `__init__.spl`/`pkg.spl`/`soc_rtl` set); fix option 1 (migrate to
  `core64_cycle`) or option 2 (shim) from below still applies to them.
- Regression check: `scripts/check/check-riscv-hardware-gates.shs` stays
  9/9 PASS after the export removal; `core64_probe`/`rvfi64_probe` (both
  import via `__init__.spl`) ALL PASS.

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
