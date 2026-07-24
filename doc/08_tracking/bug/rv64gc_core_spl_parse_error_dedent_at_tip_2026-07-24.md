# rv64gc_rtl/core.spl fails to parse at tip — rv64gc core unloadable, rv64 ISA probe blocked

- **Date:** 2026-07-24
- **Status:** open
- **Severity:** high (the entire `rv64gc_rtl` package is unloadable; any spec,
  probe, or tool that imports it fails at parse time)
- **Area:** `src/lib/hardware/rv64gc_rtl/core.spl`
- **Introduced by:** `4d10f1614b0` ("feat(riscv): add protected rv32 rv64
  generated RTL pipeline"), which restructured `core.spl` (`@@ -26,367 +26,40 @@`
  — 367 lines replaced by 40; `CoreState64` + much core logic moved into the new
  protected-core / generated-RTL structure). The restructure left a parse error.
- **Owner:** the session driving the `4d10f1614b0` protected-RTL restructure
  (do NOT fix blind — it is actively in flight; a blind edit risks clobbering
  their next push, per the W2-C / core64_step lesson).

## Reproduce (with a WORKING compiler — the bootstrap seed, since the deployed
## bin/simple silently no-ops, see below)

```
src/compiler_rust/target/bootstrap/simple run \
  test/01_unit/lib/hardware/isa_conformance/rv64_isa_conformance_probe.spl
```

Result:
```
error: compile failed: parse: in ".../rv64gc_rtl/core.spl":
  Unexpected token: expected expression, found Dedent
```

The rv32 counterpart is clean — `rv32_isa_conformance_probe.spl` runs green
(18 PASS / 0 FAIL) on the same seed, so this is specific to `rv64gc_rtl/core.spl`.

## Impact

- `scripts/fpga/difftest_isa.shs` Stage 1 (directed ISA conformance) cannot run
  the rv64 probe → the goal-aligned "verify RTL against `.spl` semantics"
  signal is dark for RV64.
- Note: a prior read-only audit (parallel-agent plan, Wave-2 L2) reported the
  rv64gc `.spl` datapath as "fully wired." That audit read the source but did
  not **compile** it, so it missed that the file does not parse. Lesson: an
  audit that claims a module works must compile-load it, not just grep it.

## Related

- `doc/08_tracking/bug/bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17.md`
  — the deployed `bin/simple run` is itself a **silent no-op / false green**
  (prints `seed sibling not found, skipping delegation` and exits 0 without
  executing; still reproduces 2026-07-24). That is why this parse error was not
  caught earlier: nobody could run the probe on the deployed binary, and the
  binary's exit-0 no-op made the harness look green.
- `scripts/fpga/difftest_isa.shs` now has a fail-closed guard: a probe that
  emits zero PASS/FAIL/XFAIL/XPASS/BLOCKED results is treated as a HARD FAILURE
  (never PASS), so both the no-op binary and this parse error now surface
  instead of false-greening.
