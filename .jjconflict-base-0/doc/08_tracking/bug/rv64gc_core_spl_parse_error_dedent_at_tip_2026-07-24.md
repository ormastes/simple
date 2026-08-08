# rv64gc_rtl/core.spl fails to parse at tip — rv64gc core unloadable, rv64 ISA probe blocked

- **Date:** 2026-07-24
- **Status:** parse FIXED (see resolution below); a separate seed-lowering
  limitation now blocks full rv64 probe execution.
- **Severity:** was high (the entire `rv64gc_rtl` package was unloadable); the
  parse blocker is resolved — the package now parses.

## Resolution (2026-07-24)

Root cause was **two multi-line boolean conditions split across lines without
the required wrapping parens** (Simple grammar rule, `.claude/rules/language.md`:
"Multi-line booleans — wrap in parentheses"). The parser hit the dedent after a
trailing `and` → "expected expression, found Dedent". The underlying parser
defect (unparenthesized multi-line boolean used as an `if`/`else if` **header**
desyncs INDENT/DEDENT tracking; the same shape in a `val` binding or bare return
expression is safe) is tracked in
`doc/08_tracking/bug/parser_trailing_operator_line_continuation_2026-07-13.md`;
parenthesizing is the documented `.spl`-level workaround. Both sites fixed by
wrapping the condition in `( … )`:
- `src/lib/hardware/rv64gc_rtl/core.spl:430` — `if (core64_fp_config_allows(…) and`
- `src/lib/hardware/rv64gc_rtl/rvfi_base.spl:128` — `if (not prev_trap and …`

Verified on the working bootstrap seed (`src/compiler_rust/target/bootstrap/simple`;
the deployed `bin/simple` is a broken no-op): the package parses, no `Dedent`
error remains.

### Remaining (separate, NOT a parse error)

Once parsed, the rv64 ISA probe hits a seed HIR-lowering limit:
`Unknown variable: lsu64_load while lowering core64_combinational` /
`variable 'hardware' not found`. This is the **bootstrap seed not supporting the
`@hardware` decorator** (rv64 `core.spl` has one `@hardware` fn,
`core64_combinational_length`; the rv32 core has zero, which is why the rv32 ISA
probe runs clean at 18/18). Not a `.spl` bug and not fixable in `.spl` — it needs
a current self-hosted compiler (the deployed one being a broken no-op is the
real blocker, tracked in
`bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17.md`).
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
