# SFFI authority census omits ambient raw calls

**Status:** Open
**Observed:** 2026-08-24

## Evidence

`src/compiler/70.backend/backend/common/mir_text_codegen.spl` directly calls
`rt_env_get("SIMPLE_ALLOW_UNLOWERED_MIR")`, but has neither a local extern
declaration nor an explicit import from a path containing `sffi`. The current
`scripts/audit/sffi-call-authority-census.shs` intentionally builds its raw-name
set only from those two source patterns, so its full call-site output contains
no row for this executable boundary.

The measured headline total of 21,267 raw calls is therefore a lower bound, not
an authoritative inventory. Adding a duplicate extern declaration merely to
satisfy the scanner would violate canonical ownership and hide the defect.

## Required fix

Generate the authoritative inventory from resolved HIR symbol identity after
imports, aliases, re-exports, aspects, and generated declarations are applied.
Each call row must identify its declaration/provider owner and distinguish a
foreign symbol from a pure-Simple function that happens to use an `rt_*` name.
The source scanner may remain a fast migration smoke test, but its report and
ratchet must label coverage as partial until reconciled against the HIR output.

## Acceptance

1. The ambient `mir_text_codegen.spl` call appears exactly once.
2. A local pure-Simple `rt_*` function is not classified as foreign.
3. Aliased and re-exported extern calls retain their canonical provider owner.
4. Interpreter, JIT, native, dynload, and SimpleOS inventories consume the same
   resolved contract ID.
5. The generator remains linear in resolved calls plus declarations and adds no
   per-call runtime lookup or allocation.
