# Import-triggered cross-module symbol misdispatch (interpreter lane)

Status: SUPERSEDED. Filed 2026-08-18 (goal-7 dedup tranche, agent-verified A/B repro).
Related: `duplicate_public_symbols_differing_return_types_jit_misdispatch_2026-08-09.md`
(same duplicate-symbol class, but that one is JIT-lane and needs differing
return types; this one reproduces in the interpreter via `bin/simple test` and
is triggered purely by adding an ALIASED import of a *different* function).

## Repro (verified by git-checkout A/B, 2026-08-18)

Baseline: `test/01_unit/lib/common/base_encoding/base_encoding_utf8_guard_spec.spl`
→ `Results: 5 total, 5 passed, 0 failed`.

Edit: in `src/lib/common/base_encoding/utilities.spl` (and/or
`src/lib/common/base_encoding.spl`), add ONLY:

```
use std.common.string_core.{text_to_bytes as _sc_text_to_bytes}
```

(and delegate the local `text_to_bytes` — but the trigger is the import). The
spec drops to `Results: 5 total, 1 passed, 4 failed`: `bytes_to_text([0xC3, 0x41])`
now returns `base_encoding.spl`'s `"�"`-fallback output instead of
`base_encoding/utilities.spl`'s own `"?"`-fallback that the spec imports and
expects — i.e. the SIBLING function `bytes_to_text`, untouched by the edit, is
resolved to the wrong module's same-named implementation once the import is
present. `compiler_cross_module_private_symbol_collision` warnings appear in
the same run.

## Impact

- Blocks goal-7 dedup of the `base_encoding.spl` / `base_encoding/utilities.spl`
  pair in BOTH directions (their `bytes_to_text` fallbacks legitimately differ:
  `"�"` vs `"?"`).
- General hazard: any module pair sharing public names can have resolution
  flipped by an unrelated import edit — silent wrong-answers, not errors.

## Wanted

Duplicate public symbol across modules reachable from one import graph should
be a hard diagnostic (or at minimum deterministic local-first resolution that
an added import cannot flip).

## Addendum 2026-11-11 — lane interp5 verdict: SUPERSEDED

Verdict: **SUPERSEDED** by commit `10e216d19f8c9b2dd9bf8fd24544793c6ad07caa`
(2026-11-09, "fix(resolve): ambiguous co-compiled duplicate definition is a
compile error (owner decision 6)"), an ancestor of base `b364745fdbf8`. That
change made interpreter + seed HIR/MIR resolution deterministic: a bare name
with >=2 co-compiled owners resolves by the caller's import path, else exact
arg-type match; a call that neither selects is a **compile error** — an added
import can no longer silently flip a sibling module's dispatch. This is exactly
the "deterministic local-first resolution that an added import cannot flip"
remedy this bug's Wanted section asked for. The immediate base_encoding
collision class had additionally been defused on 2026-08-21 by
`dec68f5173ff5dabcd3485e2120aaa3e15136494` (module-scoped renames,
`base_encoding_bytes_to_text` / `base_encoding_text_to_bytes`).

Seed-smoke verification (2026-11-11, lane interp5, refreshed seed
`bin/simple.exe` 2026-11-11 build, `SIMPLE_LIB=src`, `--mode=interpreter
--no-cache`):

- Baseline `test/01_unit/lib/common/base_encoding/base_encoding_utf8_guard_spec.spl`:
  5 total / 5 passed.
- Trigger edit applied exactly as filed (added
  `use std.common.string_core.{text_to_bytes as _sc_text_to_bytes}` to
  `src/lib/common/base_encoding/utilities.spl`): spec still **5 total / 5
  passed** — the SIBLING `bytes_to_text` dispatch no longer flips. Edit
  reverted after the run.
- The same run now emits owner-decision-2026-11-09 collision warnings
  describing caller-import-path resolution and no last-definition fallback.

Aside (not this bug): the regression spec named in the fixing commit,
`test/01_unit/compiler/interpreter/ambiguous_co_compiled_fn_call_error_spec.spl`,
currently errors because it reaches the now-private
`compiler.core.interpreter.eval_tables.func_table_reset` — a spec-maintenance
gap, recorded here for the owning lane.
