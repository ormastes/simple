# Import-triggered cross-module symbol misdispatch (interpreter lane)

Status: OPEN. Filed 2026-08-18 (goal-7 dedup tranche, agent-verified A/B repro).
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
