# private_symbol_collision — state

**Status:** investigation COMPLETE. No fix applied (compiler lanes live).
**Date:** 2026-07-28

## Verdict
- Collision mis-dispatch is REAL and SILENT on the **JIT** (default engine),
  exit 0, output line vanishes. **Interpreter is correct.** Reproduced in
  `build/symcol_probe/r_{a,b,main}.spl`.
- Root cause: `private_dup_overloads` keys on PARAM TYPES ONLY
  (`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs:1234-1260`), so
  return-type-only collisions get no `$dupN` variants → last-write-wins.
- Secondary: `candidates.last()` fallback at
  `lowering_expr_call.rs:557-577` is a deliberate silent guess.
- Flattening requires **wildcard `use m.*`**; `use m` and `use m.f` do not
  collide (negative controls in the same dir).

## The four sshd names: currently BENIGN
All four differ in PARAM types → `$dupN` mangling applies → exact-match
resolution works. All 11 `_hex_digit` bodies AGREE on every in-range input
(14→"e", 15→"f" both directions). So collision is **NOT** a second cause of
the `f`-read-as-`e` hex bug; the seed-parser attribution stands.

Residual risk: all candidates of each name share one arity (`_hex_digit` 1,
`_u8_at` 2, `_cswap_pair`/`_ladder_step` 5), so the `by_arity` tiebreak can
never fire — they rely solely on exact param-type match.

## Next (proposed, not done)
1. `src/os/crypto/curve25519_smalllimb.spl` — rename `_u8_at`→`_u8_at_i`,
   `_cswap_pair`→`_cswap_pair_limb`, `_ladder_step`→`_ladder_step_limb`.
   One file, kills 3 of 4 warnings.
2. Compiler: add return type to the dup signature key (C1) + make the
   `candidates.last()` fallback a hard error (C2).

## Artifacts
- `doc/08_tracking/bug/private_symbol_collision_sshd_four_names_2026-07-28.md`
- `build/symcol_probe/`
