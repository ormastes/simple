# Seed JIT: int-keyed Dict insert/lookup broken (blocks stage2 bootstrap)

**Date:** 2026-07-02
**Component:** Rust seed JIT (cranelift path) — dict lowering / runtime dict SFFI
**Severity:** Critical — blocks stage2 bootstrap
**Status:** Open

## Symptom

Under the seed's default JIT execution mode, `Dict<i64, i64>` is unusable:

```spl
var d: Dict<i64, i64> = {}
d[1] = 7
d.has(1)     # -> false   (expected true)
d[1] ?? -1   # -> 56      (garbage; expected 7)
d.len()      # -> -1      (expected 1)
```

String-keyed dicts (`Dict<text, i64>`) work correctly. Under
`SIMPLE_EXECUTION_MODE=interpret` all cases pass.

Repro: run the snippet above via
`src/compiler_rust/target/bootstrap/simple run <file>` (JIT default) vs
`SIMPLE_EXECUTION_MODE=interpret ...`.

Confirmed identical on the 2026-07-01 `target/release/simple` binary —
pre-existing, not introduced by the 2026-07-02 match-binding fixes. It was
previously masked in stage2 because execution crashed earlier on the
or-pattern binding bug (fixed in c2d4bc2c13b8) before reaching int-dict code.

## Impact on stage2

`native-build` (stage2) executes the pure-Simple compiler under mixed
JIT/interp. MIR-lowering and optimization passes use int-keyed dicts
pervasively (`value_map[local.id.id]`, `gep_base[dest.id]`,
`base_store_count[base_id]`, SSA rename maps, ...). JIT-compiled functions
silently read garbage from these dicts and construct corrupted values (e.g.
`MirOperand(Copy(nil))`), which downstream interpreter-executed code then
trips over:

```
error: semantic: undefined field 'id': cannot access field on value of type 'nil'
```

(observed in `optimize_write_coalesce`,
`src/compiler/60.mir_opt/_OptimizationPasses/io_passes.spl`, where the
`Copy(local)` payload arriving from upstream was nil).

## Likely root cause direction

Insert and lookup box/hash the i64 key inconsistently in the JIT lowering
(e.g. key boxed to a fresh heap pointer on insert, compared by pointer or
re-boxed differently on lookup), while the interpreter compares Value::Int
by value. Check `rt_dict_*` SFFI signatures vs the codegen's key-boxing at
`Index`-assignment and `.has()` call sites.

## Related fixed bugs (same failure cascade, 2026-07-02)

- c2d4bc2c13b8: or-pattern match arm bindings never initialized
  (statement-position lowering).
- expr-position match arms emitted no payload extraction at all
  (`lower_match_arms` in `hir/lower/expr/control.rs`); fixed via shared
  `build_pattern_binding_stmts`.
