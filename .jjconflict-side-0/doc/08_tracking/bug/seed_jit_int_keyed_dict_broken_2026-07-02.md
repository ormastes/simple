# Seed JIT: int-keyed Dict insert/lookup broken (blocks stage2 bootstrap)

**Date:** 2026-07-02
**Component:** Rust seed JIT (cranelift path) — dict lowering / runtime dict SFFI
**Severity:** Critical — blocks stage2 bootstrap
**Status:** source fixed; focused interpreter/JIT execution pending

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

## Re-confirmation (2026-07-02, later same day)

Re-repro'd from scratch on the current seed binary
(`src/compiler_rust/target/bootstrap/simple`) with a minimal standalone
snippet (`Dict<i64,i64>`, insert 1 key, then `.has()`/`[]`/`.len()`):
JIT gives `has=false, get=7 (via ?? fallback), len=-1`; interpret gives the
correct `has=true, get=7, len=1`. Confirms the defect is still present and
is the true upstream cause — not a pure-Simple producer bug.

Also confirmed `SIMPLE_EXECUTION_MODE=interpret` around the *whole*
`native-build` invocation does **not** avoid the crash (see
`stage2_interp.log` in scratch runs) — consistent with the driver treating
that env var as only the initial/default tier (`exec_core.rs:73-74`)
rather than a hard interpret-only switch; hot MIR-opt functions can still
get JIT-promoted mid-run and hit the same broken dict path.

### Mitigation applied (not a full fix)

Added defensive `if local.?:` / `if local.? and ...:` guards around the
`Copy(local) | Move(local)` extraction sites in
`optimize_write_coalesce` (`src/compiler/60.mir_opt/_OptimizationPasses/io_passes.spl`,
both the scan loop and the post-coalesce rewrite loop) so a
corrupted/nil operand is skipped instead of crashing the whole
`native-build`. This is a stopgap only — `local` is never legitimately nil
for a real `Copy`/`Move` operand, so skipping means the affected
write-coalescing opportunity is silently dropped. The many other
`Dict<i64,_>` call sites in this file and in `src/compiler/50.mir/` remain
exposed to the same underlying corruption and can surface as the "next"
crash elsewhere. Real fix must land in the seed's Cranelift JIT dict
codegen/`rt_dict_*` SFFI (or the driver's tiering must honor
`SIMPLE_EXECUTION_MODE=interpret` as a hard override), not in downstream
pure-Simple guards.

With the guards applied, the `undefined field 'id'` crash is gone and
`native-build` for `bootstrap_main.spl` progresses further, now failing
at a distinct, later point:

```
error: AOT compile error in std.io_runtime: MIR module has no functions
error: native-build worker exited with code 1 (no binary produced).
```

Still no stage2 binary produced. This next failure is a separate issue
(tracked separately, not chased further here) and may itself be another
symptom of the same underlying int-keyed Dict corruption (e.g. a
function-list/module dict losing entries).

## Resolution status (2026-07-15)

The shared runtime dictionary hashes and compares tagged values. Current MIR
index writes and reads box integer keys, and builtin `get`/`set`/`has` call
paths use the same value-wrapping owner before reaching `rt_dict_*`; the
original insert/lookup representation mismatch is therefore source-fixed.
A focused `interp_jit` driver regression now inserts an integer key and checks
`has`, `len`, and lookup through the real backend path. Its execution remains
pending a runnable Rust test artifact, so no JIT PASS is claimed.
