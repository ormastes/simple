# Seed JIT lane does not check unprovided braced `use` names (2026-11-27)

**Status:** fixed (2026-11-27)
**Area:** Rust seed, HIR lowering / Cranelift JIT entry lane
**Found by:** `scripts/check/check-undefined-import-run-exit-code.shs` (unreached shape)

## Symptom

The interpreter module loader now rejects `use m.{x}` as a hard semantic error
when `m` does not provide `x`. It does this in `module_loader.rs`,
`check_unprovided_use_names`. The JIT entry lane resolves imports on its own
path and never runs that check.

When the absent name is used only in a function that is never called, the
program compiles under JIT, runs, prints its output and exits 0:

```
use std.common.use_warning_probe.{uw_probe_zzz_absent}
fn never_called() -> i64:
    return uw_probe_zzz_absent(1)
fn main():
    print("REACHED")
```

Running it with seed `simple-local-20261127a.exe` prints `REACHED` and exits 0.
When the absent name is on the executed path, JIT fails with
`unresolved external symbol` and demotes to the interpreter. The interpreter
then raises the hard error. So that case is caught, but only indirectly.

## Expected

The same rule applies in every lane: an unprovided braced use name is a
compile error before anything executes.

## Fix direction

Run the provided-set check from the HIR import resolution path too. It should
use the same `ProvidedNames` surface, the same host-gate opacity
(`source_is_host_gated`) and the same message, so the two lanes cannot
disagree.

## Gate

`check-undefined-import-run-exit-code.shs` stays strict on this shape. It
reports `FAIL ... unreached-undefined-import-exits-0` until the fix lands. The
gate is not wired into the push tier.

## Resolution (2026-11-27)

`pipeline/module_loader.rs` `load_module_with_imports_internal`, `Node::UseStmt`
arm, now calls `interpreter_module::check_unprovided_use_in_resolved_module`
(new, `interpreter_module/module_loader.rs`) once the `use` resolves to a file.
It builds the provided set from the parse in the shared source cache with the
same `collect_provided_names`, then runs `check_unprovided_use_names` wrapped in
`unprovided_use_outcome`, so message, default `[use-warning]` (deduped by
`use_warning_seen`) and `SIMPLE_STRICT_USE=1` hard error are identical.

HIR-side subset (nothing is evaluated, so the exports table is empty): names
re-exposed by the module's own non-glob `use` lines are added to the set; enum
variants/methods come from the parsed enums. Left unchecked, like the
interpreter: opaque export-use glob/bare, glob-`use` and host-gated surfaces
(`surface_incomplete`); additionally modules containing `MultiUse` /
`CommonUseStmt`, and `__init__.spl` package targets (sibling-merged surface).
In default mode the interpreter fallback may repeat the warning when the
importer path text differs (dedup key includes the path).

Verified: `check-undefined-import-run-exit-code.shs` PASS (4 fixtures, incl.
unreached shape), `check-use-warning-oracle-deployed.shs` PASS, container sweep
54/54 on both seed 27e and 27f.
