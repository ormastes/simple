# `native-build` fails after a clean HIR with `type mismatch: cannot convert enum to int`

- **Date:** 2026-09-01
- **Status:** OPEN — newly reachable, not yet diagnosed
- **Lane:** goal item 2, x86_64 WM host-Vulkan pixel evidence (blocks the daemon build)

## Symptom

With the `self`-bound-to-bool interpreter defect fixed
(`doc/08_tracking/bug/hir_register_imported_symbol_inner_self_bound_to_bool_2026-09-01.md`,
commit `f861a2e42e7`), the 12-module reproducer now clears HIR completely
(`hir 12/12`, 0 `[field-access-error]`, 0 `[self-slot-write]`) and then fails:

```
error: semantic: type mismatch: cannot convert enum to int
[ERROR] phase 3 FAILED
BUILD_RC=1
```

No output binary is produced.

## Why this is new, not a regression

No native-build under this flag set had ever got past `hir 0/N`, so nothing
downstream of HIR had ever executed. This error is **newly reachable**, not
newly introduced. It was not observable before the `self` fix.

## Explicitly NOT the other lane's defect

`native-capsule-receipt-invalid` does **not** appear anywhere in this run's log.
The capsule/receipt path is not reached; this failure is earlier. The
capsule-receipt defect remains separately open and owned elsewhere.

## Reproduce (~9 min)

`sh build/reprobuild.sh` in the worktree (entry
`src/app/repro_iowner/i_owner.spl`, 12-module closure). Always set
`SIMPLE_DEBUG_FIELD_ACCESS=1` — the script does. The error is printed inside the
`[native-build] BEGIN/END PRESERVED DIAGNOSTICS` block, so diagnostics transport
is working on this path.

## Next step

The error carries no module/function attribution. The same technique that cracked
the `self` defect applies: find the emitting site in the Rust seed and have it
name the receiver/expression and the enclosing frame (the `[field-access-error]`
branch in `interpreter/expr/calls.rs` is the worked example, and it now prints
`locals=` / `env_keys=` under `SIMPLE_DEBUG_FIELD_ACCESS`).
