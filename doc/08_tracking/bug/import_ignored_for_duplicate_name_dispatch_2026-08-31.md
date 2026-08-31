# An explicit import can execute another module's same-named function

**Date:** 2026-08-31
**Status:** DIAGNOSED; candidate fix committed but **BEHAVIOURALLY UNVERIFIED**
**Severity:** correctness — silent wrong-body execution, not an error

## Symptom (measured, real)

`src/compiler/70.backend/backend/llvm_native_link_orchestrator.spl` imports
`host_os` and `host_arch` from `std.platform`. Those implementations are
env-first and cannot return empty. At runtime the calls executed
`std.io_runtime`'s **same-named** uname-based copies instead, which shell out
to `/bin/sh -c "uname -s"`. Windows CreateProcess has no `/bin/sh`, the spawn
fails, and both returned `""`.

Captured at the failing site:

```
hosted_os=[] hosted_arch=[] OSenv=[Windows_NT] PA=[AMD64]
```

The environment variables were present and correct — the wrong function
bodies ran. A direct `process_run("uname", ["-s"])` in the same process
worked, pinning the failure to the `/bin/sh` path inside io_runtime's copy.

Downstream effect: the native link aborted with
`unsupported on host architecture '' for OS ''`.

## Mechanism

Two defects compose:

1. **Tie-break by registration order.** `use m.{f}` records an owner binding
   (`record_flattened_import_binding` / `record_import_binding`), but a bare
   CALL of `f` never consulted it when the name resolved at all.
   `select_overload` broke same-score ties by FIRST REGISTRATION unless the
   caller's own module declared a candidate — so an import from module A
   silently executed module B's body whenever B registered first.

2. **Glob facades recorded no edge.** The flattened-import expansion sees only
   the source module's GLOBALS and already-recorded bindings. A facade's plain
   functions are in neither, so `src/lib/platform.spl`
   (`export use nogc_sync_mut.platform.*`) recorded **no** binding for
   `host_os`, and an importer's `use std.platform.{host_os}` dead-ended at the
   facade.

## Candidate fix (committed, NOT verified)

- Record the glob edge itself under a `"*"` key so a per-name miss can be
  followed to the declaring module.
- Add explicit-import dispatch for bare calls of a multiply-defined name,
  selecting by module OWNER (never by bare name), through the same two steps
  as the existing aliased-import fallback: owner-mangled symbol, then
  owner-matched candidate.
- `SIMPLE_DEBUG_DUPDISPATCH` gates diagnostics; default off, zero cost unset.

**What is NOT established:** the change compiles clean (`cargo check
--release --bin simple`, warnings only) and is purely additive (+124/-0), but
it has NOT been shown to fix the measured case, and no regression run has been
done. This is core overload resolution — a wrong fix here changes which
function every ambiguous call in the tree executes. Treat as a diagnosis with
an attached candidate, not as a resolved defect.

## Workaround already in place

`c4d6d497edf` hardened `io_runtime`'s copies so they also work on Windows,
which fixed the SYMPTOM. The dispatch defect is the real bug and remains.

## Verification still owed

1. A minimal fixture: two modules exporting one name with observably
   different behaviour, a third importing from a specific one; assert which
   body runs.
2. The real case: `host_os`/`host_arch` from the orchestrator return non-empty
   on Windows *without* relying on the io_runtime hardening.
3. A meaningful regression run with before/after counts, since this touches
   dispatch for every duplicate name in the tree.
