# An explicit import can execute another module's same-named function

**Date:** 2026-08-31
**Status:** VERIFIED 2026-09-01 — candidate fix `b0229d663b1` is **INSUFFICIENT**:
confirmed correct on a minimal single-hop fixture, confirmed to NOT fix the
real `host_os`/`host_arch` case (a corrupted `"*"` glob-edge binding for a
more complex facade shape). PR #204 (merged `787b011c220`) is a related but
orthogonal fix (native MIR codegen, different-signature collisions only) and
does not close this bug either. See Update 2026-09-01 below. Do not push
`b0229d663b1` as a resolution of this bug.
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

## Update 2026-09-01 — verified: candidate fix WORKS on a simple fixture, FAILS on the real case

**Relationship to PR #204 (`fix(mir): public same-name functions silently
dispatched to the wrong body`, merged `787b011c220`):** that fix is
orthogonal and does NOT resolve this bug. It patches
`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs`
(`private_dup_overloads`), which is the **native-codegen (MIR) direct-call**
path, not the **interpreter's** `evaluate_call` that this bug and its
candidate fix (`b0229d663b1`) touch. It also only disambiguates by
**arg-type signature** (`m1.pick(i64)` vs `m2.pick(bool)`); its own doc,
`doc/08_tracking/bug/cross_module_public_symbol_collision_wrong_dispatch_2026-08-31.md`,
lists "same-signature collisions" as explicitly **still open**. `host_os()`
and `host_arch()` are zero-arg in every copy — same signature everywhere —
so #204 cannot and does not touch this case even if it later reaches the
interpreter.

**Minimal fixture (built, run, reverted — not committed as product code):**
two library modules under `src/lib/` mirroring the real shape:
`zzdd_impl_a.spl` (`pub fn zzdd_pick() -> text: return "A"`), a glob facade
`zzdd_a.spl` (`export use zzdd_impl_a.*`, mirroring `src/lib/platform.spl`'s
`export use nogc_sync_mut.platform.*`), `zzdd_bimpl.spl`
(`pub fn zzdd_pick() -> text: return "B"`), and an explicit-list facade
`zzdd_b.spl` (`export use zzdd_bimpl.{zzdd_pick}`, mirroring
`src/lib/io_runtime.spl`). An importer did `use std.zzdd_b` (whole module,
registers B) then `use std.zzdd_a.{zzdd_pick}` (explicit import of A) and
called `zzdd_pick()`.

- **Seed built from before `b0229d663b1`** (deployed `bin/simple.exe`,
  2026-08-24, genuinely predates the fix): prints `B` — confirms the
  misdispatch is real and reproducible outside the orchestrator.
- **Seed rebuilt from `main` at `528ca4b88a9`** (candidate fix present):
  prints `A` — the explicit import wins. `SIMPLE_DEBUG_DUPDISPATCH=1` trace
  confirms `import_bound_candidate` walked the facade's `"*"` glob edge from
  `zzdd_a.spl` to `zzdd_impl_a.spl` and selected its `zzdd_pick`.
  **On this single-hop fixture the candidate fix is verified correct.**

**Real case (`host_os`/`host_arch`, same import shape as
`llvm_native_link_orchestrator.spl` lines 22 and 30 —
`use std.platform.{host_arch, host_os, is_macos}` plus
`use std.nogc_sync_mut.io_runtime.{...}`): the candidate fix does NOT
redirect the call.** `SIMPLE_DEBUG_DUPDISPATCH=1` trace on the same rebuilt
seed:

```
[dupdispatch] probe name=host_os current=<entry> entry=Some((".../src/lib/platform.spl", "host_os"))
[dupdispatch] HOP-TRY owner=.../src/lib/platform.spl name=host_os has_name=true has_star=true
[dupdispatch] HOP-RESULT owner=.../src/lib/platform.spl name=host_os hop=Some((".../src/lib/nogc_sync_mut/io/__init__.spl", "host_os"))
[dupdispatch] HOP-TRY owner=.../nogc_sync_mut/io/__init__.spl name=host_os has_name=false has_star=false
[dupdispatch] HOP-RESULT ... hop=None
[dupdispatch] P4-overload name=host_os owner=Some(".../nogc_sync_mut/io_runtime.spl") current=Some("<entry>")
```

`src/lib/platform.spl`'s recorded `"*"` glob edge does not point at
`nogc_sync_mut/platform.spl` (the module that actually declares `host_os`,
confirmed by direct read of that file) — it points at
`nogc_sync_mut/io/__init__.spl`, an unrelated module that has no `host_os`
binding at all, so the hop dead-ends and `import_bound_candidate` returns
`None`. Dispatch falls through to the historical tie-break, which lands on
`nogc_sync_mut/io_runtime.spl`'s `host_os` — the exact wrong-module dispatch
this bug describes. The symptom is invisible today only because
`c4d6d497edf` independently hardened `io_runtime`'s copy to also return
`"windows"` on Windows; the dispatch is still wrong, it just no longer
produces an empty string.

**Root cause of the corrupted `"*"` edge is not fully diagnosed** — it is a
second, distinct defect in how `record_flattened_import_binding`
(`interpreter_eval.rs`) resolves the glob target for `src/lib/platform.spl`.
`nogc_sync_mut/platform.spl` is not a bare leaf module (it itself does
`use std.io_runtime.{env_get}` / `{process_run}` / `{file_exists}`, and
`nogc_sync_mut` also has an unrelated `platform/` **package directory** with
its own `__init__.spl` alongside the `platform.spl` **file** — a naming
collision that is itself worth checking as a candidate cause of the module
identity getting swapped for `nogc_sync_mut/io/__init__.spl`). Whatever the
mechanism, the fixture proves it: a single-hop facade (`zzdd_a.spl` ->
`zzdd_impl_a.spl`, no further imports inside the target) resolves correctly;
a facade whose target module itself has further imports and/or a sibling
package-directory of the same base name (`platform.spl` vs `platform/`)
does not.

**Verdict: candidate fix `b0229d663b1` is INSUFFICIENT, not wrong.** It is
directionally correct and provably fixes the simple case with no observed
regression risk (still additive, non-invasive fallback only when no better
candidate exists), but it does **not** fix the motivating real-world case
(`host_os`/`host_arch`) because the `"*"` glob-edge table it depends on is
itself corrupted for at least one real module shape. Recommendation: **do
not push `b0229d663b1` as a claimed fix for this bug.** It may still be worth
landing on its own merits (it is a real, verified improvement for the simple
facade shape and is additive/non-regressing), but the commit message and this
doc must stop implying it resolves the `host_os` symptom, and a follow-up
must chase the `"*"`-edge corruption before this bug can be closed. No
broader regression suite was run against `b0229d663b1` beyond the two
fixtures above and a clean `cargo check`/`cargo build --release --bin
simple`; that remains open work.

**Unix/macOS impact:** identical code path — `import_bound_candidate` and
`record_flattened_import_binding` are platform-independent. The `"*"`-edge
corruption reproduced here is a module-resolution/binding-table defect, not
a Windows-specific one; it would misdispatch the same way on Linux/macOS for
any facade with the same shape (multi-import target module and/or a
file/directory basename collision). The only Windows-specific part of the
original report is that the SYMPTOM (empty string) is masked on Unix,
because `io_runtime`'s uname-based `host_os`/`host_arch` return real values
there even when wrongly selected — the wrong function still runs, it just
happens to give a plausible-looking answer.
