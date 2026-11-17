# #9247's origin check false-positives on the stage2 sanity SCV snapshot: "source declaration origin mismatches the symbol owner" poisons compiler.bootstrap_admission.p2_add (2026-11-17)

**Status:** OPEN (metadata lane follow-up: #9247's declaration-origin check is
over-strict for the sanity SCV snapshot, or the snapshot genuinely violates
the new invariant)
**Area:** stage2 candidate HIR lowering, declaration-origin tracking (#9247)
**Evidence:** cycle-34 stage2 admission at 99f13e138e5 (FreeBytes accessor
#9905 + #9247 metadata fill): the strict stage2 native build now COMPILES and
LINKS clean (1574 modules, 0 failed — the metadata fill and the accessor fix
both work). The post-build SANITY build then fails under the new candidate:

```
[first-compile-error] HIR lowering error in
  .../scv-revision-v2-8101626ba5.../src/compiler/bootstrap_admission/p2_add.spl:
  source declaration origin mismatches the symbol owner
[collect-all] 1 module(s) poisoned, 5 error(s) collected across 1 source(s)
  in phase 3 (HIR lowering).
  poisoned: compiler.bootstrap_admission.p2_add
```

## Reading

#9247 added declaration-origin tracking strict enough to reject
compiler.bootstrap_admission.p2_add inside the sanity SCV snapshot. Either
(a) the SCV snapshot rewrites declaration origins (so the check false-
positives on snapshotted sources), or (b) p2_add.spl genuinely declares a
symbol whose origin differs from its owner and the pre-#9247 compilers
tolerated it. Cycle-33 (a27ee8ab0c9, also carrying #9247) compiled the full
compiler closure cleanly but never reached sanity (it died at the link), so
this is the first sanity run of a #9247 candidate.

## Impact

- Stage2 admissions at #9247+ tips fail at sanity, so the mcp test and the
  phase-3 full run remain gated one more layer down.
- The metadata fill itself is confirmed working (0 compile failures where
  the c32 candidate reported 248 metadata errors).

## Owner asks

1. Confirm whether the sanity SCV snapshot preserves declaration origins; if
   not, scope the origin check to non-snapshot builds or fix the snapshot.
2. If p2_add.spl genuinely mismatches, repair its declaration origin.


## 2026-11-17 addendum: check-level analysis — the trigger condition and why p2_add is innocent

The check lives at src/compiler/20.hir/hir_symbol_table_methods.spl:90
(`SymbolTable.bind_declaration_origin_v1`, added with #9247). It errors when
a declaration origin is bound onto a symbol whose canonicalized
`defining_module` differs from the origin's canonical owner:

```
if _hir_symbol_owner_module(symbol.defining_module ?? "") != canonical_owner:
    return Err("source declaration origin mismatches the symbol owner")
```

p2_add.spl itself is a 23-line redeploy-gate fixture (five tag fns + main,
no imports, no re-exports) — there is nothing in its source that can
"mismatch". The failure is therefore structural to the sanity SCV snapshot:
the snapshot build registers declaration origins with the LOGICAL owner
(`compiler.bootstrap_admission.p2_add`) while the snapshot's own symbol
registration leaves `defining_module` set to the snapshot-materialized
module identity. The pre-#9247 compilers had no origin check, so the sanity
path never noticed.

Owner fix directions (either is sufficient):
1. In the sanity SCV snapshot loader (#9247's
   module_import_registration / module_reexport_materialization path), bind
   declaration origins with owner = the symbol's canonical defining_module
   as registered in the snapshot, not the logical source module; OR
2. Scope `bind_declaration_origin_v1`'s owner check to symbols whose
   defining_module is not snapshot-materialized (add a snapshot-origin
   predicate), keeping the check strict for real module builds.

Until one lands, stage2 admissions at #9247+ tips fail at sanity
(simple.exe.rejected), gating the mcp test and the phase-3 run. The c34
binary otherwise compiled and linked 1574/1574 clean.
