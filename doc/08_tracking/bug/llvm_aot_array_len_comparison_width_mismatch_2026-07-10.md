# LLVM AOT Width Lookup and Array-Index Pointer Blocker

- **Date:** 2026-07-10
- **Status:** RESOLVED. width mismatch fixed (d984ee9); array-index pointer
  half SUBSUMED by 7dc19b547ab (#138) + 67650325 — see Resolution below.
- **Area:** LLVM AOT lowering

## Summary

A tiny native `[u32]` probe exposed two width-loss paths in textual LLVM
lowering. Explicit MIR constants could inherit a stale local width, and
expression-style type lookups could return `nil` under bootstrap lowering.
The latter made declared `u32` comparison operands fall back to `i64`.

## Reproduction

The bounded CPU-SIMD span probe used:

```simple
if pixels.len() != (16 as i64): return 1
```

Before the fix, `native-build` failed in `llc-18` with:

```text
'%l20' defined with type 'i32' but expected 'i64'
%l21 = icmp ne i64 %l18, %l20
```

The fix makes explicit instruction types authoritative for constants and uses
explicit returns for local and operand type lookup. The focused MIR regression
now emits `icmp ne i32` for two declared `u32` operands and passes 3/3.

The final bounded AOT run no longer reports a width mismatch. It advances to a
separate array-index lowering failure:

```text
error: use of undefined value '%l15'
%0 = inttoptr i64 %l15 to ptr
```

The same span bridge passes interpreter tests. C runtime objects compile for
x86_64, AArch64, generic RISC-V, and RVV RISC-V. The three-cycle AOT retry cap
was reached, so the undefined array-index pointer is retained as the remaining
native probe blocker rather than retried in this session.

## Resolution (2026-07-11)

The `inttoptr i64 %lN to ptr` referencing an undefined `%lN` was the array-index
data-pointer compute for a `[u32]` local (`fill`) that is defined once (the
returned array) and then read across the `or` short-circuit blocks of
`rt_array_len(fill) != 8 or ...`. Two independently-landed root-cause fixes
close it:

- **7dc19b547ab (#138)** — array index-reads are routed through `rt_array_get`
  via the `runtime_array_locals` set instead of a raw `getelementptr`/`inttoptr`
  data-pointer compute, so the dangling `inttoptr i64 %lN to ptr` shape is no
  longer emitted for index reads.
- **67650325** — the alloca-per-slotted-local transform
  (`ssa_alloca_transform_blocks`, `var_reassign_ssa.spl`) slots cross-block-live
  single-def locals (union of multi-def and cross-block-live). The single-def
  array local `fill` escapes into later blocks, so its use is no longer
  un-dominated: the def becomes an entry-block Store and every cross-block use
  becomes a Load, eliminating the undefined `%lN` use. (The `main` case is
  multi-block, so it was already slotted by the pre-67650325 multi-block path;
  67650325 additionally covers the single-block straight-line variant.)

Evidence:
- The stale deployed emitter's generated `.ll` for the probe already
  alloca-slots the cross-block array local (`%lNN = alloca` + Store + per-use
  Load) with **no `inttoptr` and no undefined use** — the only remaining llc
  error there is the width mismatch, which d984ee9 fixes.
- MIR-level regression: `runtime_array_assignment_ssa_spec.spl` gains a fifth
  arm, "slots a cross-block-live single-def array pointer (array-index inttoptr
  shape)", asserting `applied==true` and zero residual writes of the array
  local. Run against worktree source: **6/6**. Companion suites green:
  `var_reassign_analysis` 18/0, `bootstrap_llvm_entry_symbol_source_spec` 4/0.

## Separate Signedness Hazard

This width fix does not change ordered integer predicates. LLVM lowering still
uses signed `slt`/`sle`/`sgt`/`sge` predicates after erasing `u32` signedness to
`i32`, and `i32` widening still selects `sext`. That existing semantic gap needs
signedness-preserving MIR metadata and a dedicated regression; it is not part
of the equality/inequality width fix above.

## Expected

Array-index pointer locals must be defined before the generated `inttoptr`.
This is now satisfied (see Resolution): index reads no longer emit a raw
`inttoptr` pointer compute (#138), and cross-block-live array locals are
alloca-slotted so their uses are Loads dominated by an entry-block Store
(67650325). The comparison semantics are unchanged.

Note on empirical scope: like 67650325, MIR/spec-level proof against worktree
source is authoritative here; a full `native-build` llc+run of the probe
requires a compiler binary rebuilt from worktree source (the deployed binary
still carries the pre-fix emitter). Rebuilding that binary in this environment
was not completed in-session, so the end-to-end llc+execute confirmation of the
probe is deferred to the next bootstrap deploy — identical to the precedent set
by 67650325 ("proven at MIR level; full llc e2e deferred").
