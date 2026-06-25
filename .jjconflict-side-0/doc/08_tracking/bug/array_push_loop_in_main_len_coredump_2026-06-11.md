# BUG: array push loop inside fn main + len() dumps core (native AND interpreter)

Status: FIXED (verified 2026-06-11)

**Date:** 2026-06-11
**Status:** FIXED — no longer reproduces in interpreter (`bin/simple run` → 100)
nor native (`bin/simple compile --native` → 100, exit 0); resolved by the
x=x.push() store-miscompile family (0bf222e322) + stage4 chain fixes
(2eae3b46c8). Pinned by regression spec
`test/01_unit/compiler/interpreter/array_push_loop_local_len_spec.spl` (3/3).
**Severity:** High (memory-safety crash, both execution modes)
**Found by:** memory_audit_gc_nogc nogc verification (.spipe/memory_audit_gc_nogc/research_nogc_verify.md §7 B1)

## Problem

An array-push loop placed *inside* `fn main` followed by `print(arr.len())` dumps core:
native mode exits 139 (SIGSEGV) and interpreter mode also crashes. The identical code at
module level works fine.

```simple
fn main():
    var arr: [i64] = []
    for i in 0..100:
        arr = arr.push(i)
    print(arr.len())   # core dump here (native exit 139 + interpreter crash)
```

Repro pair used during verification: `/tmp/nogc_verify/b1.spl` (crashes) vs `v1.spl`
(module-level variant, works).

## Notes

- Likely related to the x=x.push() store miscompile family fixed in 0bf222e322
  (rt_array_push dest:None) — but this variant still crashes after that fix, and it
  crashes in the *interpreter* too, so at least part of the defect is shared logic or
  a second site.
- Security relevance: SIGSEGV on safe-looking code is a memory-safety violation.

## Next step

Minimize repro, bisect interpreter crash separately from native crash; check
fn-local array variable slot allocation vs module-level global path.
