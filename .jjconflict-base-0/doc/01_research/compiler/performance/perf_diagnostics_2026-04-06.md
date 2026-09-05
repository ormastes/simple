# Performance Diagnostics — Compiler, Interpreter & Loader

**Date:** 2026-04-06
**Scope:** Full audit of performance bottlenecks and optimization state
**Status:** Complete — implementations applied

---

## Executive Summary

Audited the Simple compiler pipeline for performance issues. Many previously-documented issues in stale docs were **already fixed** in code. Applied 7 targeted fixes across data structures, interpreter, and MIR optimizer.

## Changes Applied

| Change | File(s) | Impact |
|--------|---------|--------|
| PersistentDict: hash-bucketed structural sharing | `src/lib/common/collections/persistent_dict.spl` | ~32x faster get/set/remove |
| PersistentVec: chunked tail optimization | `src/lib/common/collections/persistent_vec.spl` | O(1) push/pop vs O(n) |
| Map: hash-first comparison + negative index fix | `src/lib/nogc_sync_mut/src/map.spl` | Skips expensive key cmp when hashes differ |
| Interpreter hash: FNV-1a replaces 3-char polynomial | `src/compiler/10.frontend/core/interpreter/hashmap.spl` | Better distribution, fewer collisions |
| String interning pool (infrastructure) | `src/compiler/10.frontend/core/interpreter/intern.spl` | Ready for LOAD_FAST integration |
| TCO MIR pass | `src/compiler/60.mir_opt/mir_opt/tco.spl` | Recursive to loop, prevents stack overflow |
| GVN MIR pass | `src/compiler/60.mir_opt/mir_opt/gvn.spl` | Cross-block redundancy elimination |

## Already Done (stale docs said broken)

- Hash trait: `src/lib/nogc_sync_mut/src/hash.spl` (308 lines, FNV-1a/MurmurHash3)
- Map.hash_key: calls `key.hash()` correctly
- Interpreter scope hash maps, value caching (nil/true/false/0-255)
- MIR passes: inlining (721 lines), LICM (183 lines), CSE (372 lines)
- SMF mmap cache, lazy section loading, deferred module tracking

## Remaining Work (deferred)

| Item | Reason | Impact |
|------|--------|--------|
| LOAD_FAST index-based locals | Pervasive parser+env changes | 10-50x interpreter |
| Full string interning integration | Requires parser rewiring | 5-10x identifier cmp |
| Escape analysis to stack alloc | Codegen integration across backends | Variable |
| Cross-session bytecode cache | Disk persistence infra needed | 2-5x recompile |

## Test Results

All 62 tests pass: PersistentDict 15/15, PersistentVec 36/36, Map 11/11.
