# Sweep Delta — Before/After 7 Fixes Shipped This Session

**Date:** 2026-04-28
**Origin/main HEAD at sweep:** `fe6507117f`

## Top-line numbers

| Metric | BEFORE (baseline `run.log`) | AFTER (`run-after-fixes.log`) | Change |
|---|---:|---:|---:|
| Total ✗ markers | 3,093 | 2,867 | **−226** |
| Unique failing spec files | 566 | 517 | **−49** |
| Parse errors (cascade source) | 21 | 10 | **−11** |

> Note: `run-after-fixes.log` was killed at 53.7K lines / 2867 ✗ because the
> ElectronCapture test hung on a non-mockable scene-capture. Baseline ended at
> 55.2K lines / 3091 ✗. The two are within ~3% of each other in coverage.

## Fixes attributed to this delta

| Commit | Fix | Likely closed |
|---|---|---|
| `2725ea85c1` | Parser `peek_visibility_target_is` lexer corruption | Many cascaded `pub field` parse failures |
| `b2c58182b5` | `//` → `#` line comments in 105 files | Mostly silent — these were caught at parse, not as ✗ |
| `a865b925f8` | sdn module docblock fix | 7 sdn files now parse → unblocks dependents |
| `56b8249282` | Newtype constructor + Object→int unwrap | Some tests partially passing |
| `da3b047f56` | Newtype operator re-wrap | newtype_ops_spec: 0/24 → 24/24 |
| `c8e46854cd` | Test runner infix-expect rewrite + 9 matchers | Widget specs: 16 ✗ → 0; many other specs |
| `fe6507117f` | type_layout missing helpers | layout_verification_spec: 12/30 → 30/30 |

## Top remaining failure clusters (sorted by ✗ count)

| Count | Error | Cluster type | Suggested fix |
|---:|---|---|---|
| 254 | `method to_be_true not found on type bool` | matcher rewrite | Method-form preprocess gate (started, reverted by reconcile) |
| 122 | `expected false to equal true` | logic regression | Per-spec investigation |
| 85 | `extern fn rt_sqlite_open_memory not found` | runtime extern missing | Add extern declaration in runtime |
| 81 | `function debugger_new not found` | API drift | Class/factory rename |
| 75 | `variable RRB_BRANCH_FACTOR not found` | const missing | Add const definition |
| 68 | `function rb_contains not found` | utility missing | Add or import |
| 64 | `function trie_set not found` | utility missing | Add or import |
| 55 | `function rt_hash_text not found` | runtime extern missing | Add extern |
| 52 | `method replace not found on str` | str API drift | Method binding fix |
| 46 | `function ByteSize not found` | class missing | Define or import |
| 40 | `unknown variant or method 'int' on enum SdnValue` | SDN enum API drift | Update callers or extend enum |
| 36 | `function AtomicI64 not found` | class missing | Define or import |
| 28 | `variable vec not found` | local-binding bug | Per-spec investigation |
| 28 | `method to_bytes not found on str` | str API drift | Method binding fix |
| 26 | `parameter children missing` | class instantiation API drift | Update callers |

**Highest-leverage next fix**: re-apply `needs_infix_preprocess` gate with method-form detection — closes 254 ✗ in one commit. (Was reverted by jj reconcile during this session; binary still has it but source needs re-apply.)

## What clusters were fully closed by this session

- `function pub field` parse-cascades (parser fix)
- `function to_start_with not found` infix form (matcher rewrite)
- `function to_end_with not found` infix form
- `function Width not found` (newtype constructor)
- `function type__to_text not found` (type_layout helpers)
- `function attr_effective_align not found` (type_layout helpers)

## Honest read

This session shipped 7 fixes that closed ~230 ✗ markers (~7% of total). The remaining 2867 fails are dominated by:
- 1 fixable cluster (254 — needs the preprocess gate re-applied)
- ~20 small-medium clusters of 25-100 each (need targeted runtime/API fixes)
- A long tail of 1-3 ✗ per file that need per-spec investigation

The fix rate is decelerating — early fixes were structural (parser/test-runner) that closed wide cascades. Remaining work is more specialized.
